# QCP Strategy 与 `do` 指令使用指南

本文说明如何在 QCP 验证中加载 strategy，并在 C 程序的指定位置用

```c
/*@ do scope_name */
```

显式执行一组 strategy。重点场景是：当前断言中有一个 separation logic predicate，希望从中展开或导出若干 pure 性质，供后续符号执行、内存访问或断言使用。

## 1. Strategy、scope 与 `do` 的关系

一个 `.strategies` 文件包含若干条规则。每条规则的 `priority` 字段同时指定：

- 规则所属的 scope；
- 规则在该 scope 内的优先级层级。

例如：

```text
id : 1
priority : expose_u256(0)
left : store_u256(?p, ?x) at 0
action : ...
```

这条规则属于 `expose_u256` scope。C 文件中的：

```c
/*@ do expose_u256 */
```

会在该程序点，用当前符号状态执行 `expose_u256` scope 中能够匹配的 strategy。

可以把三者理解为：

```text
.strategies 中定义规则
        ↓ priority : expose_u256(...)
规则被放进 expose_u256 scope
        ↓ /*@ do expose_u256 */
在当前 C 程序点显式执行该 scope
```

`do` 是 QCP 标注，不是 C 运行时语句，不会改变编译后程序的行为。它只影响验证时的符号状态。

## 2. 最小语法

### 2.1 加载 strategy 文件

通常在 C 文件包含的定义头文件中写：

```c
/*@ include strategies "sm2_u256.strategies" */
```

例如：

```c
/* sm2_u256_strategy_def.h */

/*@ Extern Coq
      (U64_MOD : Z)
      (U256_MOD : Z)
      (u256_of_limbs : Z -> Z -> Z -> Z -> Z)
      (store_u256 : Z -> Z -> Assertion)
 */

/*@ include strategies "sm2_u256.strategies" */
```

C 文件再包含这个头文件：

```c
#include "sm2_u256_strategy_def.h"
```

### 2.2 在程序点执行 scope

```c
/*@ do expose_u256 */
```

注意：

- `do` 后写的是 scope 名，不是 rule 的 `id`。
- scope 名应与 `.strategies` 中 `priority : scope_name(...)` 的名字完全一致。
- 该 strategy 文件必须已经通过 `include strategies` 加载。
- `do` 应放在函数体内、需要转换当前断言的程序点。

## 3. Strategy 规则的基本结构

一条常见规则由以下部分组成：

```text
id : 1
priority : expose_u256(0)
left : store_u256(?p, ?x) at 0
check : ...
action : ...
```

各字段作用如下。

### `id`

当前 strategy 文件内的规则编号，用于区分规则和生成证明产物。

### `priority`

```text
priority : scope_name(level)
```

- `scope_name`：规则组名称，也是 `do` 使用的名称。
- `level`：scope 内的优先级层级。

### `left` 与 `right`

匹配当前 entailment 两侧的断言。

```text
left : store_u256(?p, ?x) at 0
right : store(?addr, U64, ?value) at 1
```

`?p`、`?x` 等是匹配变量。`at 0`、`at 1` 是后续 action 引用的匹配位置编号。

只需要改写当前前提时，可以仅写 `left`。

### `check`

规则应用前必须满足的额外条件。例如：

```text
check : infer(0 <= i);
        infer(i < 4);
```

如果条件无法由当前状态推出，规则不会应用。

### `action`

描述匹配成功后如何变换断言。常见动作包括：

```text
left_erase(0);
left_exist_add(x0);
left_add(0 <= x0);
left_add(store(...));
right_add(...);
```

其中：

- `left_erase(0)`：删除编号为 0 的左侧匹配断言；
- `left_exist_add(x0)`：引入新的存在量；
- `left_add(P)`：向左侧加入命题或空间断言；
- `right_add(P)`：向右侧加入命题或空间断言。

## 4. 从 separation logic predicate 导出 pure 性质

假设公开规格用一个整体谓词描述 256 位整数：

```c
store_u256(input, X)
```

希望在某个程序点得到四个 limb 的范围以及整体值与 limb 的关系：

```text
0 <= x0 < U64_MOD
...
X == u256_of_limbs(x0, x1, x2, x3)
```

可以定义一个显式展开 scope：

```text
#include "sm2_u256_strategy_def.h"

id : 1
priority : expose_u256(0)
left : store_u256(?p, ?x) at 0
action : left_erase(0);
         left_exist_add(x0);
         left_exist_add(x1);
         left_exist_add(x2);
         left_exist_add(x3);
         left_add(0 <= x0);
         left_add(x0 < U64_MOD());
         left_add(0 <= x1);
         left_add(x1 < U64_MOD());
         left_add(0 <= x2);
         left_add(x2 < U64_MOD());
         left_add(0 <= x3);
         left_add(x3 < U64_MOD());
         left_add(x == u256_of_limbs(x0, x1, x2, x3));
         left_add(UInt64Array::full(
           field_addr(p, u32, v),
           4,
           cons{Z}(x0,
             cons{Z}(x1,
               cons{Z}(x2,
                 cons{Z}(x3, nil{Z}))))));
```

然后在 C 中调用：

```c
u1 u32_shl(u32 *input)
/*@ With (X : Z)
    Require
      store_u256(input, X)
    Ensure
      ...
 */
{
  /*@ do expose_u256 */

  u1 carry = input->v[3] >> 63;
  ...
}
```

执行 `do` 后，后续符号执行可使用：

- 新引入的 `x0`、`x1`、`x2`、`x3`；
- limb 的上下界；
- `X == u256_of_limbs(...)`；
- 展开后的数组内存所有权。

这正是“从 separation logic predicate 导出 pure 性质”的典型做法。

## 5. 只导出 pure 性质，还是同时展开内存？

设计 strategy 时必须先明确需要哪一种行为。

### 情况 A：后续需要访问结构体字段或数组元素

需要把整体谓词展开成底层空间断言，例如：

```text
UInt64Array::full(...)
```

或四个标量 `store(...)`。否则符号执行器仍可能找不到内存读取所需的所有权。

### 情况 B：只需要一个数学事实

如果 strategy 的逻辑基础允许保留原谓词，可以添加 pure 命题而不删除空间谓词。这样后续仍保有抽象表示。

但是，不能无依据地从 `store_u256(p, X)` 添加任意 pure 命题。每条 strategy 都会产生对应的正确性义务，必须在生成的 strategy proof 中证明。

### `left_erase` 的影响

下面的 action：

```text
left_erase(0);
```

会消费匹配到的抽象谓词。如果随后只加入展开后的数组或标量 store，那么当前状态中不再保留原来的 `store_u256`。

这通常适合函数入口处的“打开谓词”，但函数返回前往往还需要：

- 一条放在 `post` scope 中的反向 fold strategy；或
- 一个明确的 Assert/Ensure entailment；

把底层内存重新组合成公开后条件要求的抽象谓词。

## 6. 非消耗式 pure 投影：证明时展开并立即折回

如果目的只是从 separation logic predicate 导出 pure 性质，最合适的方法通常不是先 `left_erase` 再用 `post` 重建，而是：

```text
left : predicate(...) at 0
check : absense(pure_fact)
action : left_add(pure_fact);
```

这种规则有两个关键点：

1. action 中没有 `left_erase(0)`；
2. 只通过 `left_add` 加入 pure 性质。

因此执行前后分别是：

```text
执行前：predicate(args)
执行后：pure_fact && predicate(args)
```

原 separation logic predicate 没有被消费，不需要后续 fold。在 strategy correctness 的 Rocq 证明中，可以展开 predicate 证明 `pure_fact`，随后原 predicate 仍作为空间资源保留；从使用者视角看，就是“展开后立即折叠回去，只把 pure 性质导出来”。

### QCP 现有例子：从数组谓词导出长度非负

`QCP_examples/QCP_demos_LLM/char_array.strategies` 中有：

```text
id : 6
priority : core(1)
left : CharArray::full(?p, ?n, ?l1) at 0
check : absense(0 <= n);
action : left_add(0 <= n);
```

规则应用后：

- `CharArray::full(p, n, l1)` 仍然存在；
- 当前状态额外得到 `0 <= n`；
- `absense(0 <= n)` 防止同一规则反复添加相同事实。

### QCP 现有例子：配合 `do local`

`QCP_examples/QCP_demos_LLM/common.strategies` 中有：

```text
id : 21
priority : local(0)
left : store(?p : Z, U32, ?x : Z) at 0
check : absense(x >= 0);
action : left_add(x >= 0);

id : 22
priority : local(0)
left : store(?p : Z, U32, ?x : Z) at 0
check : absense(x <= UINT_MAX());
action : left_add(x <= UINT_MAX());
```

在 C 的目标程序点执行：

```c
/*@ do local */
```

即可从 `store(p, unsigned int, x)` 导出：

```text
0 <= x
x <= UINT_MAX
```

同时原来的 `store` 保持不变。这正是 `do scope_name` 用于“从空间谓词直接导出 pure 性质”的标准范式。

### SM2 推荐写法

假设 `store_u256(p, X)` 的定义能够证明 `X` 位于 256 位无符号范围，可以写：

```text
#include "sm2_u256_strategy_def.h"

id : 1
priority : u256_pure(0)
left : store_u256(?p, ?x) at 0
check : absense(0 <= x);
action : left_add(0 <= x);

id : 2
priority : u256_pure(0)
left : store_u256(?p, ?x) at 0
check : absense(x < U256_MOD());
action : left_add(x < U256_MOD());
```

在 C 中按需调用：

```c
/*@ do u256_pure */
```

调用后的预期状态是：

```text
0 <= X &&
X < U256_MOD &&
store_u256(input, X)
```

这比完全展开成四个 limbs 更适合只需要范围、非负性或其他 pure 语义性质的场景。

### 使用限制

- `left_add(P)` 必须在逻辑上能由原 predicate 推出；否则 strategy correctness proof 无法完成。
- pure 投影规则不能提供字段读取所需的底层内存所有权。需要访问 `input->v[i]` 时，仍需另行展开数组或标量 store。
- 必须使用 `absense(P)` 或其他终止条件，避免反复添加同一事实。
- 如果一条 pure 性质依赖存在量，可以用 `left_exist_add` 引入见证，但不要因此错误复制空间资源。

## 7. 用 `post` scope 自动折叠

QCP 已有一种不需要手写 `/*@ do fold_scope */` 的自动折叠方式：把回收规则放入内置的 `post` scope。

教程中的：

- `swap_simple2.strategies`
- `swap_simple3.strategies`

展示了两者的差别。两个 C 文件的函数体完全相同，也都没有写 `do`。`swap_simple3.strategies` 比 `swap_simple2.strategies` 多出下面的规则：

```text
id : 4
priority : post(1)
left : store(field_addr(?p, int_pair, a), I32, ?x) at 0
       store(field_addr(p, int_pair, b), I32, ?y) at 1
action : left_erase(0);
         left_erase(1);
         left_add(store_int_pair(p, x, y));
```

当符号状态中重新同时出现两个字段的 store 时，这条 `post` 规则会把它们自动收回为：

```text
store_int_pair(p, x, y)
```

因此：

- `core` 规则负责在符号执行需要字段所有权时打开抽象谓词；
- `post` 规则负责在操作后自动整理、回收或折叠空间断言；
- C 中不需要写 `/*@ do post */`。

### SM2 数组中的同一模式

当前 `array_bridges.strategies` 与 QCP 数组 strategy 使用：

```text
UInt64Array::full(base, n, l)
```

访问单个元素时，`core` 规则把它拆成：

```text
UInt64Array::missing_i(base, i, 0, n, l)
store(base + i * sizeof(U64), U64, l[i])
```

未修改元素时，下面的 `post` 规则恢复原数组：

```text
id : 3
priority : post(1)
left : UInt64Array::missing_i(?base, ?i, 0, ?n, ?l) at 0
       store(base + i * sizeof(U64), U64, l[i]) at 1
check : infer(0 <= i);
        infer(i < n);
action : left_erase(1);
         left_erase(0);
         left_add(UInt64Array::full(base, n, l));
```

元素已更新时，另一条 `post` 规则用 `replace_Znth` 恢复更新后的数组：

```text
id : 4
priority : post(3)
left : UInt64Array::missing_i(?base, ?i, 0, ?n, ?l) at 0
       store(base + i * sizeof(U64), U64, ?v) at 1
check : infer(0 <= i);
        infer(i < n);
action : left_erase(1);
         left_erase(0);
         left_add(UInt64Array::full(
           base, n, replace_Znth{Z}(i, v, l)));
```

这就是“展开后自动折叠回去”的标准做法。

### `post` 自动折叠的边界

`post` 只会执行能够匹配当前状态的规则，不是自动展开 Rocq 定义。因此仍需保证：

- 展开规则留下了足够的 frame，例如 `missing_i`；
- 写回后的 `store` 地址、类型和下标与 fold 规则一致；
- 修改元素时，fold 规则正确更新抽象值；
- 如果还要从 `UInt64Array::full` 折叠回更外层的 `store_u256`，需要再提供一条对应的 `post` 规则；
- unfold 与 fold 不应放在同一个会互相反复触发的自动阶段。

## 8. 推荐的 scope 划分

不要把所有规则都塞进一个会到处自动触发的 scope。可以按用途命名：

```text
expose_u256
derive_u256_range
```

例如：

```c
/*@ do expose_u256 */
/* 访问和更新 limbs */
...
```

回收规则则优先放在：

```text
priority : post(...)
```

优点是：

- 调用位置清晰；
- 不会在无关程序点意外展开谓词；
- 更容易定位不收敛或错误匹配；
- strategy proof 的用途更容易审查。

`core`、`post` 是 QCP 现有示例用于自动处理的 scope。需要用户精确控制执行时机的派生或展开规则，可以使用表达用途的自定义 scope，并由 `do` 显式调用；结构性回收规则通常放入 `post`。

## 9. 完整小例子

### 定义头文件

```c
/* pair_strategy_def.h */

struct int_pair {
  int a;
  int b;
};

/*@ Extern Coq
      (store_int_pair : Z -> Z -> Z -> Assertion)
 */

/*@ include strategies "pair.strategies" */
```

### Strategy 文件

```text
#include "pair_strategy_def.h"

id : 1
priority : expose_pair(0)
left : store_int_pair(?p, ?x, ?y) at 0
action : left_erase(0);
         left_add(store(field_addr(p, int_pair, a), I32, x));
         left_add(store(field_addr(p, int_pair, b), I32, y));

id : 2
priority : post(1)
left : store(field_addr(?p, int_pair, a), I32, ?x) at 0
       store(field_addr(p, int_pair, b), I32, ?y) at 1
action : left_erase(0);
         left_erase(1);
         left_add(store_int_pair(p, x, y));
```

### C 文件

```c
#include "pair_strategy_def.h"

int read_first(struct int_pair *p)
/*@ With x y
    Require
      store_int_pair(p, x, y)
    Ensure
      __return == x &&
      store_int_pair(p, x, y)
 */
{
  /*@ do expose_pair */
  return p->a;
}
```

`expose_pair` 删除 `store_int_pair` 并产生两个字段 store；`post` 规则随后可以自动把两个字段重新组合为 `store_int_pair`，满足公开后条件。

## 10. 常见错误

### 找不到 scope

检查：

1. `.strategies` 是否通过 `include strategies` 加载；
2. include 路径是否正确；
3. `do` 后的名称是否与 `priority : scope_name(...)` 完全一致；
4. 运行 QCP 时是否提供了正确的 strategy 搜索路径。

### `do` 执行后没有变化

通常表示 scope 存在，但没有规则匹配当前断言。检查：

- predicate 名称和参数是否一致；
- 类型名是否使用 QCP 的规范形式；
- `left`/`right` 是否要求了当前不存在的匹配项；
- `check : infer(...)` 是否能够成功；
- 规则是否在错误的 scope 中。

### 内存读取仍然失败

只添加 pure 性质不等于提供内存所有权。后续若执行 `p->field` 或 `a[i]`，strategy 还必须产生相应的 `store`、`undef_data_at` 或数组谓词。

### 后条件无法证明

检查是否通过 `left_erase` 展开并消费了公开谓词，却没有提供可匹配的 `post` fold 规则。

### Strategy 不收敛

典型原因是 unfold 和 fold 规则在同一个自动 scope 中互相触发。应：

- 把两类规则放入不同 scope；
- 在不同程序点分别用 `do` 调用；
- 避免 action 重新生成同一条规则的输入形状。

### Strategy 正确性证明失败

strategy 不是无条件可信的文本替换。若 action 加入的 pure 命题或空间断言不能由匹配前提推出，对应的 Rocq strategy obligation 就无法证明。此时应修正规则或补充真正需要的数学引理，不能通过弱化公开规格规避。

## 11. 建议的工作流程

1. 先写清楚 predicate 的 Rocq 定义和希望导出的事实。
2. 为单一用途建立一个命名清楚的 scope。
3. 先只写一条最小规则。
4. 在需要转换状态的精确程序点加入 `/*@ do scope_name */`。
5. 运行 QCP，确认 scope 被找到且规则实际匹配。
6. 检查生成的普通 VC 和 strategy correctness obligations。
7. 完成对应的 strategy proof。
8. 检查展开后是否需要 `post` fold，并分别覆盖“未修改”和“已更新”状态。
9. 最后再增加其他规则，避免一次引入多个可能冲突的改写。

## 12. 本项目可参考的 QCP 文件

QCP 当前教程和示例中，与本指南关系最密切的文件包括：

- `tutorial/T4-2 在规约或断言中使用新定义的分离逻辑谓词.md`
- `tutorial/T2-2 断言常见形式和分离合取的常用性质.md`
- `QCP_examples/QCP_demos_tutorial/swap_simple2.strategies`
- `QCP_examples/QCP_demos_tutorial/swap_simple3.strategies`
- `QCP_examples/QCP_demos_LLM/common.strategies`
- `QCP_examples/QCP_demos_LLM/char_array.strategies`
- `QCP_examples/LLM_bench/Crypto/sm2_u32_shl/sm2_u256.strategies`
- `QCP_examples/LLM_bench/Crypto/sm2_u32_shl/sm2_u32_shl.c`
- `Rocq/examples/LLM_bench/Crypto/sm2_u32_shl/sm2_u256_strategy_proof.v`

其中 tutorial 展示了抽象 predicate 与底层字段谓词之间的关系，SM2 strategy 示例展示了如何把整体 `u256` 表示展开为有界 limbs 和数组/标量内存断言。
