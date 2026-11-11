# 验证代码与 YCrypt 源码的差异

参考源码为 YCrypt 的 `sm2/` 目录和 `sm3/sm3.c`，验证代码位于
`QCP_examples/Applications_human/sm2/`。本文只记录当前验证代码的可执行 C 差异；
annotation 属于逻辑证明输入，不计为 C 实现差异。除下文列出的项目外，验证函数
保持参考实现的类型、初始化、控制流、访存顺序和返回值。

`solinas_reduce` 的局部变量 `u32 payload`
初始化器最后一个成员省略了参考源码中的 trailing comma。当前预编译前端能够
符号执行此前的语句，但保留该逗号时会在随后的 `}` 处报语法错误。仅移除这个
逗号不改变任何字段初值、控制流或内存结果。

## 1. 基础类型

参考文件：YCrypt 的 `sm2/dataType.h`。

验证文件：`QCP_examples/Applications_human/sm2/include/dataType.h`。

### `UINT64`

源码：

```c
#define UINT64 unsigned long long
```

验证代码：

```c
typedef unsigned long long UINT64;
```

原因：QCP 需要将 `UINT64` 作为类型名处理。两种写法的 C 整数类型相同。

### `u32`

源码：

```c
typedef struct {
    u8 v[4];
} u32;
```

验证代码：

```c
typedef struct u32 {
    u8 v[4];
} u32;
```

原因：命名结构体允许 strategy 使用 `field_addr(p, u32, v)`。字段和内存布局
不变。

验证版 `dataType.h` 只保留当前已验证模块使用的类型。Milestone 3 开始验证
ECC 后加入了与参考布局相同的 `AFPoint` 和 `JPoint`；Milestone 5 加入了与参考
布局相同的 `SM2SIG`、`PrivKey` 和 `PubKey`。

### 标准头类型

源码从标准头取得 `bool` 和 `size_t`。验证头文件直接定义：

```c
typedef _Bool bool;
typedef unsigned long long size_t;
#define false 0
#define true 1
```

`MontgInvModp.c` 和 `MontgInvModn.c` 还定义：

```c
typedef unsigned char uint8_t;
```

原因：验证输入不加载系统头。`bool` 直接别名到 C 内建 `_Bool`，保持标准
`<stdbool.h>` 的归一化语义；`size_t` 用作 64 位无符号长度和下标；`true` 和
`false` 保留标准的 1/0 语义；`uint8_t` 用作单字节无符号量。

## 2. 验证接口头文件

验证文件：

```text
include/basicOp.h
include/fieldOp.h
include/sm2_const.h
include/sm2_protocol.h
include/sm3.h
```

`basicOp.h` 和 `fieldOp.h` 导入对应 Rocq 库并声明 annotation 使用的逻辑定义。
被调用函数的 C 声明和 contract 写在各 case C 文件中。

`sm2_const.h` 只保留当前 case 使用的 SM2 常量，并声明相应的数值和内存谓词。
保留的常量使用原类型、数值和初始化方式。

`sm2_protocol.h` 和 `sm3.h` 分别导入 M5 的协议与 SM3 Rocq 定义，并声明拆分
case 使用的逻辑接口。被调用函数的 C 声明和冻结 contract 仍写在各 case C 文件中。

Milestone 3 的 `is_on_curve` 使用曲线系数 `SM2_a` 和 `SM2_b`，因此验证头文件
从参考 `sm2_const.h` 原样保留了这两个 `u32` 常量及其四个 limb 初始化值。

`affine_to_jacobian` 使用参考 `ecc.h` 中的只读文件作用域常量 `JPoint_ZERO`；
验证版 `ecc.h` 原样保留其 `JPoint` 类型和 `(1, 1, 0)` 初始化值。

`affine_to_jacobian` 的 C 实现语句与参考源码一致。验证 annotation 在两个结构体
复制点前使用 `which implies`，把公开规格中的未初始化 limb 数组资源转换为前端
结构体复制所需的 `UndefStructPredu32` 或 `UndefStructPredJPoint`。这是纯逻辑状态
转换，不改变控制流、赋值顺序或内存结果。当前前端会在标量字段写入前按需展开
外层未定义结构体，但嵌套结构体复制不会先做同一展开，因此需要该桥接。

`ecc_montg.c` 的验证接口另使用：

```text
include/ecc_constants.h
include/ecc_memory.h
```

`ecc_constants.h` 保存参考源码中 `BN_ZERO` 和 `MONTG_ONE` 的原始类型和值；
`ecc_memory.h` 只声明 `memcpy`、`memset` 及其 trusted contract。它们用于拆分后的
单函数验证文件，不改变参考实现的对象布局或执行语句。

`ecc_montg/` 下的 `montg_equal_one`、`bignum_is_equal`、
`bignum_set_to_zero`、`copy_bignum`、`montg_set_jpoint_to_zero`、
`montg_is_apoint_zero`、`montg_is_jpoint_zero`、`montg_jpoint_to_apoint`、
`montg_jpoint_to_apoint2`、`montg_apoint_to_jpoint2` 和
`montg_inv_mod_p_ex` 均从参考 `ecc_montg.c` 提取。去除 annotation 后逐函数比较的
可执行 token 与参考定义一致；其中 `montg_inv_mod_p_ex` 保持参考源码对
`MontgInvModp` 的单次调用。

## 3. 赋值语法兼容

### `raw_mul` 和 `raw_pow`

函数：`raw_mul`、`raw_pow`

参考文件：YCrypt 的 `sm2/basicOp.c`。

源码：

```c
result[0] = result[1] = result[2] = 0;
```

验证代码：

```c
result[2] = 0;
result[1] = 0;
result[0] = 0;
```

原因：QCP 前端不能解析该链式赋值。三个数组元素互不重叠，拆分后得到相同的
内存状态。

验证文件：

```text
basicOp/raw_mul.c
basicOp/raw_pow.c
```

### `str_reverse_in_place`

参考文件：YCrypt 的 `sm2/extra.c`。

参考实现在交换字节后通过复合指针赋值同时更新指针：

```c
*p1++ = *p2;
*p2-- = tmp;
```

验证代码保持相同的读写和求值顺序，将指针更新拆成独立语句：

```c
*p1 = *p2;
p1++;
*p2 = tmp;
p2--;
```

原因：QCP 前端不支持左值中的后缀自增/自减。拆分后仍先写入当前地址，
再更新对应指针；循环分支、交换结果和最终指针值均不变。

验证文件：

```text
extra/str_reverse_in_place.c
```

## 4. Montgomery 乘法核心

函数：`sm2p_mong_mul_core`、`sm2n_mong_mul_core`

参考文件：YCrypt 的 `sm2/basicOp.c`。

### 局部静态常量

源码：

```c
static const size_t LEN = 9;
```

验证代码：

```c
const size_t LEN = 9;
```

原因：QCP 不支持函数内具有静态存储期的局部对象。`LEN` 只作为值为 9 的只读
循环界。

### `sm2n_mong_mul_core` 的 `pos`

源码在外层循环体声明 `size_t pos;`，并在 `factor == 1` 的内层循环中重新声明：

```c
size_t pos = 1 + i + j;
```

验证代码复用外层变量：

```c
pos = 1 + i + j;
```

原因：符号执行内部为两个 C 局部对象分配了不同的地址 ID，但生成 Rocq goal
时把两个地址都打印为 `&("pos")`。同址 cell 的分离合取不能表示原程序状态。
复用外层变量后只保留一个 `pos` 对象；每次使用前仍执行相同赋值。

### `sm2n_mong_mul_core` 的快速分支

源码的 `factor == 1` 分支结束后继续执行通用分支。验证代码在该分支末尾加入：

```c
continue;
```

原因：快速分支已经把 `SM2_N` 加入 `interim`。继续执行通用分支会再次加入
`factor * SM2_N`。`continue` 使该路径只执行一次约减步骤。

验证文件：

```text
basicOp/sm2p_mong_mul_core.c
basicOp/sm2n_mong_mul_core.c
```

## 5. `MontgInvModn` 的 Phase II 边界

参考文件：YCrypt 的 `sm2/fieldOp.c`。

源码无条件执行：

```c
memset(&t, 0, 32);
k = 2 * 256 - k;
i = k / 64;
k = k % 64;
t.v[i] = ((UINT64)1) << k;
sm2n_mong_mul(&r, &t, result);
```

验证代码：

```c
if (k != 256) {
    memset(&t, 0, 32);
    k = 2 * 256 - k;
    i = k / 64;
    k = k % 64;
    t.v[i] = ((UINT64)1) << k;
    sm2n_mong_mul(&r, &t, result);
} else {
    memcpy(result, &r, 32);
}
```

原因：Phase I 允许 `k == 256`。此时原代码得到 `i == 4`，访问越界的
`t.v[4]`。该边界下 `r` 已是所需结果，验证代码直接复制 `r`。

验证文件：`fieldOp/MontgInvModn.c`。

## 6. `montg_add_jpoint` 的结构体复制长度

参考文件：YCrypt 的 `sm2/ecc_montg.c`。

源码：

```c
memcpy(&U9, &T, sizeof(U9));
```

验证代码：

```c
memcpy(&U9, &T, sizeof(UINT64) * 4);
```

原因：QCP 前端在该调用点不能把局部 typedef 结构体的 `sizeof(U9)` 直接归约为
四个 `UINT64` limb 的长度。`U9` 和 `T` 均为含四个 `UINT64` 的 `u32`，两种写法
复制相同的 32 字节，不改变源地址、目标地址、控制流或结果。

验证文件：`ecc_montg/montg_add_jpoint.c`。

## 7. Montgomery mixed-add 的同点和逆点分支

参考文件：YCrypt 的 `sm2/ecc_montg.c`。

参考实现计算 `C = x2*z1^2-x1` 和 `D = y2*z1^3-y1` 后无条件进入普通 mixed-add
公式。验证代码在这两步之后加入：

```c
if (bignum_is_equal(C.v, BN_ZERO)) {
    if (bignum_is_equal(D.v, BN_ZERO)) {
        montg_double_jpoint(a, r);
    } else {
        montg_set_jpoint_to_zero(r);
    }
    return 1;
}
```

原因：`C == 0 && D == 0` 表示两个有限输入是同一点，普通 mixed-add 公式会产生
错误的 `z = 0`，正确运算是倍点；`C == 0 && D != 0` 表示两个输入互为逆元，正确
结果是群单位元。该分支使函数在全部合法点输入上实现群加法，并允许调用者使用
不带“有限输入点不同”条件的公开 contract。

验证文件：`ecc_montg/montg_add_jpoint_and_apoint.c`。

`CopyJPoint`、`montg_add_jpoint_ex` 和 `montg_add_jpoint_and_apoint_ex` 去除 annotation
后的函数体 token 与参考定义一致。五个函数中除本节和上一节记录的两处差异外，
其余可执行 token 均与参考源码一致。

## 8. WNAF 动态预计算表的存储期

函数：`montg_times_point_naf_w3`

参考文件：YCrypt 的 `sm2/ecc_montg.c`。

源码：

```c
static AFPoint PT[4] = { 0 };
static AFPoint NT[4] = { 0 };
```

验证代码：

```c
AFPoint PT[4];
AFPoint NT[4];
```

原因：QCP 不支持函数内具有静态存储期的可写数组。函数在每次调用中先由
`montg_pre_compute_naf_w3` 完整写入随后可能读取的槽 1 和 3；槽 0 和 2 从不读取。
因此 automatic 数组保持该调用实际使用的全部表内容和访问顺序，同时使每次调用的
数组所有权局部于当前验证状态。该改写不改变点运算、分支、数组下标或函数输出。

验证文件：`ecc_montg/montg_times_point_naf_w3.c`。

## 9. SM2 密钥与签名边界

参考文件：YCrypt 的 `sm2/sm2.c`。

### `sm2_keypair` 的私钥范围

参考实现只调用一次 `get_random_u32_in_mod_n`。验证代码重复取样，直到私钥同时
满足 `D != 0` 和 `(D + 1) mod N != 0`：

```c
u32 one = { 1, 0, 0, 0 };
u32 d_plus_one;

do {
    get_random_u32_in_mod_n(&(privkey->da));
    add_mod_n(&(privkey->da), &one, &d_plus_one);
} while (u32_eq_zero(&(privkey->da)) ||
         u32_eq_zero(&d_plus_one));
```

原因：随机数接口允许返回 `0 <= D < N`。SM2 私钥要求 `D != 0`，签名公式还需要
`1 + D` 在模 `N` 下可逆，因此同时排除 `D = N-1`。原实现对 `D=N-1` 调用零输入
的 Montgomery 逆元路径时可能越界访问。

### `sm2_sign_dgst` 的 nonce 范围

验证代码在每次取样后拒绝 `K=0`：

```c
get_random_u32_in_mod_n(&k);
if (u32_eq_zero(&k)) {
    continue;
}
```

原因：随机数接口允许返回 `K=0`，SM2 签名 nonce 要求 `1 <= K < N`。后续已有
分支继续拒绝 `R=0`、`(R+K) mod N=0` 和 `S=0`。

### `sm2_sign_dgst` 的横坐标 N 域约减

验证代码在从随机点取得普通仿射横坐标后，先复用 `tmp` 保存其模 N 结果：

```c
mod_n(&(rand_AFPoint.x), &tmp);
add_mod_n(&e, &tmp, &r);
add_mod_n(&r, &k, &tmp);
```

原因：横坐标是 P 域元素，只保证 `0 <= X < P`，而 `add_mod_n` 的实现只对
规范 N 域输入执行正确的一次减 N 约减。SM2 中 `P>N`，当前曲线上存在
`X=N+4` 的点；取 `E=N-4` 时，原实现把 `2N` 计算为 `N` 而不是 `0`。
先调用 `mod_n` 后直接实现标准签名公式 `R=(E+X) mod N`。

### `sm2_verify_dgst` 的无穷远结果

验证代码在取得仿射横坐标前加入：

```c
if (montg_is_jpoint_zero(&point1_jacobian))
    return 0;
```

原因：一般 `R/S` 输入可能使 `[S]G + [R+S]P` 为无穷远点。该结果没有 SM2
验签所需的仿射横坐标，必须作为验签失败处理；原实现会继续把它转换成 `x=0`。

## 10. QCP 前端对齐兼容

参考实现中的局部字节数组会被传给执行 `uint32_t` typed 访问的 SM3 接口。相应
局部对象需要表达 `_Alignas(uint32_t)` 的对齐语义，但 QCP 前端不会从该 C 表达
建立验证所需的地址对齐事实。验证代码在数组声明后调用：

```c
alignas_uint32_t(total);
alignas_uint32_t(ZA);
alignas_uint32_t(dgst);
```

验证专用 trusted 接口为：

```c
void alignas_uint32_t(const void *address)
/*@ Require emp
    Ensure aligned_4(address) && emp
 */;
```

该接口不读取、写入或拥有数组内存，只向符号状态提供本地自动数组的四字节对齐
事实。它只紧邻 `sm2_get_id_digest` 的 `total[250]` 以及 `sm2_sign`、`sm2_verify`
的 `ZA[32]`/`dgst[32]` 声明使用，不用于调用者传入的外部指针。该 wrapper 只处理
QCP 前端未建模的 C 对齐表达语义，不改变算法分支、内存内容或返回值。

## 11. SM3 压缩轮函数

参考实现使用 `ONE_ROUND_16`、`ONE_ROUNDS_16`、`ONE_ROUND_64` 和
`ONE_ROUNDS_64` 四个多语句宏展开 64 轮压缩。验证代码将它们写成四个
`static inline` 函数，并显式传入 `A` 至 `H`、`W`、`k`、`SS1` 和 `SS2` 的地址。

QCP 当前不能在多语句宏展开内部建立函数 contract 和循环轮次边界。inline 函数
逐句保留原宏的赋值顺序、32-bit 运算、`Ti[idx]`/`W[idx]` 读取以及四轮参数轮换；
调用序列仍为 0、4、8、12 的前 16 轮和 16 至 60 的后 48 轮。所有指针都指向
`sm3_compress` 原有的不同局部变量，因此改写不增加可观察内存访问，也不改变
压缩状态和 digest 写回结果。
