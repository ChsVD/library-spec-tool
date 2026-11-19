# 阶段三公共内容

已审核 1 / 1 条需求，待处理 0 条，共享条目 1 项。
当前状态 `completed`，模型请求 7 次，参考原文读取 6059 字符。

## 逐需求交付

### definition · Model the fields read by downstream code; distinguish the target probe from the whole representation.

`fn-85c3fb94fe0d59f1da3de85f:1:d8cffa7d77a034c4`

For OpenSSL struct BIGNUM (bignum_st): find reference definitions describing a dynamic signed multiple-precision number, its backing limb array and which prefix is used. Need a connection between memory fields d (least-significant limb first), top (used length), dmax (allocated capacity), neg (sign), and the mathematical integer. Identify which fields, ownership and value interpretation the precedent actually supports and any layout adaptations.

上游状态 `approved`。在交付的 Linux x86_64、C11 配置下，project/target/normalized.c:1–8 确认 d 的类型为 BN_ULONG *，BN_ULONG 是 unsigned long long 的别名。第 18–21 行支持 read_data_field 情景：若 p 指向有效对象且 d 字段已初始化并可合法读取，函数只读取该字段，返回入口指针值（含空指针），且无内存写入。其他字段无需初始化，函数不访问 d 所指存储。注释在入口和返回时使用同一字段存储断言。草案明确排除了非法字段读取和对所指存储的额外保证。交付材料未列出调用情景，也未确认 store 的形式化权限模型或 QCP 验证状态。

处理状态 `accepted`，覆盖 `partial`，结论 `adaptation`，适用性 `requires_target_validation`，目标验证 `not_run`。

候选定义覆盖下游使用的字段对应、有效前缀、容量与有符号求值。实际使用位置是 normalized.c 第 18–21 行的 bn_data_probe。函数只读取 p->d，返回入口指针值，包括空指针，并且没有内存写入。源码规约在入口与返回处写有同一个字段存储断言。此处把完整表示作为可选的调用者前提。已交付材料没有下游调用位置，形式化调用验证状态为 not_run。

**共享条目**

- [BIGNUM 的有效字前缀与有符号整数表示](#item-ae74205d691918fea854577a42ec4a314a771be99413f21202a1d5d4e85d11c5)

**对象对应**

- mini-GMP 的 _mp_d 对应目标 d，_mp_alloc 对应目标 dmax，|_mp_size| 对应目标 top。_mp_size 的符号信息对应候选定义中的独立 neg 字段。
- mpd_store_Z_compact 中的 data 对应目标有效字序列 L；store_Z 中用 UIntArray.undef_seg 描述的余段对应候选布局中的 [top,dmax)。
- 先例用 UIntArray 描述元素存储，目标 d 的类型为 unsigned long long *。采用低位字优先的递推时，目标须使用与 BN_ULONG 匹配的元素类型、步长、界和基数。目标 flags 在这组先例字段中没有对应项。

**使用条件**

- 在 bn_data_probe 入口，p 指向有效 BIGNUM 对象，p->d 已初始化并可合法读取，源码规约要求 store(&(p->d), q)。其他字段无需初始化，探针无需持有 q 指向的存储。
- 若下游已经建立完整表示，候选定义中的 d 字段记录提供提取入口指针值所需的事实。形式化调用还须证明该字段资源符合目标 store 的权限规则。探针的返回值本身只提供指针值相等这一事实。
- 下游读取 q[i] 时，另须建立对应 BN_ULONG 元素的存活存储、合法寻址、下标范围和已初始化读取权限。紧凑形、符号约定及 flags 对缓冲区所有权的影响均须由下游所用规约确认。

**未解决事项**

- 参考读取额度用尽，尚未取得 same_sign、list_within_bound、Base 或 UINT_MOD，以及 UIntArray.full 和 undef_seg 的底层声明或规则。现有摘录支持断言的组成与值递推，尚不能核实先例的精确数值界、分配权或逐元素读取权限。
- 尚缺目标 BN_ULONG 数组的形式化前缀和余段断言，以及从完整表示提取并归还目标 store 字段资源的规则。目标 store 的权限模型和 QCP 验证状态未确定。
- 尚缺目标构造或更新规约来确认 neg 的取值、零值与紧凑形约定、flags 相关所有权、后备区生命周期及释放权。交付材料没有具体下游调用可供核对这些前提。

**目标材料**

- `project/target/normalized.c:1–8`
- `project/target/normalized.c:18–21`
- `supplemental/top_level/0/TOPLEVEL_SPEC.md:1–4`

**参考依据**

- `Rocq/examples/Applications_human/minigmp/GmpNumber.v:909–915` 完整声明显示三个字段的存储断言、|size| ≤ cap、same_sign 条件，以及紧凑前缀和容量余段的分离。目标的独立 neg、flags、字段布局和缓冲区释放权需要独立依据。
- `Rocq/examples/Applications_human/minigmp/GmpNumber.v:95–97` 完整声明将序列值、长度、元素界和末字条件与同一个前缀资源关联。元素界通过 list_within_bound 表达，其具体定义尚未核实。
- `Rocq/examples/Applications_human/minigmp/GmpNumber.v:76–77` 完整声明将前缀资源展开到 UIntArray.full，参数为基地址、序列长度和序列值。逐元素读取及所有权仍取决于数组断言的底层规则。
- `Rocq/examples/Applications_human/minigmp/GmpNumber.v:79–83` 完整递推表明空序列值为零，表头处在最低位，其余各项按 Base 进位。目标的 2^64 基数来自交付配置下的 BN_ULONG 类型。

检索 `searched`。检索了 OpenSSL 字段、mini-GMP 动态有符号表示，以及数组资源和 64 位字的相关声明。根据已取得的完整声明采用 mini-GMP 的表示结构。关键依赖继续读取时达到参考源额度，检索命中与生成验证条件未用作定义或目标验证的依据。

审核 `accept`。mini-GMP 摘录支持三个字段的存储断言、有效前缀与容量余段的分离，以及表头为最低有效字的幅值递推。候选将目标的独立 neg 字段、BN_ULONG 数组布局和资源权限作为下游规约需建立的条件。目标源码支持探针仅读取并返回 p->d 的入口值，注释在入口和返回处使用同一字段断言。交付材料没有具体下游调用，目标字段资源的形式化提取规则及参考断言的底层语义仍待核实。

**上游复查**

- 针对 normalized.c 第 19–20 行的 store(&(p->d), d)，定位目标 store 的定义及权限规则，核对下游完整表示能否在调用前提供该字段资源，并在返回后用归还的资源重建表示。
- 针对原需求中的 d、top、dmax、neg 与数学整数的对应，查阅目标 BIGNUM 的构造和更新规约，确认有效前缀的初始化、neg 的取值及零值约定，并核对 flags 对后备区所有权与释放权的影响。
- 针对参考 store_Z 的 same_sign 与 UIntArray.undef_seg 子句，以及 mpd_store_Z_compact 的 list_within_bound 子句，补读定义和数组规则，核对符号条件、Base 与 UINT_MOD 的关系、精确元素界及前缀和余段各自提供的权限。

## 共享定义、引理和 strategy

<a id="item-ae74205d691918fea854577a42ec4a314a771be99413f21202a1d5d4e85d11c5"></a>
### BIGNUM 的有效字前缀与有符号整数表示

`item:ae74205d691918fea854577a42ec4a314a771be99413f21202a1d5d4e85d11c5` · `definition`

这是供下游规约采用的候选定义。参数为对象地址 p、数学整数 N、后备存储地址 q、有效长度 t、容量 c、符号标记 s 和有效字序列 L。字段资源分别记录 p->d = q、p->top = t、p->dmax = c、p->neg = s，并要求 0 ≤ t ≤ c、L 的长度为 t。数组按 BN_ULONG 元素寻址，L[i] 对应 q[i]，下标 0 对应最低有效字。有效前缀 [0,t) 的资源记录已初始化的元素值。若规约还需要持有整个后备区，则对 [t,c) 单独描述存储资源，其内容不参与求值，该资源本身不保证元素已初始化或可读。容量边界只约束下标，实际访问仍需对应的存储和权限。令 B 为 2 的 BN_ULONG 值位数次幂，在交付的 Linux x86_64 配置下 B = 2^64。每个有效字满足 0 ≤ L[i] < B，幅值 M = Σ_{0≤i<t} L[i] × B^i，空前缀的幅值为 0。若下游规约采用 s = 0 表示非负、s = 1 表示负的约定，则分别定义 N = M 和 N = −M。若另需紧凑规范形，再要求 t > 0 时 L[t−1] 非零，并约定空前缀的 s 为 0。mini-GMP 的 store_Z 提供字段、有效前缀与容量余段分离的结构。其紧凑子断言把前缀长度和幅值绑定到同一序列，list_to_Z 的递推让表头处于最低位。这些声明支持上述结构与求值方向。目标字段类型、符号约定和存储断言须按目标重新建立。flags、分配来源及释放权由相应规约另行描述。

`Rocq/examples/Applications_human/minigmp/GmpNumber.v:95–97`

    Definition mpd_store_Z_compact (ptr: addr) (n size: Z): Assertion :=
      EX data,
        “ list_to_Z data = n /\ last data 1 >= 1 /\ list_within_bound data ” && “ size = Zlength data ” && mpd_store_list ptr data.

`Rocq/examples/Applications_human/minigmp/GmpNumber.v:909–915`

    Definition store_Z (x: addr) (n: Z): Assertion :=
      EX (ptr: addr) (size cap: Z),
        “ Zabs size <= cap ” && 
        “ same_sign n size ” && mpd_store_Z_compact UINT_MOD ptr (Z.abs n) (Z.abs size) ** UIntArray.undef_seg ptr (Z.abs size) cap **
        &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
        &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
        &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

`Rocq/examples/Applications_human/minigmp/GmpNumber.v:76–77`

    Definition mpd_store_list (ptr: addr) (data: list Z): Assertion :=
      UIntArray.full ptr (Zlength data) data.

`Rocq/examples/Applications_human/minigmp/GmpNumber.v:79–83`

    Fixpoint list_to_Z (data: list Z): Z :=
      match data with
        | nil => 0
        | a :: l0 => (list_to_Z l0) * Base + a
      end.
