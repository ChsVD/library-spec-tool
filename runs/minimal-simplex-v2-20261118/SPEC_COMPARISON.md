# Minimal Simplex 自然语言规约对照

## 结论

8 个共有核心函数在当前求解器实际调用域内的主要数学行为接近。顶层双向可行性、初始表的逐项结果、两种扫描顺序、换基公式和资源生命周期均未发现相反承诺。两份材料仍有调用域、表示精度和接口组织差异，其中 entering 的非空字段接口差别最明显。

旧稿取自上次证明各批的自然规约交接。入口使用最后一轮输入，build 使用 2026-11-13 生效修订稿，其余取相应阶段三产物。历史正式契约仅用于核对哪些差异会影响现有接口。v2 另外生成了 11 个自有后端辅助函数，旧交接没有与其逐一配对的自然规约，本表覆盖 8 个共同函数。

运行来源见 [旧证明进度](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/proof/PROGRESS.md)、[旧正式契约](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/contracts/contract.c)及 [v2 实验说明](EXPERIMENT.md)。

| 函数 | 对照结论 | 差异及依据 |
| --- | --- | --- |
| `sx_check_qcp` | 核心承诺一致 | 正常返回的 0/1 与有理可行性双向对应，输入地址、链接、数学值和可清理资源归还，释放内部存储，两版均覆盖空约束和零变量。v2 将统一入口拆为四个命名情景。旧版另明确要求后续提供纯计算判定接口或等价接口，v2 保留精确关系语义和两条退出分支的证明需求，但未将此接口要求同样明确地交付。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/stage3-driver-20261115/specs/sx_check_qcp-c118d07f0c90.md#L12) · [v2](SPECS.md#L7) |
| `integers` | 数组语义一致，具体表示更抽象 | 正长分配得到长度准确的全零可清理数组，零长保留 NULL 或可释放的零大小分配身份。旧稿明确固定初始头的 alloc=0、size=0 和静态 dummy 指针，v2 只承诺合法零值并允许共享 dummy。原 MiniGMP 实现支持旧稿的字段事实，现有 v2 独审仍将后端模型与资源匹配列为待核。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/stage3/specs/integers-957e5e7d7b3f.md#L12) · [v2](SPECS.md#L1048) |
| `release` | 资源消费一致 | 先逐头清理拥有的 limb，再释放原头数组。共享 dummy 保留。v2 把零长 NULL 和零大小分配拆开，另列 destroy 的 d/c/a 三种调用场景。它们都可由旧稿通用清理语义及各调用处保留的框架资源解释。旧正式契约另有 all_counts 统一入口。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/stage3/specs/release-4861a42a63ef.md#L12) · [v2](SPECS.md#L1102) |
| `build` | 数组内容与输入归还一致 | 两版都交付五块独立存储，D=1、常数及原变量系数逐项复制、辅助列为零，basic/row 的初始映射相同。v2 将空维度拆为四种情景。旧稿在 build 后置直接给出初始表方程与原辅助变量定义的等价关系，v2 的数组等式足以推出该关系，但把连接明确放在顶层公共内容需求。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/contracts/input-revision-20261113/specs/build-994a19b9b0b4.md#L1) · [v2](SPECS.md#L386) |
| `destroy` | 资源消费一致 | 三块整数数组及其拥有的 limb、两块索引存储均释放，表头保留，原指针字段不能再解引用。旧稿已允许按实际长度清理可释放资源，v2 将行列零值组合写成命名情景，其中有行无列并非本轮 build 可达的状态。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/stage3/specs/destroy-543c15e6c25d.md#L12) · [v2](SPECS.md#L303) |
| `violated` | 字段扫描一致，完整表结论移为待证桥接 | 两版均按变量编号从 n 开始选择首个对应正 _mp_size 的基本辅助变量，返回其行号，找不到时返回 SIZE_MAX。返回的是首个候选所对应的行号。旧稿还有完整表入口，直接归还完整表快照并给出当前基本赋值的结论。v2 保留只读字段接口，将完整表、符号解释和返回 SIZE_MAX 时构造有理赋值的结论列为公共内容需求。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/stage3-next-batch-20261113/specs/violated-4e8a0ba4dc14.md#L12) · [v2](SPECS.md#L234) |
| `entering` | 求值规则一致，非空调用域收窄 | 两版选择最小合格非基变量，原变量系数非零、辅助变量系数为正，无候选返回 SIZE_MAX。空列都只需读取 cols。旧版非空字段入口只要求实际访问的 row 槽和 _mp_size 字段合法可读，允许任意 size_t 的 n 和 r，只要索引与实际对象有效。v2 非空情景额外要求 n≤cols、r<rows，并要求整行合法整数表示。旧稿的完整表入口可在附加数学条件下直接给出无候选的不可行结论，v2 在公共内容需求中保留这条条件引理。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/stage3-next-batch-20261113/specs/entering-368928343315.md#L12) · [v2](SPECS.md#L92) |
| `pivot` | 精确算法与资源结果一致 | 正负主元的符号、跳过零消元项、GCD 缩放的精确整数商、五数组的唯一更新、基映射及对所有有理赋值的方程等价均一致。v2 将通用非零主元拆为两份。旧稿单列方程残差恒等式及分配令牌的表述，v2 保留对应的等价和资源目标，细节需在下游落实。 [旧稿](../../../library-spec-tool/runs/isolated-simplex-gmp-minimal-20261111-01/stage3-followup-20261115-budget/specs/pivot-19082d9ed501.md#L12) · [v2](SPECS.md#L176) |

## 形式化前需要核对的接口

1. 保留按实际字段访问组织的扫描接口。对 entering，可把 _mp_size 和 row 的字段级扫描，与要求合法整数表示、正分母、有效基及表方程的求解器接口分开。这样局部内存安全的适用域与全表数学结论都能表达。violated 可沿同样的接口组织保留完整表版本。
2. 明确初始化结果需要的表示层次。如果下游需要旧版整数头数组的具体 dummy 资源，应显式要求相同字段结果，或补出从初始化资源到调用者所需资源的桥接。若只需要数学零，也应记录清理资源如何建立。
3. 在命名入口的前置条件中显式绑定变量和条件。v2 顶层和建表的部分情景把行列为零或非零写在 With 里。形式化时应在 Require 中用实参和逻辑状态绑定这些条件。顶层可统一写为一份总契约，并用针对空约束和常数约束的推论支持调用。
4. 补齐可组合的数学接口。build 建立初始表方程，pivot 保持方程等价，violated 与 entering 给出退出分支需要的条件。v2 的公共内容已经记录多数连接。旧顶层还要求把精确判定关系通过一个明确的可计算接口或等价接口交给下游。

旧证明采用 Arch32 BigEndian，v2 分析采用 WSL x86-64 LP64。两者的整数数学语义可对读，但 size_t、指针、结构体布局和分配跨度的前提按各自配置解释。对照结论属于自然规约文本审查，v2 的正式调用和函数证明仍待验证。
