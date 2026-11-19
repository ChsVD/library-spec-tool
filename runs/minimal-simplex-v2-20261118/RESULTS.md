# 自然规约运行结果

## 原样调用图试验

- 状态 in_progress，已保存 1/8 个函数。
- 1 份规约草稿。审核分布 {'conditional': 1}。
- 模型完成调用次数 {'write': 9, 'review': 1}，接受补图 0 条。
- 形式化调用验证 not_run。
- 产物 [stage2.json](stage2-native/stage2.json)，[运行事件](stage2-native-events.jsonl)。

已保留入口记录并手动结束原样试验，后续使用链接证据输入。

| 函数 | 审核状态 | 规约情景 |
| --- | --- | --- |
| release | 未提交 |  |
| build | 未提交 |  |
| destroy | 未提交 |  |
| integers | 未提交 |  |
| violated | 未提交 |  |
| pivot | 未提交 |  |
| entering | 未提交 |  |
| sx_check_qcp | conditional | empty_constraints、constant_constraints、rational_linear_constraints |

### 入口规约

判断有限整数线性非严格不等式系统在有理数域上的可行性。正常返回时，0准确表示存在有理解，1准确表示不存在有理解；交还借入的输入资源并释放求解器内部存储。本规约不保证终止。

#### empty_constraints

With  入口维数n、空节点快照P、空头地址矩阵H和0×(n+1)矩阵C。

Require  head=NULL，m=0，E成立。无需提供任何输入节点或系数资源；n仍须满足公开尺寸条件及内部索引数组分配条件。

Ensure  返回0，空约束系统在Q^n上可行。归还空输入资源，释放全部内部拥有存储。实现仍执行build和destroy；n>0时会建立长度n的row数组，不能把本情景理解为无分配的直接返回。零大小数组不被解引用，其分配结果按分配器契约释放。

#### constant_constraints

With  n=0，m>0，入口快照P、H及m×1整数矩阵C。

Require  InputRep(P,H,C)和E成立。每个节点仍须提供一个合法、已初始化的常数整数头；不能因没有变量而省略coef资源。

Ensure  正常返回值由入口常数确定：若所有C[i,0]≤0，返回0；若存在C[i,0]>0，返回1。这分别等价于存在、不存在Q^0中的解。交还ReturnedInput(P,H,C)，释放全部内部拥有存储，不公开见证或错误对象。

#### rational_linear_constraints

With  n>0，m>0，入口节点及头地址快照P、H，入口整数矩阵C。

Require  InputRep(P,H,C)和E成立。每行表示C[i,0]+Σ C[i,j+1]x[j]≤0，原变量自由且取有理数。允许任意符号及任意合法长度的整数系数、常数行、重复行、全零行、无用变量和非互素系数。

Ensure  返回值只能为0或1；返回0当且仅当存在x使SatQ(C,x)，返回1当且仅当不存在这样的x。返回0不推出整数可满足，返回1推出整数不可满足。交还ReturnedInput(P,H,C)，全部表数组、索引数组、内部大整数及后端临时拥有存储均已释放。没有公开解向量、证明对象或错误状态；正常返回保证不蕴含终止保证。

#### 审核意见

草案准确对应background/0/TOPLEVEL_SPEC.md:11–83的正常返回目标、输入资源归还、尺寸及轨迹容量条件，并分别覆盖空约束、零变量常数约束和一般有理约束。project/target/src/solver.c:83–155支持建表、两种退出判断及统一销毁路径；:24–80的换基在精确整数运算语义下保持有理方程，未发现草案与源码的直接冲突。空约束仍可能分配row，零变量仍读取常数头；草案对此及分配失败、非法输入和不保证终止均有明确说明。条件性保留：TableInv的资源实现、MiniGMP初始化／复制／清理接口衔接，以及全部内部和后端临时存储释放尚缺检查依据；已交付mpz_set和store_Z片段不能单独证明完整生命周期。当前编译为Linux x86-64 LP64，历史契约为QCP Arch32 BigEndian，布局、尺寸和后端契约迁移尚未验证。须在各自模型中落实这些接口及BackendCapacityOK(trace)，才能批准相应实现保证；本结论不表示形式化证明或QCP调用测试通过。

## 链接证据主试验

- 状态 in_progress，已保存 13/19 个函数。
- 13 份规约草稿。审核分布 {'conditional': 13}。
- 模型完成调用次数 {'write': 30, 'review': 31}，接受补图 0 条。
- 形式化调用验证 not_run。
- 产物 [stage2.json](stage2-link-evidence/stage2.json)，[运行事件](stage2-link-evidence-events.jsonl)。

最后错误 invalid model report: missing call evidence for call-35fa5c1e1992d2bb71fceb5a

| 函数 | 审核状态 | 规约情景 |
| --- | --- | --- |
| release | 未提交 |  |
| build | conditional | 空约束且无变量、空约束且有变量、非空约束且无变量、非空约束且有变量 |
| free_gmp_div_inverse | 未提交 |  |
| destroy | conditional | 无行且无列的空表、无约束但具有变量列的表、具有行和列的表、有行但无列的通用清理入口 |
| mpn_zero_p | conditional | 零长度检查、正长度完整数组检查、负长度实现行为 |
| int_swap | conditional | 分离整数交换及局部长度调用、分离容量字段交换、分离有效长度字段交换、同址自交换 |
| integers | 未提交 |  |
| malloc_mpz_struct | conditional | 头对象分配成功、头对象分配失败 |
| gmp_realloc_limbs | 未提交 |  |
| mpz_srcptr_swap | conditional | 分离指针变量交换、同一指针变量自交换 |
| violated | conditional | 空扫描区间、非空扫描且没有正项候选、非空扫描且存在正项候选 |
| gmp_free_limbs | 未提交 |  |
| gmp_alloc_limbs | 未提交 |  |
| malloc_gmp_div_inverse | conditional | 除法调用者所需的成功分配、成功分配假设之外的分配失败 |
| pivot | conditional | 正主元换基、负主元换基 |
| entering | conditional | 空列扫描、最小合格变量为原变量、最小合格变量为松弛变量、非空行不存在合格变量 |
| free_mpz_struct | conditional | 空指针释放、清理后的临时整数头、头内容未知或尚未初始化 |
| sx_check_qcp | conditional | 空约束、无变量且所有常数约束成立、无变量且存在矛盾常数约束、含变量的非空约束系统 |
| mp_ptr_swap | conditional | 分离指针槽交换、同一指针槽自交换 |

### 入口规约

检查整数系数非严格线性不等式组在有理数域上的可满足性。满足前置条件且正常返回时，返回0当且仅当存在有理解，返回1当且仅当不存在有理解；归还借入的输入资源并释放求解器内部拥有的存储。这是待验证的自然语言需求，不代表已完成函数证明。

#### 空约束

With  With n、空矩阵c以及入口资源快照。

Require  Require head=NULL、m=0，并满足公共前提P。即使没有约束，仍需满足k=n的索引数组尺寸和实际分配条件；不能把整个执行的资源需求视为emp。

Ensure  Ensure 正常返回时返回0；空约束在Q^n上可满足，包括n=0时的空赋值。满足公共归还保证R。零大小分配结果不被作为数组元素解引用，按分配器契约释放。

#### 无变量且所有常数约束成立

With  With m>0、n=0、入口矩阵c及输入资源快照；Q^0只含空赋值。

Require  Require 公共前提P，且对每个i∈[0,m)，c[i,0]≤0。每个节点仍须有一个合法、已初始化的常数整数头。

Ensure  Ensure 正常返回时返回0，空赋值满足全部约束；满足公共归还保证R。

#### 无变量且存在矛盾常数约束

With  With m>0、n=0、入口矩阵c及输入资源快照。

Require  Require 公共前提P，且存在i∈[0,m)使c[i,0]>0。

Ensure  Ensure 正常返回时返回1，原系统不存在有理解，也不存在整数解；满足公共归还保证R。该返回表示约束矛盾，不表示分配失败或容量不足。

#### 含变量的非空约束系统

With  With m>0、n>0、入口矩阵c及输入资源快照。

Require  Require 公共前提P。所有约束均为整数系数的非严格小于等于零关系，原变量自由且按有理数解释；允许负系数、零系数、任意精度整数、常数行、重复行、全零行和无用变量，不要求行GCD为1。

Ensure  Ensure 正常返回时返回值属于{0,1}，且返回0当且仅当存在x满足SatQ(c,x)，返回1当且仅当不存在这样的x。返回0不保证存在整数解；返回1推出不存在整数解。满足公共归还保证R。函数不返回可读取的满足赋值或不可满足证书。

#### 审核意见

草案符合background/0/TOPLEVEL_SPEC.md:11–21、25–83规定的有理可满足性、输入资源归还及环境条件；四个命名情景覆盖空约束、无变量的成立／矛盾常数系统及非空含变量系统，明确不保证终止，不将分配失败解释为0/1。project/target/src/solver.c:136–155支持两种返回分支及正常退出前清理，但完整数学和资源保证仍有具体待核对接口：138行无条件调用build，P提供链表、整数资源及尺寸条件，需要建立完整Table并保留输入；141行在建表或换基后调用violated，需要Table提供合法映射和整数符号，118–124行支持其只读首个违反行搜索；146行在r有效时调用entering，需要整行可读，126–134行支持最小合格非基列及未找到时的符号事实；151行在r、e有效且主元非零时调用pivot，25–81行支持所述换基结构，但保持Table仍依赖后端算术、精确除法和资源契约；153行在结果确定后调用destroy，18–22、109–116行支持逐项清理和释放结构，零长度循环不访问元素。未交付可应用的mpz_init、mpz_set、算术及mpz_clear契约，故初始零列、输入合法资源归还、换基算术及最终limb释放尚不能独立确认。BackendCapacityOK(trace)是显式环境条件，不能替代缺失的契约匹配；当前LP64配置与历史Arch32 BigEndian的尺寸、布局及unsigned long适配亦未验证。上述缺口使草案可作为条件化需求使用，尚不足以批准其全部实现保证；未据此声称完成QCP调用测试或正式证明。

## 报告规则澄清后续跑

- 状态 partial，已保存 19/19 个函数。
- 19 份规约草稿。审核分布 {'conditional': 19}。
- 模型完成调用次数 {'write': 14, 'review': 6}，接受补图 0 条。
- 形式化调用验证 not_run。
- 产物 [stage2.json](stage2-link-evidence-clarified/stage2.json)，[运行事件](stage2-link-evidence-clarified-events.jsonl)。

| 函数 | 审核状态 | 规约情景 |
| --- | --- | --- |
| release | conditional | 空数组且指针为NULL、空数组且持有零大小分配、一般正长度整数数组、destroy清理d数组、destroy清理c数组、destroy清理a矩阵存储 |
| build | conditional | 空约束且无变量、空约束且有变量、非空约束且无变量、非空约束且有变量 |
| free_gmp_div_inverse | conditional | 空指针清理、释放未初始化或部分初始化的拥有块、释放已初始化的拥有块 |
| destroy | conditional | 无行且无列的空表、无约束但具有变量列的表、具有行和列的表、有行但无列的通用清理入口 |
| mpn_zero_p | conditional | 零长度检查、正长度完整数组检查、负长度实现行为 |
| int_swap | conditional | 分离整数交换及局部长度调用、分离容量字段交换、分离有效长度字段交换、同址自交换 |
| integers | conditional | 零长度分配、正长度初始化成功 |
| malloc_mpz_struct | conditional | 头对象分配成功、头对象分配失败 |
| gmp_realloc_limbs | conditional | 全部内容已知的扩容或等容量替换、有效前缀已知且剩余容量未知的扩容、全部内容未知的扩容、缩容并保留可容纳的已知前缀 |
| mpz_srcptr_swap | conditional | 分离指针变量交换、同一指针变量自交换 |
| violated | conditional | 空扫描区间、非空扫描且没有正项候选、非空扫描且存在正项候选 |
| gmp_free_limbs | conditional | 空指针释放、非空零大小分配释放、一般存活分配块释放、mpz_clear释放拥有的limb、多字除法释放归一化临时除数、单字除法释放独立临时工作区 |
| gmp_alloc_limbs | conditional | pos_realloc_替换块申请、pos_div_qr_除法临时区、pos_div_qr_1_preinv_除法临时区、pos_init2_整数容量申请、pos_realloc_零容量对象首次分配、zero_零大小申请、positive_failure_非零申请失败 |
| malloc_gmp_div_inverse | conditional | 除法调用者所需的成功分配、成功分配假设之外的分配失败 |
| pivot | conditional | 正主元换基、负主元换基 |
| entering | conditional | 空列扫描、最小合格变量为原变量、最小合格变量为松弛变量、非空行不存在合格变量 |
| free_mpz_struct | conditional | 空指针释放、清理后的临时整数头、头内容未知或尚未初始化 |
| sx_check_qcp | conditional | 空约束、无变量且所有常数约束成立、无变量且存在矛盾常数约束、含变量的非空约束系统 |
| mp_ptr_swap | conditional | 分离指针槽交换、同一指针槽自交换 |

### 入口规约

检查整数系数非严格线性不等式组在有理数域上的可满足性。满足前置条件且正常返回时，返回0当且仅当存在有理解，返回1当且仅当不存在有理解；归还借入的输入资源并释放求解器内部拥有的存储。这是待验证的自然语言需求，不代表已完成函数证明。

#### 空约束

With  With n、空矩阵c以及入口资源快照。

Require  Require head=NULL、m=0，并满足公共前提P。即使没有约束，仍需满足k=n的索引数组尺寸和实际分配条件；不能把整个执行的资源需求视为emp。

Ensure  Ensure 正常返回时返回0；空约束在Q^n上可满足，包括n=0时的空赋值。满足公共归还保证R。零大小分配结果不被作为数组元素解引用，按分配器契约释放。

#### 无变量且所有常数约束成立

With  With m>0、n=0、入口矩阵c及输入资源快照；Q^0只含空赋值。

Require  Require 公共前提P，且对每个i∈[0,m)，c[i,0]≤0。每个节点仍须有一个合法、已初始化的常数整数头。

Ensure  Ensure 正常返回时返回0，空赋值满足全部约束；满足公共归还保证R。

#### 无变量且存在矛盾常数约束

With  With m>0、n=0、入口矩阵c及输入资源快照。

Require  Require 公共前提P，且存在i∈[0,m)使c[i,0]>0。

Ensure  Ensure 正常返回时返回1，原系统不存在有理解，也不存在整数解；满足公共归还保证R。该返回表示约束矛盾，不表示分配失败或容量不足。

#### 含变量的非空约束系统

With  With m>0、n>0、入口矩阵c及输入资源快照。

Require  Require 公共前提P。所有约束均为整数系数的非严格小于等于零关系，原变量自由且按有理数解释；允许负系数、零系数、任意精度整数、常数行、重复行、全零行和无用变量，不要求行GCD为1。

Ensure  Ensure 正常返回时返回值属于{0,1}，且返回0当且仅当存在x满足SatQ(c,x)，返回1当且仅当不存在这样的x。返回0不保证存在整数解；返回1推出不存在整数解。满足公共归还保证R。函数不返回可读取的满足赋值或不可满足证书。

#### 审核意见

草案符合background/0/TOPLEVEL_SPEC.md:11–21、25–83规定的有理可满足性、输入资源归还及环境条件；四个命名情景覆盖空约束、无变量的成立／矛盾常数系统及非空含变量系统，明确不保证终止，不将分配失败解释为0/1。project/target/src/solver.c:136–155支持两种返回分支及正常退出前清理，但完整数学和资源保证仍有具体待核对接口：138行无条件调用build，P提供链表、整数资源及尺寸条件，需要建立完整Table并保留输入；141行在建表或换基后调用violated，需要Table提供合法映射和整数符号，118–124行支持其只读首个违反行搜索；146行在r有效时调用entering，需要整行可读，126–134行支持最小合格非基列及未找到时的符号事实；151行在r、e有效且主元非零时调用pivot，25–81行支持所述换基结构，但保持Table仍依赖后端算术、精确除法和资源契约；153行在结果确定后调用destroy，18–22、109–116行支持逐项清理和释放结构，零长度循环不访问元素。未交付可应用的mpz_init、mpz_set、算术及mpz_clear契约，故初始零列、输入合法资源归还、换基算术及最终limb释放尚不能独立确认。BackendCapacityOK(trace)是显式环境条件，不能替代缺失的契约匹配；当前LP64配置与历史Arch32 BigEndian的尺寸、布局及unsigned long适配亦未验证。上述缺口使草案可作为条件化需求使用，尚不足以批准其全部实现保证；未据此声称完成QCP调用测试或正式证明。

