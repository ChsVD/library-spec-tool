# 项目 MiniGMP 工程适配

原始完整哈希见 BASELINE_MANIFEST.json；所有副本文件与来源逐项核对，仅 mpz_make_odd.c 有局部变化，原文件另存 docs/mpz_make_odd.c.original。该变化以 _mp_size 显式有界扫描低零limb并处理零入口，代替无长度mpn_scan1入口。原mpn_scan1把un=i传给扫描函数，终止边界不符合长度含义；在规范化非零对象前提下仍会遇到非零末limb，不能据此声称合法输入确定越界。新增入口不再依赖该隐式前提，未更换整数算法。其注释中已有QCP规约不代表适配代码经过验证。

原set_ui、set_si是32位limb假设；LP64宽long不是通用整数导入。公共API十进制逐位构造，直接ui参数仅0..10；不暴露原始整数API。系统GMP对象不能传入。仅审查过的路径：init/set/neg/abs/add/sub/mul/gcd/divexact及内部trunc除余、shift、mpn原语。没有声称原库任意API安全。

## 失败机制

所有底层外部分配原语在 src/arith.c 实现，分配块有对齐头部和双向事务链。allocator遇到实际失败或fail_at注入直接longjmp，不向原库返回NULL。唯一捕获点为公共API内部run。TLS拒绝嵌套入口，事务内没有外部回调，不允许信号处理器重入这些API。C++调用者不可绕过入口，后端跳转不跨外部C++析构栈。事务上下文在堆上；跳转后只读取未改变的volatile上下文指针和堆字段，不读取跳转后修改的自动对象。成功提交之前不修改调用者结果；输出可别名a或b（含a=b=out）。失败统一释放本次链上的全部块，旧输出保持；成功只detach两个输出limb块或导出字符串，然后清理旧输出和剩余临时。长期输出头部不指向已销毁事务。clear幂等。多线程可各自独立用对象；对象必须在同一线程创建、操作、清理，不允许跨线程移交。

上下文calloc为分配点1，逐点故障注入覆盖它。每次backend realloc使用allocate/copy/free，旧块直到新块成功才释放。记录live blocks可检查所有权；不用malloc_usable_size等不可移植接口。外部裸mpz函数不属于支持接口，必须禁止调用；链接符号存在仅用于独立构建。

## 数值及预算边界

每个原语调用前检查保守长度：add/sub max(n,m)+1；mul n+m；gcd max(n,m)+2；divexact n+1；解析每位经过这些检查。每个整数缓冲区分配也限制到max_limbs。max_limbs必须在[4,INT_MAX/64]，默认1048576。原库可见int长度运算为加1、乘2或加两个长度；乘法预检查n+m保证该表达式不溢出，除法nn-dn+1在nn>=dn>0时不超过nn，shift从受限limb长度生成，转换回int不溢出；GCD消去2幂不增加输入位长，恢复最多原输入长度加1，预留2limb。INT_MAX/64同时为余下bit/limb转换保留32倍和额外常数余量。这是所用函数子集的保守工程界和源码审计，不是形式化证明。接近该硬界的真实分配无法由常规测试覆盖。

max_bytes当前精确定义为“单次事务同时存活分配payload”上限，默认64MiB，含整数临时、对象、导出临时，不含Tx本身、Block头、已存在/成功转交的输出块、外部输入及栈；不是整个进程或未来求解器总内存上限。上下文分配及头部溢出单独检查；所有size_t乘法在受限limb数或SIZE_MAX检查后进行。求解器总表空间另设max_table_bytes。

max_limbs保守预测可能因中间估计拒绝最终可容纳的操作；max_bytes也因事务保留临时而偏保守。返回SX_LIMIT，不能解释为数学UNSAT；实际malloc失败返回SX_OOM。SX_INVALID含非法十进制和除零；SX_INTERNAL含重入。不设置数学状态。时间预算和求解UNKNOWN reason只在P2/P3集成，不冒称已实现。

诊断：每个公共API初始化SxStats（若非NULL），其中reason区分BAD_ARGUMENT、BAD_DECIMAL、ZERO_DENOMINATOR、DIV_ZERO、BYTES、LIMBS、SIZE_OVERFLOW、ALLOC、REENTRY；成功为NONE。分配尝试包含失败点及上下文，peak_bytes仅payload。调用方需将stats传入以获取详细原因；错误类别不依赖它。
