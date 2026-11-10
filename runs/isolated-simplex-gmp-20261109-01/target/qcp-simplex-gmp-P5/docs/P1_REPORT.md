# P0/P1 实现与验证记录

2026-11-06，Ubuntu-24.04 WSL，GCC/cc默认工具链；具体编译命令由Makefile和日志保留。

交付：61个项目MiniGMP文件的完整原始哈希和Git状态；同源副本及一个显式长度扫描适配；P0未来接口、换基公式、不变量保持理由和未完成终止证明义务；P1 TLS事务运行时、动态分数所有权、十进制导入导出、规范化四则和比较、交叉约分和零快捷路径；静态库及独立CLI；新写测试。

完成的命令及结果：

- `make test`：1010个逐点分配失败，全部回收本事务块且保留旧输出；C别名、资源分类、非法输入、动态100对象、重复清理测试通过。新src/tests以-Wall -Wextra -Werror -Wpedantic -Wconversion -Wshadow编译。
- `python3 tests/check_fraction.py`：1000个精确CLI对照通过（Python标准库Fraction），涵盖32/64位边界、低limb零、2^512共同因子、至1024位的确定种子随机输入。
- `make sanitize`：上述全部测试在AddressSanitizer+UndefinedBehaviorSanitizer下通过，无报告。日志build/sanitize.log。
- `python3 tests/check_baseline.py`：61个原文件、commit、完整porcelain状态与冻结时一致；除了记录的mpz_make_odd.c适配，副本与来源哈希一致。

主代理独立写的reviewer_fraction.py另行验收，不当作本实现者自测数字；最终验收由主代理复跑并报告。

限制：没有表/求解循环，不提供任何SAT/UNSAT结果；没有启动QCP形式化验证。最小索引规则无预算终止证明尚未完成，未来须保留有限换基预算。max_bytes只计单次事务payload，排除分配头、Tx和存活输出，不是全模块总内存界。对象必须同线程拥有，raw MiniGMP函数不支持公共直接调用，当前无独立public整数API，未来输入由P2适配。临时结果到事务结束统一回收会增加峰值，保守limb预测可能提前SX_LIMIT；无时间抢占。实际可分配规模及原库全部API不在安全承诺内，未形式化证明源代码子集，测试不是数学正确性的完整证明。
