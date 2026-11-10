# P5 最终交付审查开发报告

2026-11-09。同一GPT‑6.1 Sol high子代理完成P5构建/示例/发布整理，主代理负责候选包与最终包独立验收。没有修改算法、原QCP/旧实验/权限、历史清单或reviewer_*；未启动形式化验证。

新增examples/qcp_check.c以合法项目分数所有者构造整系数只读视图和原coef/next链表，演示Q/Z/error/资源UNKNOWN和结果清理；输入在结果读取前由调用方销毁。新增make normal可靠恢复普通静态库，sanitize原行为保留兼容历史审查；普通复用与例子不需要额外SAN链接参数。日常benchmark默认改写build下的新结果，冻结P4数据保留。

tools/make_release.py提供确定性源码tar.gz与成员清单/外部SHA，tools/verify_release.py独立检查成员；源码包不依赖原QCP目录运行普通构建/数学测试。PROVENANCE明确哪些原路径/Git核查需原库，且数据布局互操作不等于多套同名MiniGMP运行时可混链。

候选源码/README定稿后由主代理在临时空目录验证解包、普通库和外部消费者、ASan/UBSan及P1–P4回归；最终只补充主代理报告/计划/冻结清单后再次打包复验，避免用未测试目录替代交付件。候选阶段已在本工作区执行make test、make sanitize、make normal及普通无SAN参数的独立两TU消费者。P1 1010、P2 4369、P3默认8334/ALL8564、P4 12630逐点失败及1000分数/184 P3 CLI/96 P4 CLI回归通过，ASan/UBSan无报告；四个示例通过，恢复后普通消费者给出x=1/36893488147419103233并无残余所有权。日志可在build/p5-normal.log、p5-sanitize.log、p5-restored-normal.log重新生成；源码包不依赖这些外部旧日志运行。

新增发布校验回归在普通、python -O及PYTHONOPTIMIZE=1三种模式下均接受原文件、拒绝篡改；verify_release不使用assert作为安全校验。原commit的LICENSE完整复制vendor/QCP_LICENSE，来源哈希见docs/LICENSE_SOURCE.json；仅保留取用上游材料的notice，不为新增代码重新授权。日常benchmark实际写入build新路径后已核对冻结P4 JSON未改。示例额外参数会usage/exit2。

主代理已在实际解包的候选源码上完成完整普通/ASan/UBSan独立验收；成员核验、-O下篡改拒绝、P1–P4数学/故障回归、两种头文件的独立C消费者及候选字节一致重打包均通过，详见docs/ACCEPTANCE_P5.md。候选审查以140个源成员为输入，未使用未测目录替代交付件。

最终包只更新交付状态报告/开发计划、增加主代理P5验收报告及最终P5_HASHES；核心源码、示例、构建规则、工具和测试与通过完整测试的候选包一致。最终成员/归档复核由主代理在新目录执行并写包外release/P5_DELIVERY_RECORD.json，将最终包与候选完整测试关联。包内报告不嵌入本包自身SHA，P5_HASHES排除自身，RELEASE_MANIFEST排除自身，归档摘要仅在包外，避免自引用。
