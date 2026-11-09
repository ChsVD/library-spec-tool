# FM-Agent 函数依赖图

阶段二默认使用 `fm-agent` 后端。直接导入上游模块，不重新实现其调用边或函数指针解析算法：
- FM-Agent：https://github.com/fmagent-project/FM-Agent ，固定提交 `c552cd5ef25bd096178c7b06d3645dc3fd1e376e`。
- CodeGraph：https://github.com/fmagent-project/codegraph ，上游固定构建 `1.6.2-fmagent.1`。这是 FM-Agent 使用的第三方 CodeGraph 分支，底层包含 tree-sitter 索引。
- `src/languages/c.py` 调用 `clang.py` 和 `codegraph.py`；`c_indirect.py` 补充间接调用。
- Clang 使用命令行 JSON AST，不是 Python libclang。当前 WSL 安装 Ubuntu Clang 18.1.3。

## 环境与运行

在 Ubuntu-24.04 WSL 内，从项目根目录执行：

```sh
bash scripts/setup_graph.sh
python3 -m stage3 --manifest stage2/manifests/openssl-bn-word-group.json --output runs/new-graph-plan --prepare-only
```

安装目录为 `.deps/FM-Agent`、`.deps/codegraph`、`.venv-graph`。脚本拒绝已有 FM-Agent 的版本漂移或跟踪文件改动，不会强制重置它。Python 图分析依赖与主程序隔离，只安装静态分析所需部分，不安装/运行 FM-Agent 模型和证明流水线。CodeGraph 分析运行关闭遥测。

有实际构建数据库时加 `--graph-compile-commands /absolute/path/compile_commands.json`。目录和源码路径必须映射到所选库副本；命令仅作为 Clang 参数读取，不能把数据库当作 shell 脚本执行。配置头文件需要与该数据库一致，用户提供配置时不会自动运行另一套 OpenSSL 配置覆盖它。

没有数据库时，为选中的 C 文件生成分析命令，提供项目根、include、crypto、crypto/bn 包含目录。OpenSSL 在独立副本执行 `perl Configure linux-x86_64 no-asm no-shared` 和 `make -j2 build_generated`，生成配置头及相关构建材料；这不是 QCP 源码适配或证明准备，也不代表其他平台和宏组合已覆盖。所选范围只有头文件时，上游可能对索引的 C 单元执行默认扫描，成本可能更高。

## 过程和范围

1. 复制所选库到输出目录 `graph-analysis/project/`，拒绝越出库根的源码符号链接；不写入 `input/`。
2. CodeGraph 对副本建索引，保留限定到文件/函数变体的 FQN，不能按裸函数名合并。
3. FM-Agent 从 Clang AST 提取直接调用边；成功覆盖的调用者优先使用这些边，其他调用者回退 CodeGraph；保留上游合成的函数指针 dispatch 边。
4. 同时运行 FM-Agent C 间接调用分析，将 flow/type 候选边加入图和 SCC。该分析按字段汇总、上下文不敏感、有迭代上限，并可能使用有错误的部分 AST，不能保证候选集合完整。
5. V2 选定文件内的 CodeGraph 函数进入目标；V1 保留显式函数集合。旧清单发现而 CodeGraph 未识别的定义仍保留并标记依赖未知。范围外的已知目标只记录为外部依赖，不自动扩大规约生成范围。
6. 原有 caller-first 调度、SCC、独立审核和阶段三交接继续使用同一图结构。索引之外的宏生成函数、条件配置、外部依赖和解析缺口不能据此认定不存在。

这里只复用静态依赖分析，不引入 FM-Agent 的阶段划分或模型规划流程。源码副本和配置文件是分析材料，不宣称与所有原始构建条件等价。正式证明仍须匹配经过审核的源文件和契约。

## 中间产物与诊断

`graph-analysis/` 保存：
- `project/.codegraph/codegraph.db`：原始索引。
- `project/compile_commands.json`：实际交给后端的编译数据库。
- `configure.log`、`generated.log`、`codegraph.log`、`backend.log`：执行记录。
- `raw-graph.json`：上游边、函数指针候选、函数索引、Clang 覆盖、每次解析结果及命令/退出码/stderr。
- `analysis.json`：固定版本、构建配置、分析边界和诊断路径。

最终 `graph.json` 的每条边保存 evidence 和调用点；`unknown_calls` 保留外部/未解析调用、间接候选的不完备性、上游未返回目标的间接调用点及未覆盖函数。图仍为 `unverified_reference_graph`。身份记录包含后端版本及用户编译数据库摘要；旧词法运行续跑须显式用 `--graph-backend lexical`。不要把旧图直接改成新图后续跑。

复用已有图使用 `--resume`。新的运行重新建副本和索引，当前没有跨运行缓存复用；磁盘成本应纳入运行目录管理。构图失败保留日志，不静默切回旧正则图。

## 验证

```sh
LST_RUN_GRAPH_TESTS=1 python3 -m unittest tests.test_fm_graph -v
python3 -m unittest tests.test_reference_specs tests.test_reference_review tests.test_reference_stage3 -q
```

真实后端测试覆盖宏调用、同名静态函数、重复调用点、函数指针候选、递归 SCC、条件实现、用户编译数据库及身份变更拒绝续跑、属性修饰定义、缺失头文件回退、未知调用和 prepare-only/resume。普通单元测试继续显式使用词法夹具，避免依赖外部安装；这不改变生产默认值。

## 2026-10-27 验证结果

- 环境安装脚本已在 Ubuntu-24.04 WSL 成功执行；Clang 18.1.3，固定 CodeGraph 与 FM-Agent 版本核对通过。
- 全套单元测试运行 321 项，通过（其中当时 2 项真实后端测试按默认配置跳过）。随后启用真实后端并加入编译数据库/未解析指针测试，相关 43 项测试全部通过。
- 最终 BN 模块验证目录：../runs/fm-agent-bn-module-graph-20261027-02。
- 选定范围内 363 个函数定义条目（包含条件/平台变体），979 条候选边，360 个 SCC；其中 316 个选定条目获成功 Clang AST 覆盖。
- 41 个 C 翻译单元中 39 个成功；两份 E2K 源文件分别缺 e2kbuiltin.h/e2kintrin.h，属于当前 x86-64 分析环境不覆盖的平台，保留 CodeGraph 回退和原始诊断。
- 上游返回 5 个带候选目标的间接调用点；另外记录 226 个上游未返回候选目标的原始调用点。后者为上游统计口径，不保证跨翻译单元去重，也不代表 226 个不同函数。
- 完整图保留 1929 条未知/范围外/条件及语法缺口记录。这些不是 1929 个已确认错误，也不能当作已解决依赖。
- 输入快照前后相同；状态为 planned，模型任务文件为 0。没有生成自然规约、启动模型实验或执行证明。
