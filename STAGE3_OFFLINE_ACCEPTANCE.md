# 阶段三离线验收

在仓库根目录运行，输出路径应尚未存在。

```bash
python3 -m stage3 \
  --stage2 runs/minimal-simplex-v2-20261118/stage2-link-evidence-clarified/stage2.json \
  --reference example/minimal-simplex/references/fme/Rocq/fme_gmp_lib.v \
  --fixture tests/fixtures/stage3-simplex-review.json \
  --output /tmp/library-spec-stage3-sol-20261118.json
python3 -m unittest discover -s tests -p test_stage3.py -v
```

阶段二输入导入 19 个 `conditional` 函数中的 60 条需求。此次落盘的原始需求是 `build` 第一条，ID 为 `fn-1307838fa0bae641e6f393a3:1:e54cc49140d2bb87`。需求文本、用途和阶段二证据坐标原样保留。通过全局 `call_id` 联接到 `solver.c:102:13` 的 `mpz_set` 复用调用，原检查为 `unknown`。同一函数到 `integers` 的三条内部调用检查均从被调侧联接得到 `compatible`。

扫描整个 FME 文件取得 50 条声明，其中 12 条识别到顶层空间蕴含。两个查询共有 `index.in_bounds`，拆分查完整数组到单槽加缺一项余部，重组交换两侧。查询未携带引理名。排序按两侧命中特征与额外前提评分，同分按源文件行号排序。

| 排名 | 拆分命中 | 分数 | 重组命中 | 分数 |
| --- | --- | ---: | --- | ---: |
| 1 | L80 `MpzArray.full_split_to_missing_i` | 12 | L70 `MpzArray.missing_i_merge_to_full` | 10 |
| 2 | L236 `mpz_coef_array_split` | 11 | L281 `mpz_coef_array_merge` | 9 |
| 3 | L54 `MpzArray.full_length` | 2 | L80 `MpzArray.full_split_to_missing_i` | 2 |
| 4 | L62 `MpzArray.full_Zlength` | 2 | L236 `mpz_coef_array_split` | 1 |
| 5 | L70 `MpzArray.missing_i_merge_to_full` | 2 | L54 `MpzArray.full_length` | 0 |

封装重组出现在拆分检索第 7，得分 1。封装拆分出现在重组检索第 4，得分 1。排名前两条各有对应该方向的目标资源。其余排名反映部分资源或相反方向的静态匹配。

固定审核替身读取两条封装声明的完整文本及摘要和行区间，报告同一个需求的拆分、重组用途，需求覆盖为 `partial`，两个用途各标记 `not_run`。待解决事项含 Simplex 到 FME 的节点和行表示、同值替换恢复原行、dummy 共享及清理、Arch32 历史契约到 LP64 的适配。测试逐行核对原文，拒绝未交付条目的引用，并验证改名后的封装、槽谓词和引理仍按方向检索。未知记号条目保留原文及空结构。

此次实测使用固定审核替身，未调用模型、Rocq 或 QCP。输入使用冻结阶段二文件中保存的阶段一绝对路径。单文件扫描支持有限的分离蕴含写法和数组谓词链，角色识别是检索线索。程序运行和测试均已完成。
