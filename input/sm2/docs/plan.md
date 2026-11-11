# SM2 验证计划

验证范围：以默认生产构建中的 `sm2_keypair`、`sm2_get_public_key`、
`sm2_sign` 和 `sm2_verify` 为公开入口，验证其生产调用链。Milestone 1
保持既定分工，验证 `basicOp.c` 中生产可达的 18 个函数；Milestone 2 验证
调用链可达的 `fieldOp.c` 22 个函数。

编译配置：以 `make lib` 的默认配置为准，不启用 `MONG`，因此验证
`fieldOp.c` 的非 `MONG` 路径；测试代码和仅在其他编译选项下可达的分支不在
当前范围内。

## Milestone 1：`basicOp.c`

### 范围

- 验证 `bignumber/YCrypt/sm2/basicOp.c`。
- 20 个源码函数中有 18 个生产可达，各分配给一位同学，不重复分配。
- `u32_neg` 和 `u32_inc` 在默认生产调用链中不可达，不要求补充规格、符号执行
  或 VC 证明，也不计入 Milestone 1 的完成条件。
- 函数规格统一维护在 `docs/spec_contract.c`。
- 跨组调用只使用已经冻结的 contract，不等待其他同学完成 proof。

### 分工

#### 占月：进位加法与 u32 加减

- `portable_addcarryx_u64`
- `u32_neg`（生产不可达，不要求验证）
- `u32_add`
- `u32_inc`（生产不可达，不要求验证）
- `u32_sub`

#### 马旭：移位、比较与判等

- `u32_shl`
- `u32_shr`
- `u32_ge`
- `u32_gr`
- `u32_eq`
- `u32_eq_zero`
- `u32_eq_one`

#### 王瀚洋：P Montgomery 路径

- `raw_pow`
- `sm2p_mong_mul_core`
- `sm2p_mong_mul`
- `sm2p_mong_pow`

#### 王瑞涵：乘法与 N Montgomery 路径

- `portable_mulx_u64`
- `raw_mul`
- `sm2n_mong_mul_core`
- `sm2n_mong_mul`

### 公共 contract

并行验证前优先冻结以下跨组接口：

- `portable_addcarryx_u64`
- `portable_mulx_u64`
- `u32_add`
- `u32_ge`
- `raw_mul`

其中 `u32_add` 的 contract 必须覆盖 `result == a` 和 `result == b`
两种原地别名调用。

### 别名补充小结

按默认生产构建从四个公开 SM2 入口向下分析，M1 还需要补充以下 6 个
可复用的别名版本：

- `u32_add`：`r_eq_b`
- `raw_mul`：`a_eq_b`
- `sm2p_mong_mul`：`r_eq_x`、`r_eq_y`
- `sm2p_mong_pow`：`r_eq_x`
- `sm2n_mong_mul`：`r_eq_x`

### 完成标准

- 完成 `basicOp.c` 中 18 个生产可达函数的规格。
- 完成这 18 个函数的符号执行与 VC 证明。
- 汇总并检查这 18 个函数的公开 contract。

## Milestone 2：`fieldOp.c`

### 范围

验证默认生产调用链可达的 22 个函数。下列别名版本包括普通分离调用和
调用链向下传递后实际需要的精确同址调用；不包括复合别名和部分重叠。

### 分工

#### 占月：P/N 基础模运算

- `add_mod_p`：`non_alias`、`a_eq_b`、`r_eq_a`、`r_eq_b`
- `add_mod_n`：`non_alias`、`r_eq_b`
- `sub_mod_p`：`non_alias`、`r_eq_a`、`r_eq_b`
- `sub_mod_n`：`non_alias`、`r_eq_b`
- `mod_n`：`non_alias`、`in_place`
- `double_mod_p`：`non_alias`
- `mul_by_2_mod_p`：`non_alias`
- `mul_by_3_mod_p`：`non_alias`、`in_place`
- `div_by_2_mod_p`：`non_alias`、`in_place`
- `get_random_u32_in_mod_n`：单输出参数，无别名版本

#### 马旭：P Montgomery 逆元与域转换

- `MontgInvModp`：`non_alias`
- `inv_for_mul_mod_p`：`non_alias`
- `montg_mul_mod_p`：`non_alias`、`r_eq_a`、`r_eq_b`
- `montg_sqr_mod_p`：`non_alias`、`in_place`
- `montg_to_mod_p`：`non_alias`
- `montg_back_mod_p`：`non_alias`、`in_place`

#### 王瀚洋：P Solinas 乘法路径

- `solinas_reduce`：`non_alias`
- `pow_mod_p`：`non_alias`
- `mul_mod_p`：`non_alias`、`x_eq_y`、`r_eq_x`、`r_eq_y`

#### 王瑞涵：N Montgomery 乘法与逆元

- `MontgInvModn`：`non_alias`、`in_place`
  - 源码风险：Phase II 没有像 `MontgInvModp` 一样处理 `k == 256`，
    此时可能访问越界的 `t.v[4]`。冻结规格和开始证明前应先确认并修复。
- `inv_for_mul_mod_n`：`non_alias`、`in_place`
- `mul_mod_n`：`non_alias`

## Milestone 3：ECC 点表示与点运算（`ecc.c`、`ecc_montg.c`）

### 范围

验证默认生产调用链可达的 29 个点判定、坐标转换、倍点和点加函数。标量展开、
预计算和标量乘法留到下一 Milestone。SM3 和随机数接口使用 trusted spec，
不验证其实现。

### 分工

#### 王瀚洋：点判定、表示转换与混合点加

- `equ_to_AFPoint_one`：单输入只读
- `equ_to_JPoint_one`：单输入只读
- `is_on_curve`：单输入只读
- `affine_to_jacobian`：`non_alias`
- `jacobian_to_affine`：`non_alias`
- `AFPoint_neg`：`non_alias`
- `add_JPoint_and_AFPoint`：`non_alias`、`r_eq_point1`
- `montg_apoint_to_montg`：`non_alias`
- `montg_inv_mod_n_ex`：`non_alias`、`in_place`

#### 占月：普通与 Montgomery 倍点、普通点加

- `double_JPoint`：`non_alias`、`in_place`
- `add_JPoint`：`non_alias`、`r_eq_point1`
- `montg_double_jpoint`：`non_alias`、`in_place`
- `montg_double_jpoint_ex`：`non_alias`、`in_place`

#### 马旭：Montgomery 基础操作与表示转换

- `montg_equal_one`：单输入只读
- `bignum_is_equal`：`non_alias`
- `bignum_set_to_zero`：单输出参数
- `copy_bignum`：`non_alias`
- `montg_set_jpoint_to_zero`：单输出参数
- `montg_is_apoint_zero`：单输入只读
- `montg_is_jpoint_zero`：单输入只读
- `montg_jpoint_to_apoint`：`x_only`
- `montg_jpoint_to_apoint2`：`non_alias`
- `montg_apoint_to_jpoint2`：`non_alias`
- `montg_inv_mod_p_ex`：`non_alias`、`in_place`

这些函数的 contract 分层为：

- 四个裸 bignum helper 使用 `store_u256_limbs` base spec；字段接口只作为坐标
  转换 caller 的局部 derived tag；
- Jacobian 清零、Affine/Jacobian 判零使用 Montgomery 坐标 base spec，并提供
  `ECInfinity` 点层 derived spec；
- `montg_jpoint_to_apoint` 的 `x_only` base spec 输出普通横坐标，
  `point_x_only` 给出同一抽象点的仿射坐标 witness；
- `montg_jpoint_to_apoint2` 和 `montg_apoint_to_jpoint2` 使用坐标 base spec 与
  同一 `ec_point` 的完整点层 derived spec；
- `montg_inv_mod_p_ex` 保留 `non_alias`、`in_place` raw array base spec，字段语义
  由调用者局部派生。

#### 王瑞涵：Montgomery 点加

- `CopyJPoint`：`non_alias`、`in_place`；并从这两个坐标层 base tag 派生
  `mont_non_alias`、`mont_in_place`
- `montg_add_jpoint`：`non_alias`、`r_eq_a`、`r_eq_b`
- `montg_add_jpoint_and_apoint`：`non_alias`、`r_eq_a`
- `montg_add_jpoint_ex`：`non_alias`、`r_eq_a`
- `montg_add_jpoint_and_apoint_ex`：`non_alias`、`r_eq_a`

### 公共 contract

并行验证前冻结以下跨组接口：

- `equ_to_JPoint_one`
- `bignum_is_equal`
- `montg_is_apoint_zero`
- `montg_is_jpoint_zero`
- `montg_apoint_to_jpoint2`
- `montg_double_jpoint`：`non_alias`、`in_place`

两个 mixed-add 函数覆盖全部合法抽象点输入。实现必须显式处理两个有限输入同点和
互逆的分支；公开规格不要求有限输入点不同。

## Milestone 4：标量展开与标量乘法

### 范围

在 Milestone 3 点运算 contract 已冻结的基础上，验证默认生产调用链可达的
5 个 NAF、预计算和标量乘法函数。固定基点函数使用已检查的普通或 Montgomery
预计算表谓词；SM3 与随机数接口继续使用 trusted spec。

### 分工

#### 王瀚洋：普通表示固定基点乘法

- `ML_mul_basepoint`：`non_alias`

#### 占月：width-3 NAF 与动态预计算

- `get_naf_w3`：`non_alias`
- `montg_pre_compute_naf_w3`：`non_alias`

#### 马旭：任意点 Montgomery 标量乘法

- `montg_times_point_naf_w3`：`non_alias`

该函数的公开 contract 覆盖生产调用链的完整 `0 <= K < SM2_N_Z` 范围，并要求
输入公钥点不是 `ECInfinity`。其 NAF 循环调用完整语义的
`montg_add_jpoint_and_apoint_ex`；callee 对有限同点和互逆输入分别执行倍点和单位元
分支，因此 caller 不需要维护“两个有限输入点不同”的额外不变量。

#### 王瑞涵：固定基点 Montgomery 标量乘法

- `montg_times_base_point`：`non_alias`

### 公共 contract

并行验证前冻结以下跨组接口：

- `get_naf_w3`
- `montg_pre_compute_naf_w3`

## Milestone 5：SM2 协议与 SM3

M5 的协议谓词、执行边界、冻结 contract 和 strategy 组织统一见
[design.md](design.md)；完整函数规格以 [spec_contract.c](spec_contract.c) 为准。

### 分工

#### 王瀚洋：SM2 签名链

- `sm2_keypair`
- `sm2_get_public_key`
- `sm2_get_id_digest`
- `sm2_get_message_digest`
- `sm2_sign_dgst`
- `sm2_sign`

#### 王瑞涵：SM2 验签链

- `u1_to_u32`
- `str_reverse_in_place`
- `sm2_verify_dgst`
- `sm2_verify`

#### 马旭：SM3 压缩核心

- `sm3_compress`
- `sm3_init`

#### 占月：SM3 流式处理

- `sm3_update`
- `sm3_final`
- `sm3`

## 归档状态

当前 `main` 分支的正式 artifact 状态如下：

| 范围 | 已归档 C/VC case | 状态 |
| --- | ---: | --- |
| Milestone 1：`basicOp` | 18 | 完成 |
| Milestone 2：`fieldOp` | 22 | 完成 |
| Milestone 3：ECC 点运算 | 29 | 完成 |
| Milestone 4：标量乘 | 5 | 完成 |
| Milestone 5：`extra` 与 SM2 协议 | 10 | 完成 |
| Milestone 5：SM3 实现 | 5 | 完成 |

已完成 case 合计 89 个。
