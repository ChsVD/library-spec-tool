# SM2 验证设计

## 1. 验证范围与保证

本仓库验证 YCrypt 默认生产构建中从以下四个公开入口可达的 SM2 实现：

- `sm2_keypair`
- `sm2_get_public_key`
- `sm2_sign`
- `sm2_verify`

“可达”指从这四个入口沿默认编译配置下的静态函数调用关系展开。测试函数和
只在其他预处理分支中出现的函数不计入范围。SM2 调用的 SM3 压缩、初始化、
流式更新、摘要输出和一次性摘要实现也在范围内。

验证版本和执行模型如下：

| 项目 | 采用的版本或配置 |
| --- | --- |
| QCP 与参考源码快照 | `qcp-binary-democases` `main` commit `126de54aacf08cd1caefe747383b7cfb3ab16a46` |
| 参考 C 文件 | 该快照中的 `YCrypt/sm2/` 和 `YCrypt/sm3/sm3.c` |
| Rocq/Coq proof checker | 8.20.1 |
| 字节序 | Makefile 向 QCP 传入 `--endian little` |
| 基本整数模型 | `u1` 为 8 位，`u4`/`uint32_t` 为 32 位，`u8`、`UINT64` 和 `size_t` 为 64 位 |

源码中的 `MONG` 宏只在 `fieldOp.c` 中选择 `pow_mod_p` 和 `mul_mod_p` 的两套实现。
默认配置未定义该宏，所以这两个函数验证 `raw_mul`/`raw_pow` 加 Solinas reduction
的分支。Montgomery core、域转换和 Montgomery ECC 函数独立编译，
并按默认调用链进入验证范围。

正式归档包含 89 个 C case：`basicOp` 18 个、`fieldOp` 22 个、`ecc` 17 个、
`ecc_montg` 17 个、`extra` 2 个、SM2 协议 8 个、SM3 5 个。每个 case 都由 QCP
在上述小端模型下执行符号执行并生成 VC；最终 goal check 组合自动证明、手工证明
和所加载 strategy 的 soundness proof。全部 89 个 goal check 均已编译通过；
manual proof、strategy proof 和正式库中没有 `Admitted`。前端生成的
`*_proof_auto.v` 按 QCP 规则单独管理，不计入手工 proof 完成度。

本文描述上述范围采用的验证设计。函数的逐项正式 contract 见
[spec_contract.c](spec_contract.c)，验证 C 相对参考实现的差异见
[source_changes.md](source_changes.md)，annotation、strategy、proof 和生成边界见
[verification_rules.md](verification_rules.md)，完成范围和函数分类见
[plan.md](plan.md)。

## 2. 从 C 内存到函数语义

QCP 首先把 C 对象表示成内存资源。以 `u32` 为例，前端生成的结构体谓词描述
对象中四个 64-bit limb 的存储位置和内容。此时得到的是字段级内存信息，还没有
把四个 limb 当作一个 256 位整数。

`store_u256(p,x)` 在这些字段资源上增加小端整数解释，表示地址 `p` 处的 `u32`
保存整数 `x`。`store_fp(p,x)` 和 `store_fn(p,x)` 进一步要求 `x` 分别位于 SM2 的
P 域和 N 标量范围内。算术函数的 contract 因而可以直接说明输入整数与输出整数
之间的模运算关系，而不必逐项描述四个 limb 如何变化。

其他 C 对象采用相同的方法解释：

- `store_bytes` 把字节数组解释为一个字节列表；
- `store_afpoint` 和 `store_jpoint` 把点结构体的坐标解释为一个抽象椭圆曲线点；
- `store_sm3_ctx` 把 `SM3_CTX` 的字段解释为已经吸收的消息；
- `store_sm2_private_key`、`store_sm2_public_key` 和 `store_sm2_signature` 分别解释
  协议使用的私钥、公钥和签名对象。

在这些表示之上，Rocq 数学定义给出算法应当计算的结果。整数函数使用模运算，
ECC 函数使用点加和标量乘，SM3 函数使用标准摘要函数，SM2 协议函数使用密钥、
签名生成和验签关系。连接定理证明 C 实现中的 limb 运算、坐标公式和位运算得到
这些数学结果。

函数 contract 最后把输入输出的内存谓词和数学结果写在一起。例如，
`sm2_verify` 的输入谓词说明内存中保存的公钥、消息和签名；摘要定义给出该消息的
SM3 摘要；返回值则说明该签名是否满足 SM2 验签关系。

第 3 节介绍共享的 C 内存和字节定义，第 4 至 7 节依次介绍整数算术、ECC、SM3
和 SM2 协议。第 8 节介绍函数规格、strategy 与 proof 的组织，第 9 节列出正式
库和验证文件。

## 3. 基础数据模型与可信边界

后续所有验证都建立在同一套 C 内存模型上。本节先说明前端为结构体生成的谓词，
再介绍共享的数组和字节谓词、字节编码，最后列出验证所依赖的 C 布局与外部接口。

### 3.1 前端生成的结构体谓词

QCP 前端为 C 结构体生成逻辑 record、已初始化谓词、未初始化谓词和结构体数组
实例。共享定义按 C 类型统一归档：

| C 类型 | 共享定义 | 生成谓词 |
| --- | --- | --- |
| `u32` | `u32_def.v` | `Recordu32`、`StructPredu32`、`UndefStructPredu32`、`Structu32Array` |
| `AFPoint`、`JPoint` | `ecc_point_def.v` | `RecordAFPoint`、`RecordJPoint`、对应 `StructPred*`、`UndefStructPred*` 和数组实例 |
| `SM2SIG`、`PrivKey` | `sm2_protocol_def.v` | 协议结构体的 record 与 `StructPred*` |
| `SM3_CTX` | `sm3_def.v` | 上下文 record、字段谓词和未初始化对象谓词 |

这些生成谓词只表达 C 对象形状和字段内容。整数值、曲线点、SM3 消息状态和
协议语义由各领域的表示谓词在其上建立。嵌套结构体统一导出共享定义，例如
`ecc_point_def.v` 复用 `u32_def.v`，所有相关 case 使用同一套 `u32` 逻辑定义。

### 3.2 内存单元、数组和字节资源

底层内存资源由 QCP 的 `data_at`、`UInt64Array`、`UIntArray`、`UCharArray` 和
生成的结构体谓词表示。字节和 32-bit word 的共享内存接口为：

```rocq
store_bytes address length bytes
store_byte_prefix address capacity bytes
store_u32_words address count words
```

`store_bytes` 拥有完整字节区域并携带长度和逐字节范围；
`store_bytes(address,0,nil)` 等价于 `emp`。`store_byte_prefix` 拥有完整容量，已初始化
前缀保存指定字节，其余后缀保持可写。`store_u32_words` 描述 32-bit word 列表。

三个谓词的纯条件和内存形状为：

```text
store_bytes(address,length,bytes):
  Zlength(bytes) = length，且每个字节位于 [0,256)

store_byte_prefix(address,capacity,bytes):
  0 <= Zlength(bytes) <= capacity，前缀保存 bytes，剩余后缀未初始化

store_u32_words(address,count,words):
  Zlength(words) = count，且每个 word 位于 [0,2^32)
```

typed integer 与 4/8/32 字节视图的连接集中在 `byte_memory.v`。普通数组元素地址
统一表示为：

```text
base + index * sizeof(type)
```

特定 typed 数组或零偏移 alias 在 QCP 内部可能产生更具体的地址项。这些地址项在
产生它们的具体函数验证中处理；通用 C annotation 仍使用上述统一的加法形式。

### 3.3 字节编码与位运算

`byte_encoding.v` 定义以 256 为基的字节值、大小端解释、固定宽度编码和 SM2
`ENTLA` 编码。`bitwise.v` 直接对 QCP 前端生成的 `unsigned_last_nbits`、
`Z.land`、`Z.lor`、`Z.lxor`、`Z.lnot`、`Z.shiftl` 和 `Z.shiftr` 证明范围、
掩码和组合性质。循环移位和 32-bit 字节交换分别由 `rotate_left` 和
`byte_swap32` 表示。

这些定义连接 C 整数与字节级标准语义，由 SM3 消息读写、SM2 大端整数转换和
协议编码共同使用；它们不定义额外的 C 内存资源。

### 3.4 C 布局、外部调用和可信边界

结构体字段资源和数组实例由 QCP 前端根据第 1 节列出的 C 类型生成。QCP 将部分
命名字段地址和 typedef 大小保留为抽象项，因此本验证另信任以下四条 C 布局事实：

| Rocq 公理 | 信任的 C 布局事实 |
| --- | --- |
| `u32_v_field_address_eq` | `u32` 对象地址等于首字段 `v` 的地址 |
| `sizeof_AFPoint_layout` | `sizeof(AFPoint) = 64` |
| `afpoint_x_field_address_eq` | `AFPoint` 对象地址等于首字段 `x` 的地址 |
| `sm3_block_count_address_eq` | `SM3_CTX.block + 56` 与 `SM3_CTX.nblocks + 64` 是同一地址 |

`u32_v_field_address_eq` 位于 `sm2_common_lib.v`，其余布局桥位于 `sm2_c_layout.v`。
`sizeof_AFPoint_matches_generated` 由 `sizeof_AFPoint_layout` 和前端生成的结构体
大小定义证明得到。上表四条公理只建立地址或大小等式，整数、ECC 和
SM3 的函数语义均由后续定理证明。

SM2 wrapper 中需要作为 `uint32_t *` 使用的局部字节数组通过验证专用接口
获取 `_Alignas(uint32_t)` 事实：

```c
void alignas_uint32_t(const void *address)
/*@ Require emp
    Ensure aligned_4(address) && emp
 */;
```

该接口只导出地址对齐，数组资源始终由 frame 保留。验证还使用以下外部函数
contract：

| 外部接口 | 本验证信任的语义 |
| --- | --- |
| `u32_rand` | 写入某个 `[0,2^256)` 内的 256 位整数；不假设具体概率分布 |
| `memcpy` | 复制实际调用指定的字节或 limb；规格分别覆盖 non-alias 和完全同址情况 |
| `memset` | 对实际调用的长度建立清零结果；一次性 `sm3` 的局部 context 调用只保留完整 shape |
| `printf` | 不改变验证拥有的内存；返回值未被使用 |
| `alignas_uint32_t` | 为紧随声明的局部数组地址提供 `aligned_4` |

完全同址复制选择 `memcpy` 和对应 caller 的 in-place tag；其他复制选择
non-alias tag。上述外部函数的 C 实现不在本仓库中验证。

验证结论还依赖 QCP 前端及其 C 语义、符号执行和 VC 生成的正确性，以及
Rocq kernel 和导入的 QCP、Coqprime、标准库证明。项目自己的正式库、manual proof
和 strategy soundness proof 均由 Rocq 检查；除表中的四条布局公理外，不含其他
未经证明的项目公理。具体 proof 规则见 [verification_rules.md](verification_rules.md)。

## 4. 整数、模运算与 Montgomery 设计

有了结构体和数组资源后，首先需要解释 SM2 大整数。本节从 limb 的整数值开始，
依次建立 P/N 范围谓词、Montgomery 表示和算术循环所需的数学关系。

### 4.1 Limb 与 `u32` 整数表示

验证头文件将源码类型名 `u8` 和 `UINT64` 定义为 64-bit 无符号整数，`u32` 由
四个 64-bit limb 组成。这里的 `u8`、`u32` 是 YCrypt 的历史类型名，不表示 8 位
或 32 位宽；一个 limb 就是 `u32.v` 数组中的一个 64-bit 元素。设
`U64_MOD = 2^64`、`U256_MOD = 2^256`，则四个 limb 按小端权重解释：

```text
u256_of_limbs(x0, x1, x2, x3)
  = x0 + x1 * 2^64 + x2 * 2^128 + x3 * 2^192
```

`store_u256_limbs(base,x)` 要求每个 limb 位于 `[0,2^64)`，并使加权和等于 `x`。
`store_u256(p,x)` 将它作用到 `u32.v` 字段，表示完整 `u32` 对象的整数值。

`store_u64_limbs(base,n,x)` 对应可变长 `UINT64[n]`：

```text
exists limbs,
  Zlength limbs = n /\
  u64_list_bounded limbs /\
  u64_list_value limbs = x /\
  UInt64Array.full base n limbs
```

固定四 limb 谓词直接对应 `u32.v`，可变长谓词用于 `raw_mul`、`raw_pow`、Montgomery
core 和九 limb `interim` 等真实数组状态。

### 4.2 P 域、N 标量与全局常量

SM2 使用两个 256 位素数：P 是曲线坐标域的模数，N 是标准基点的阶，也是标量和
签名 `R/S` 的模数。

```text
P = FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF
N = FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123
```

`store_mod(modulus,p,x)` 在 `store_u256` 上增加规范剩余范围：

```text
0 <= x < modulus && store_u256(p,x)
```

SM2 的两个实例为：

```text
store_fp(p,x) = store_mod(SM2_P_Z,p,x)
store_fn(p,x) = store_mod(SM2_N_Z,p,x)
```

`store_fp` 表示 P 域元素，`store_fn` 表示 N 上的规范标量。算术全局常量谓词把
静态 C 对象连接到 `SM2_P_Z`、`SM2_N_Z` 和对应 Montgomery 参数。验证只在函数
实际读取这些全局对象时展开相应谓词。

### 4.3 Montgomery 数学与表示

通用定义位于 `montgomery.v`：

```rocq
Montgomery.mont p R x := (x * R) mod p
```

SM2 使用 `R = 2^256`，并在 `sm2_common_lib.v` 中实例化：

```rocq
mont_p x := Montgomery.mont SM2_P_Z U256_MOD x
mont_n x := Montgomery.mont SM2_N_Z U256_MOD x
```

记 `R = U256_MOD = 2^256`。普通值 `a` 的 P Montgomery 数值为
`mont_p(a) = a * R mod P`，内存谓词写成 `store_fp(p,mont_p(a))`。N 上的
`mont_n` 含义相同，只把模数换成 N。

Montgomery 乘法的 base spec 直接描述内存中的输入数值。若输入对象保存 `X`、`Y`，
输出保存 `Z`，则存在整数 `K` 使：

```text
0 <= Z < P
Z * R = X * Y + K * P
```

`K` 只是说明约减前后相差 P 的整数倍，不进入后续接口；`0 <= Z < P` 选出唯一的
规范余数。当 `X = mont_p(a)` 且 `Y = mont_p(b)` 时，上式推出
`Z = mont_p(a*b)`。derived spec 正是把这一前提和结论写成表示层接口。N 模数和
Montgomery core 的 `T` 输入使用同一等式，其中右侧的 `X*Y` 换成八 limb 整数 `T`。
alias 和 non-alias 情况分别从各自的 base tag 派生。

P 和 N 上的乘法、平方、进入/退出 Montgomery 表示及逆元函数共享这一设计。
普通模加、模减、除二和小常数乘法的 base spec 给出模结果；需要继续使用
Montgomery 表示的上层函数选择对应的 `mont_*` derived tag。

### 4.4 算术 helper 与逆元

直接处理 `UINT64[4]` 的 bignum helper 以 `store_u256_limbs` 为 base 接口。需要将
结果继续作为域元素使用的 ECC 函数选择 helper 已证明的 field derived tag。这些
tag 只切换同一四-limb 对象的逻辑视图；纯裸整数比较保持 raw 接口。

逆元函数的 contract 要求输入 `A` 非零且位于 P 或 N 的规范范围。binary
almost-inverse 的第一阶段维护 `u`、`v`、`r`、`s`、计数器 `k` 和进位；退出时
`256 <= k <= 512`，并得到与 `2^k` 同余的缩放逆元。第二阶段使用
`2^(512-k)` 消除这部分缩放，最终输出 `Z` 满足：

```text
0 <= Z < modulus
A * Z = 2^256 + K * modulus
```

因此 `Z` 是 `A` 的逆元的 Montgomery 表示。`almost_inverse.v` 对模数参数化并
证明两阶段状态转换，`fieldOp_lib.v` 为 P 和 N 提供具体实例。`k = 256` 时第二阶段
无需 one-hot 乘数，验证实现直接返回第一阶段结果；这也避免构造数组下标 4。
零输入不属于逆元 contract，密钥和 nonce 生成函数在调用逆元前排除相应零值。

### 4.5 `raw_mul` 乘法循环

设两个输入分别为 `A = sum(ai * 2^(64*i))` 和
`B = sum(bj * 2^(64*j))`，其中 `0 <= i,j < 4`。`raw_mul` 按 `i+j` 从小到大累加
16 个 `ai*bj`。宏 `MUL_ACC(i,j)` 计算一个 64x64 乘积，将低位加到
`result[i+j]`，并把高位和进位加到 `result[i+j+1]`。

检查点位于 `i+j = 0,1,2,3` 四条对角线全部完成之后：

```text
raw_mul_prefix_3 = sum(ai * bj * 2^(64*(i+j)))，其中 i+j <= 3
```

后缀 `3` 表示已经处理的最高对角线编号。此时 `result[0..5]` 保存该前缀的六个
limb，`result[6..7]` 尚未初始化。随后处理 `i+j = 4,5,6`，并由
`raw_mul_prefix_3_to_6_conservation` 组合每次 `MUL_ACC` 的进位等式，证明最终
八个 limb 的值等于 `A*B`。alias 和 non-alias 分支共享这一定理。

## 5. ECC 验证设计

第 4 节已经给出了坐标字段的整数和 Montgomery 表示。本节先定义 SM2 曲线上的
抽象点和群运算，再说明 C 点结构体如何表示抽象点，最后给出点运算与标量乘的
函数语义。

### 5.1 Coqprime 曲线与群模型

SM2 使用素域 P 上的短 Weierstrass 曲线：

```text
y^2 = x^3 + A*x + B mod P

A  = FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC
B  = 28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93
Gx = 32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7
Gy = BC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0
```

P 和 N 的值见第 4.2 节。`sm2_curve_params.v` 保存这些参数，
`sm2_primality.v` 证明 P、N 的素性，`sm2_curve.v` 使用 Coqprime 建立有限域和
非奇异椭圆曲线群。Coqprime 是本项目采用的 Rocq 椭圆曲线群库。
`sm2_generator_order.v` 证明标准基点 `G=(Gx,Gy)` 的阶为 N。

Coqprime 素域元素通过项目接口访问：

```rocq
sm2_fe       : Set
sm2_fe_of_Z  : Z -> sm2_fe
sm2_fe_value : sm2_fe -> Z
```

`sm2_fe_of_Z` 取模后构造域元素，`sm2_fe_value` 返回规范整数代表。公共引理给出
范围、往返以及域运算与 `Z.modulo` 的对应关系。普通 VC 使用规范 `Z`，有限域
表示只在 ECC 语义连接定理中出现。

项目其余部分只使用以下抽象点接口；下面列出的是类型签名，Coqprime 实例参数由
`sm2_curve.v` 固定：

```text
ec_point        : Set
ECInfinity      : ec_point
sm2_point_add    : ec_point -> ec_point -> ec_point
sm2_point_double : ec_point -> ec_point
sm2_point_negate : ec_point -> ec_point
sm2_point_mul    : Z -> ec_point -> ec_point
```

`ec_point` 包含群单位元 `ECInfinity` 和携带曲线方程证明的有限点。群运算由
`SMain.add`、`SMain.opp` 和 `EGroup.gpow` 实现。项目对外导出单位元、逆元、交换律、
结合律、消去律和标量组合引理；`sm2_point_mul k P` 表示整数标量 `k` 对点 `P`
的群乘。验证具体 C 函数时直接使用这些接口，无需展开 Coqprime 内部实现。

### 5.2 C 点对象与坐标表示

`AFPoint` 含两个 `u32` 字段，`JPoint` 含三个 `u32` 字段。前端生成的 record
和数组谓词位于 `ecc_point_def.v`；ECC 表示谓词在其上按三层建立：

| 层次 | 谓词 | 含义 |
| --- | --- | --- |
| 精确字段 | `store_afpoint_fields`、`store_jpoint_fields` | 字段保存规范 P 域整数 |
| Montgomery 坐标 | `store_mont_afpoint_coords`、`store_mont_jpoint_coords` | 字段保存规范坐标的 `mont_p` 值 |
| 抽象点 | `store_afpoint`、`store_jpoint`、`store_mont_afpoint`、`store_mont_jpoint` | C 对象表示指定 `ec_point` |

坐标层只约束字段值和表示，适用于比较、清零和表示转换。抽象点层额外使用
`afpoint_represents` 或 `jpoint_represents` 连接到 `ec_point`，适用于点加、倍点和
标量乘。

仿射无穷远点在 C 中编码为 `(0,0)`。Jacobian 无穷远点由 `z = 0` 表示；
`JPoint_ZERO`、点清零函数以及采用 canonical contract 的点函数使用规范编码
`(1,1,0)`。`store_jpoint_with_canonical_infinity` 要求该编码，`store_jpoint`
允许任意坐标范围内的 `z = 0` 编码。

曲线系数 `SM2_a`、`SM2_b` 和规范 Jacobian 无穷远常量 `JPoint_ZERO` 使用 ECC
专用全局常量谓词。验证只在函数读取这些常量时展开相应谓词。

### 5.3 坐标与抽象点的语义连接

`afpoint_represents x y point` 将 `(0,0)` 连接到无穷远点，将其他规范坐标连接到
对应有限点。`jpoint_represents x y z point` 要求坐标在 P 域范围；对有限点：

```text
z <> 0
x = affine_x * z^2 mod SM2_P_Z
y = affine_y * z^3 mod SM2_P_Z
```

对无穷远点则要求 `z = 0`。`jpoint_canonical_infinity_encoding` 只额外限定无穷远编码为
`(1,1,0)`。表示引理给出坐标范围、坐标/点唯一性和
`point = ECInfinity <-> z = 0`。

`valid_afpoint x y` 表示曲线判定函数接受的 C 坐标编码：它接受代表无穷远点的
`(0,0)`，也接受 P 域内满足曲线方程的有限坐标。该性质与
`exists point, afpoint_represents x y point` 等价。它只说明坐标编码可以表示曲线点；
协议层的 `valid_sm2_public_key` 还要求该点由合法私钥乘标准基点得到。因此
`is_on_curve` 返回真不等于该输入已经满足协议公钥条件。

C 点操作的纯整数关系包括仿射/Jacobian 转换、倍点、完整点加和 mixed-add 公式。
`ec_math_refinement.v` 证明这些坐标关系的结果分别表示
`sm2_point_double point` 或 `sm2_point_add point1 point2`。证明覆盖左右无穷远、
互为逆元、同点倍点和不同有限点相加等分支。

这些定理的前提是 C 公式产生的整数坐标关系，结论是相应的抽象点运算结果。
点函数的验证先建立坐标关系，再应用这些定理得到 `sm2_point_add` 或
`sm2_point_double`，无需展开 `SMain.add` 的内部定义。

### 5.4 点运算 contract

ECC 公开 contract 根据函数语义选择最低且充分的谓词层：

| 函数类别 | 规格层次 |
| --- | --- |
| 坐标比较、清零、Montgomery 转换 | 精确字段或 Montgomery 坐标谓词 |
| `is_on_curve` | 返回值与 `valid_afpoint` 等价 |
| 仿射/Jacobian 转换 | 输入输出表示同一 `ec_point` |
| 取负、倍点和完整点加 | 输出函数式抽象点运算结果 |
| 普通 mixed-add | derived spec 输出 `store_jpoint`；需要规范无穷远编码时选择 canonical tag |
| Montgomery 完整点加与 mixed-add | 输出 `store_mont_jpoint(result,sm2_point_add(P,Q))` |
| 标量乘 | 输出 `sm2_point_mul scalar point` 或固定基点实例 |

`CopyJPoint` 的 base contract 处于精确字段层，non-alias 和完全同址 in-place 各有独立
tag；Montgomery derived tag 在其上保持同一抽象点。`montg_add_jpoint` 和
`montg_add_jpoint_and_apoint` 的公开结果直接使用 `sm2_point_add`。`aj_*`、
`maja_*` 和临时坐标只描述函数内部计算。

普通 `add_JPoint_and_AFPoint` 的不完整 mixed-add 公式可以产生非规范 `z = 0`
结果。base spec 用 `store_mixed_add_result_impl` 描述这些分支；derived spec 将其
转换为 `store_jpoint`，并在满足附加条件时转换为
`store_jpoint_with_canonical_infinity`。canonical 条件是：左输入为无穷远点、右输入
为无穷远点，或者两点之和不是无穷远点。公开接口使用后两种点谓词。

### 5.5 标量乘、WNAF 和预计算表

`ecc_scalar_mul.v` 定义 width-3 WNAF 数字、动态预计算表和标量乘组合引理。
`wnaf3_representation K digits` 的准确含义为：

```text
Zlength(digits) = 257
digits[i] in {-3,-1,0,1,3}
K = sum(digits[i] * 2^i)，0 <= i < 257
digits[i] != 0 时，范围内的 digits[i+1] 和 digits[i+2] 均为 0
```

digit 按最低有效位在前的顺序保存。C 数组类型是 `int8_t[257]`，逻辑中使用
`CharArray.full` 直接保存上述有符号整数值，不把负 digit 重新解释为无符号字节。
公共后缀引理给出从高下标向低下标执行倍点/加点循环所需的递推和非负性。

动态表 `PT[4]`、`NT[4]` 只使用槽位 1 和 3：`PT[1]=P`、`PT[3]=[3]P`，
`NT[1]=[-1]P`、`NT[3]=[-3]P`，四项均采用 Montgomery 仿射坐标；槽位 0 和 2
从不读取。`store_mont_wnaf3_precomp(PT,NT,P)` 精确拥有这四个有效表项。
`sm2_no_three_torsion.v` 证明非无穷远点 `P` 的 `[3]P` 仍为有限点，使槽位 3
可以使用 Montgomery 仿射点谓词。

固定基点表的 C 类型是 `AFPoint[4][8][256]`。前两个下标选出
`window = 8*limb + byte_in_limb`，第三个下标是 `byte_value`；对应记录表示：

```text
[byte_value * 256^window]G
```

因此四个 64-bit limb 的 32 个输入字节各选择一个基点倍数，点加后得到整个标量
乘结果。`sm2_ecc_const_table.v` 证明普通表和 Montgomery 表的全部 8192 个记录
满足该索引语义，`sm2_basepoint_mul.v` 组合表项、标量字节分解和群运算。

固定表的 C 三维数组在逻辑中扁平化为 `StructAFPointArray.full`。
`sizeof_AFPoint_matches_generated` 将 C 下标使用的 `sizeof(AFPoint)` 与生成数组的
元素步长对齐。验证一次表项访问时，从完整数组中取出当前索引对应的已证点；
点运算完成后再恢复完整数组。具体 record 和数组缺口只用于这一访问过程。

标量乘循环同时维护整数分解和抽象点累积不变式。数组索引、Montgomery 编码和
结构体复制在内存层处理；每次点运算完成后通过表证书或坐标正确性定理回到
`ec_point`。循环结束时统一得到 `sm2_point_mul`。

## 6. SM3 验证设计

SM3 使用第 3 节的字节和位运算定义。本节先给出标准 SM3 数学函数，再解释
`SM3_CTX` 如何保存流式消息状态，随后说明实现中的对齐条件和各公开函数的语义。

### 6.1 标准数学语义与 C 连接

`sm3.v` 按 SM3 标准在字节列表上定义：

- 8 个初始 chaining word；
- `FF`、`GG`、`P0`、`P1` 和逐轮常量；
- 16 个大端输入 word、68-word 消息扩展和 64 轮压缩；
- block chaining、`0x80`/零/64-bit bit-length padding；
- `sm3_digest_words` 和 32 字节大端结果 `sm3_digest_bytes`。

标准层对扩展表方程、round state 范围、block 拼接、padding 长度和摘要长度给出
纯数学定理。`sm3_c_bridge.v` 将 C 的预旋转 `Ti[64]`、`cpu_to_be32` 位运算项和
字节读取连接到这套标准语义。

### 6.2 `SM3_CTX` 流式状态

SM3 内存语义位于 `sm3_def.v`：

```rocq
store_sm3_ctx ctx message
store_sm3_ti
sm3_ctx_full_shape ctx
```

`store_sm3_ctx` 保存已吸收的 ghost 消息 `message`。digest 字段等于完整 block 的
压缩状态，`nblocks` 保存完整 block 数，`block` 保存不足 64 字节的尾段，
`num` 保存尾段长度。若 `full_len = 64 * (Zlength message / 64)`，则这四部分
精确表示为：

```text
digest  = sm3_compress_bytes(SM3_IV, message[0 .. full_len))
nblocks = full_len / 64
num     = Zlength message mod 64
block[0 .. num) = message[full_len .. Zlength message)
block[num .. 64) 未初始化且可写
```

`store_sm3_ctx` 还要求每个消息字节位于 `[0,256)` 且
`Zlength message < SM3_MAX_BYTES`。`store_sm3_ti` 将只读全局表连接到标准
逐轮常量。`sm3_ctx_full_shape` 表示 `sm3_final` 后上下文所有字段均已初始化，
但不再对其数值作语义承诺。

`SM3_MAX_BYTES = 2^61` 是 64-bit bit-length 字段允许的累计消息上界。多次调用
`sm3_update` 时，较早输入缓冲区的内存已经交还给调用方，但规格仍需记住此前
吸收的消息。ghost `Prefix` 保存这段逻辑历史，并与本次 `data_len` 共同满足
`Zlength Prefix + data_len < SM3_MAX_BYTES`。

### 6.3 32-bit 访问与对齐条件

SM3 C 实现通过 `uint32_t *` 读取 block、写入 digest，并访问 `ctx->block + 56`
的 length word。公开 contract 用条件谓词精确表达实际路径的对齐需求：

```text
sm3_compress_input_aligned(block,nblocks):
  nblocks = 0 or aligned_4(block)

sm3_digest_input_aligned(data,data_len):
  data_len < 64 or aligned_4(data)

sm3_update_data_aligned(data,data_len,buffered):
  buffered = 0 and (data_len < 64 or aligned_4(data))
  or
  0 < buffered < 64 and
    (data_len < 128-buffered or aligned_4(data + 64-buffered))
```

零 block、短输入或只写入内部 byte buffer 的路径不从外部输入做 32-bit
读取。已有尾段时，`sm3_update` 先填满内部 block，因此外部输入的首个
typed 读取地址是 `data + 64-buffered`。上述谓词只在该地址实际被读取时
要求 `aligned_4`。

上下文内部字段的对齐由生成的 typed 字段资源和第 3.4 节的
`sm3_block_count_address_eq` 导出。digest 输出使用 `uint32_t *` 写入，因此
`sm3_final` 和一次性 `sm3` 要求输出地址四字节对齐。SM2 wrapper 中作为这些
接口参数的局部字节数组由 `alignas_uint32_t` 提供同样的对齐事实。

### 6.4 SM3 函数语义

SM3 函数的公开 contract 统一使用标准字节语义和 `SM3_CTX` 状态：

| 函数 | 前置状态 | 返回后的语义 |
| --- | --- | --- |
| `sm3_compress` | 8-word chaining state、精确 `64*nblocks` 字节和条件对齐 | state 等于依次压缩这些 blocks 的结果；block 和 `Ti` 保持不变 |
| `sm3_init` | 未初始化的 `SM3_CTX` | `store_sm3_ctx(ctx,nil)` |
| `sm3_update` | `store_sm3_ctx(ctx,Prefix)`、本次 `Chunk`、累计长度上界和条件对齐 | `store_sm3_ctx(ctx,Prefix ++ Chunk)`；输入字节不变 |
| `sm3_final` | `store_sm3_ctx(ctx,Message)` 和对齐的 32-byte 未初始化输出 | 输出 `sm3_digest_bytes(Message)`；上下文变为 `sm3_ctx_full_shape` |
| `sm3` | 完整输入字节、条件输入对齐和对齐的 32-byte 输出 | 返回 32，输出 `sm3_digest_bytes(Message)`，输入不变 |

`sm3_update` 显式要求 `Zlength Prefix + data_len < 2^61`，使 64-bit bit-length
编码不溢出。`store_sm3_ctx` 使 `sm3_final` 自动拥有同一上界。一次性 `sm3`
没有单独重复该前置条件：`store_bytes` 已导出 `datalen <= 2^32`，因而调用
`sm3_update` 时必然满足 `datalen < 2^61`。

`sm3_final` 之后的 context 只保留完整已初始化的形状，不再满足
`store_sm3_ctx`，因此不能直接继续 `sm3_update`。一次性 `sm3` 随后对其
局部 context 执行 `memset`；该局部对象不出现在公开后置条件中。
各 contract 中由 `*` 连接的非空 context、输入和输出区域互不重叠。
零长输入的 `store_bytes` 为 `emp`，不产生读取、对齐或有效地址要求。

`sm3_update_lib.v` 提供字节前缀资源和批量 block 算术引理，`sm3_final_lib.v` 提供
padding、长度编码、digest word 写回和 final shape 引理。两个辅助库共同把 C
实现步骤连接到 `sm3.v` 定义的标准语义。

## 7. SM2 协议验证设计

SM2 协议把前面的 ECC 公钥运算和 SM3 摘要组合起来。本节依次定义密钥与签名
对象、ZA 和消息摘要、签名生成与验签关系，最后汇总协议函数的公开语义。

### 7.1 协议对象与密钥

`SM2SIG` 和 `PrivKey` 使用 `sm2_protocol_def.v` 中的前端生成谓词，`PubKey`
复用 `AFPoint` 表示。协议层在这些 C 对象上建立：

```rocq
store_sm2_private_key
store_sm2_public_key
store_sm2_signature
store_sm2_za
```

`store_sm2_private_key` 将 `PrivKey.da` 连接到规范 N 标量和私钥范围。
`store_sm2_public_key` 同时要求 `valid_sm2_public_key` 和对应的 `store_afpoint`。
`store_sm2_signature` 使用两个 `store_u256` 精确保存 `R/S`，从而覆盖 verifier 可以
接收的全部 256-bit 输入。`store_sm2_za` 表示 32-byte 输出等于指定
ID 和公钥的 `sm2_za_digest`。

私钥、密钥对和合法公钥的纯数学定义为：

```rocq
valid_sm2_private_key d := 1 <= d < SM2_N_Z - 1

valid_sm2_keypair d point :=
  valid_sm2_private_key d /\
  point = sm2_point_mul d SM2_G_POINT

valid_sm2_public_key point :=
  exists d, valid_sm2_keypair d point
```

### 7.2 ZA 与消息摘要

协议摘要由纯函数唯一确定：

```rocq
sm2_za_input id point
sm2_za_digest id point
sm2_message_digest id point message
```

`ENTLA` 是 `8 * Zlength ID` 的两字节大端编码。所有曲线整数和坐标都使用
32 字节大端编码，因而 ZA 的完整输入为：

```text
ENTLA || ID || A || B || Gx || Gy || Px || Py
```

`sm2_za_digest` 对该字节串应用标准 SM3。`sm2_message_digest` 则对
`ZA || message` 应用 SM3。`sm2_point_x` 和 `sm2_point_y` 给出有限抽象点的
规范坐标；它们在 `ECInfinity` 上的定义值均为 0。公开的 ID digest wrapper
支持 `id_len <= 50`；超过该长度时返回 `-1` 且不初始化输出区。

wrapper 中的对齐条件使用两个单一纯谓词表达：

```text
sm2_id_digest_output_aligned(result,id_len):
  id_len > 50 or aligned_4(result)

sm2_message_input_aligned(message,message_len):
  message_len < 96 or aligned_4(message)
```

它们分别表达 ID 过长时不写输出，以及先吸收 32-byte ZA 后是否会对外部 message
执行 typed word 读取，并通过引理连接到对应 SM3 函数的条件对齐要求。

### 7.3 签名生成与标准验签关系

签名生成和验签分别由两个纯关系表示：

```rocq
sm2_signature_generated e d r s
sm2_signature_verifies e point r s
```

`sm2_signature_generated e d r s` 的完整含义是：`d` 为合法私钥，并且
存在 `k,x,y,inverse`，满足：

```text
1 <= k < N
(x,y) represents [k]G
0 <= inverse < N
(1+d) * inverse mod N = 1
r = (e+x) mod N             and 1 <= r < N
(r+k) mod N != 0
s = (k-r*d) * inverse mod N and 1 <= s < N
```

`sm2_signature_verifies e P r s` 直接表达标准验签关系：

```text
1 <= r < N and 1 <= s < N
t = (r+s) mod N and t != 0
Result = [s]G + [t]P and Result != ECInfinity
Result has affine x-coordinate x and r = (e+x) mod N
```

公钥满足 `valid_sm2_public_key point` 时，两个关系由以下定理连接：

```rocq
valid_sm2_public_key point ->
  (sm2_signature_verifies e point r s <->
   exists d,
     valid_sm2_keypair d point /\
     sm2_signature_generated e d r s)
```

`sm2_sign` 的 base spec 说明输出签名满足指定私钥的 generated 关系。该
spec 不假设传入的公钥与私钥匹配；公钥用于计算 ZA。当两者满足
`valid_sm2_keypair` 时，`verifies` derived tag 同时给出该公钥下的验签关系。

`sm2_verify` 的 `verifies` spec 说明返回值与 verifies 关系等价。当输入使用
`store_sm2_public_key` 表示合法公钥时，`generated` derived tag 再用上述定理
将成功条件改写为“存在匹配私钥和 generated witness”。

### 7.4 协议与辅助函数 contract

| 函数 | 输入边界 | 返回和输出语义 |
| --- | --- | --- |
| `str_reverse_in_place` | 正长度字节串 | 原地变为 `rev bytes` |
| `u1_to_u32` | 精确 32 字节大端输入 | 写入数值等于该大端字节串的 `u32` |
| `sm2_get_public_key` | `store_sm2_private_key(privkey,D)` | 输出 `store_sm2_public_key(pubkey,[D]G)` |
| `sm2_keypair` | 未初始化的公钥和私钥对象 | 输出 `1 <= D <= N-2` 与匹配公钥 `[D]G` |
| `sm2_get_id_digest` | 任意 ID 字节和 `store_afpoint` 可表示的点编码 | `id_len <= 50` 时返回 0 并输出 ZA；否则返回 -1 且输出仍未初始化 |
| `sm2_get_message_digest` | 32-byte ZA 和消息 | 返回 0，输出 `SM3(ZA || Message)` |
| `sm2_sign_dgst` | 32-byte digest 和合法私钥 | 返回 1，输出满足 `sm2_signature_generated` 的 `R/S` |
| `sm2_sign` | `id_len <= 50`、合法协议公钥和合法私钥 | 返回 1，对 `SM3(ZA || Message)` 输出 generated 签名；匹配密钥对 tag 同时给出 verifies |
| `sm2_verify_dgst` | 非无穷远仿射点、任意 256-bit `R/S` 和 32-byte digest | 只返回 0 或 1；返回 1 当且仅当 `sm2_signature_verifies` |
| `sm2_verify` | `id_len <= 50`、非无穷远仿射点、任意 256-bit `R/S` | 只返回 0 或 1；对 `SM3(ZA || Message)` 返回标准验签结果 |

签名实现的循环在返回前排除 `k=0`、`r=0`、`(r+k) mod N=0` 和
`s=0`，并先将 `[k]G` 的横坐标约减到 N 域后计算 `r`。密钥生成排除
`D=0` 和 `D=N-1`。验签在 `[s]G+[t]P` 为无穷远点时返回 0，
不将其 C 编码 `(0,0)` 当作有效仿射横坐标。

`u32_rand` 的 contract 只提供范围内的存在值，因此密钥和 nonce 的规格不
声称均匀性或具体概率分布。对重复采样循环的证明是部分正确性：函数返回
时，输出满足上述范围和协议关系。

所有只读 ID、消息、digest、公钥和私钥资源都在后置条件中原样归还。
`store_sm2_*_globals` 系列谓词按每条调用链组合实际读取的只读全局资源。

## 8. QCP 规格、Strategy 与证明架构

第 3 至 7 节定义了 C 对象和对应的数学结果。本节说明这些定义如何写入函数规格，
以及 strategy 和 Rocq proof 如何共同完成 QCP 生成的 VC。

### 8.1 函数规格和符号状态

公开 spec 描述输入值、输出值、内存所有权和实际使用的全局常量。base spec
直接描述 C 实现的整数或坐标结果；derived spec 将同一结果提升为 Montgomery、
抽象点或协议语义。每个 derived spec 都表达函数本身的稳定语义。

同一函数支持多种 alias 情况时，使用 `non_alias`、`in_place`、`r_eq_a`、`r_eq_b`
等独立 tag 分别描述。调用另一个函数时，annotation 通过 `where(tag)` 选择该函数
对应的规格。循环 invariant 保存当前内存、已处理与未处理区间、数值范围以及
循环状态和最终结果的数学关系。full assertion 合并分支结束后的共同状态，
`Given` 引入后续语句需要的存在量。

普通符号状态优先保留 `store_fp`、字段谓词、坐标关系、`store_sm3_ctx` 和协议
对象谓词。实现 trace、临时坐标和数组缺口只在相应函数内部存活。

### 8.2 Strategy 分层

Strategy 负责反复出现的谓词转换和数组访问。所有 strategy 按责任分组：

| 层次 | Strategy | 职责 |
| --- | --- | --- |
| 通用表示与数组 | `sm2_representation`、`array_bridges`、`byte_memory_views`、`byte_pointer_views`、`u32_alias` | 整数/域/数组/字节视图转换与精确同址处理 |
| 算术 case | `basicop_facts`、`raw_mul_arrays`、`raw_pow_arrays` | 导出纯算术事实并管理部分初始化数组 |
| ECC 共享 | `sm2_constants`、`ecc_constants`、`ecc_representation`、`ecc_point_facts`、`ecc_point_overwrite`、`ecc_point_copy_steps`、`ecc_montg_helper_views` | 常量、点表示、纯事实、完整覆盖写入和 helper 视图 |
| 标量乘 | `basepoint_table_points`、`basepoint_bytes`、`wnaf3_precomp_points`、`wnaf3_predicate_cancellation` | 固定/动态预计算表、标量字节和 WNAF 资源 |
| SM3 与协议 | `sm3_word_views`、`sm3_ctx_views`、`sm3_streaming_memory_views`、`sm2_protocol_views`、`sm2_za_buffers` | typed word、流式上下文、协议对象和 ZA 字节区间 |
| 普通点运算 trace | `add_JPoint_trace`、`add_JPoint_boundary`、`jpoint_double_trace` | 归一化普通点加/倍点 trace 并在结果边界物化字段 |
| Montgomery 完整点加 | `montg_add_jpoint_precompute`、`montg_add_jpoint_x`、`montg_add_jpoint_y`、`montg_add_jpoint_z`、`montg_add_jpoint_compare`、`montg_add_jpoint_result`、`montg_add_jpoint_cleanup` | 预计算、X/Y/Z、比较、抽象结果和局部资源回收 |
| Montgomery mixed-add | `montg_add_jpoint_and_apoint_precompute`、`montg_add_jpoint_and_apoint_x`、`montg_add_jpoint_and_apoint_y`、`montg_add_jpoint_and_apoint_compare`、`montg_add_jpoint_and_apoint_result`、`montg_add_jpoint_and_apoint_cleanup` | mixed-add 五类分支的局部 trace、结果和回收 |

`montg_times_point_naf_w3` 的动态表访问是一个具体例子。循环 invariant
保留聚合资源 `store_mont_wnaf3_precomp(PT,NT,P)`。当 digit 为正数时，
`wnaf3_focus_positive` 只取出 `PT[digit]` 的 `store_mont_afpoint`，并保留
其余表资源；点加 callee 返回后，`wnaf3_restore_positive` 恢复完整聚合谓词。
负 digit 对 `NT[-digit]` 使用对称的 focus/restore 规则。因此表的 record 和
数组缺口只在一次调用周围出现，循环其余部分始终使用点级谓词。

谓词转换的总体方向为：

```text
data_at / generated arrays
  <-> limb / byte / word views
  <-> integer / field / coordinate predicates
  <-> point / SM3 context / protocol predicates
```

### 8.3 `core`、命名 scope 和按需 load

`core` rule 只用于跨函数稳定复用、方向唯一、不引入展开/折叠循环的转换。聚合
资源的主动展开、常量物化、结构体 record 物化和 case trace 使用命名 priority，
由 annotation 通过 `do rule_name` 或 `which implies ... by rule_name` 显式触发。

每个 C case 只加载自身 contract、内部状态或显式 `do/by` scope 需要的 strategy。
一个函数加载的 strategy 不会自动传递给调用它的函数。这样可以保持上层状态
抽象，并避免无关 `core` 扩大匹配空间。

point-add trace strategy 按 precompute、坐标、compare、result 和 cleanup 拆分；裸 limb 只在
compare scope 打开，抽象点结论只在 result scope 建立，局部资源只在 cleanup scope
回收。固定表和 WNAF 数组的 strategy 也保持表项聚焦/恢复边界，不把 record 缺口
传播到其他 ECC 函数。

### 8.4 Proof 组成

每个 case 的最终检查由四类验证文件组成：

```text
symbolic-execution goal
  + generated auto proof
  + manual proof body
  + loaded strategy soundness proofs
  -> goal check
```

manual proof 处理前端和 strategy 未自动关闭的 VC。跨多个 VC 复用的数学引理和 proof
tactic 位于正式 lib，不写入生成文件 prelude。strategy proof 只证明该 strategy 规则本身
的 separation-logic obligation。具体 tactic 风格、禁用项、编译时间阈值和生成文件
编辑边界统一由 [verification_rules.md](verification_rules.md) 规定。

## 9. 库与验证文件组织

最后，本节把前述定义、定理、strategy 和函数验证对应到仓库中的正式文件。

### 9.1 Rocq 库依赖

正式库按语义依赖分组：

| 分组 | 文件 | 职责 |
| --- | --- | --- |
| 生成结构体与布局 | `u32_def.v`、`ecc_point_def.v`、`sm2_protocol_def.v`、`sm2_c_layout.v` | C record、Struct/array 谓词和布局桥 |
| 通用数学与内存 | `limb_arithmetic.v`、`byte_encoding.v`、`byte_memory.v`、`bitwise.v`、`montgomery.v` | limb、字节、typed view、位运算和 Montgomery 通用定义 |
| SM2 算术 | `sm2_common_lib.v`、`almost_inverse.v`、`basicOp_lib.v`、`fieldOp_lib.v` | SM2 实例、基础算术和域运算引理 |
| ECC 数学与表示 | `sm2_curve_params.v`、`sm2_primality.v`、`sm2_curve.v`、`sm2_generator_order.v`、`sm2_no_three_torsion.v`、`ecc.v`、`ec_math_refinement.v` | 曲线、群、坐标表示和坐标公式语义 |
| ECC case 与标量乘 | `add_JPoint_and_AFPoint_lib.v`、`add_JPoint_lib.v`、`montg_add_jpoint_lib.v`、`montg_add_jpoint_and_apoint_lib.v`、`ecc_scalar_mul.v`、`sm2_ecc_const_table.v`、`sm2_basepoint_mul.v` | 点运算 trace、WNAF、固定表证书和标量乘组合引理 |
| SM3 与协议 | `sm3.v`、`sm3_c_bridge.v`、`sm3_def.v`、`sm3_update_lib.v`、`sm3_final_lib.v`、`sm2_protocol.v` | SM3 标准语义、上下文、streaming 引理和 SM2 协议关系 |

依赖方向从生成结构体和通用定义出发，再建立 SM2 整数、点、SM3 状态和
协议语义，最后由 case lib 引入具体函数的 trace 和组合引理。通用库和共享
表示库不导入 case lib。

### 9.2 目录布局

归档仓库中，验证 C 按 YCrypt 源码模块组织，每个目标函数使用一个
独立标注 C 文件：

```text
annotated_C/
  include/          C 类型、公共 contract 和 trace 接口
  basicOp/          基础大数运算
  fieldOp/          P/N 域与 Montgomery 运算
  ecc/              普通 ECC 与固定基点函数
  ecc_montg/        Montgomery ECC 与任意点标量乘
  extra/            字节/整数协议 helper
  sm2/              SM2 协议函数
  sm3/              SM3 实现
  strategy/         strategy source

rocq/
  Makefile
  lib/              正式数学、表示和 case lib
  strategy/         strategy goal/proof/goal-check
  vc/               按 C 模块归档的 case 验证文件
```

在 QCP 工作树中运行时，`annotated_C/` 同步到
`QCP_examples/Applications_human/sm2/`，`rocq/` 同步到
`Rocq/examples/Applications_human/sm2/`。

### 9.3 生成与验收

每个 case 生成：

```text
<function>_goal.v
<function>_proof_auto.v
<function>_proof_manual.v
<function>_goal_check.v
```

需要结构体定义的 case 额外生成 `<function>_def.v`，并导出对应共享结构体文件。
每份 strategy 对应 strategy goal、soundness proof 和 goal check。

`rocq/Makefile` 在部署后即为 `Rocq/examples/Applications_human/sm2/Makefile`，
统一执行库、strategy check 和全部 case goal check。
`test/spec_check.py` 检查正式函数签名、base/derived contract，以及调用点保存的
被调函数 contract 副本。
本文第 1 节范围内的验证文件均已通过这两类验收。仓库部署方法见
[README](../README.md)，逐函数清单见 [plan.md](plan.md)。
