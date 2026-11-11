CURRENT_DIR := .
SL_DIR := ../../..
REPO_ROOT := ../../../..
CASE_DIR := examples/Applications_human/sm2
C_CASE_DIR := QCP_examples/Applications_human/sm2
FORMAL_REPO_DIR := Rocq/$(CASE_DIR)
LOGIC_ROOT := SimpleC.EE.Applications_human.sm2
VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.basicOp
FIELDOP_VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.fieldOp
ECC_VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.ecc
ECC_MONTG_VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.ecc_montg
SM2_PROTOCOL_VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.sm2
SM3_VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.sm3
EXTRA_VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.extra
EXPERIMENT_VC_LOGIC_ROOT := $(LOGIC_ROOT).vc.experiments
STRATEGY_LOGIC_ROOT := $(LOGIC_ROOT).strategy

COQBIN ?=
SUF ?=
COQC := $(COQBIN)coqc$(SUF)
SYMEXEC ?= linux-binary/symexec
SYMEXEC_GEN_FLAGS ?= --gen-and-backup
STRATEGY_CHECK ?= linux-binary/StrategyCheck
STRATEGY_GEN_FLAGS ?= --gen-and-backup
SM2_STRATEGY_NAMES := sm2_representation array_bridges sm2_constants basicop_facts u32_alias
SM2_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(SM2_STRATEGY_NAMES)))
SM2_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(SM2_STRATEGY_NAMES)))
ECC_STRATEGY_NAMES := ecc_representation ecc_constants
ECC_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(ECC_STRATEGY_NAMES)))
ECC_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(ECC_STRATEGY_NAMES)))
ECC_AUX_STRATEGY_NAMES := ecc_point_overwrite ecc_point_facts
ECC_AUX_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(ECC_AUX_STRATEGY_NAMES)))
ECC_AUX_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(ECC_AUX_STRATEGY_NAMES)))
ECC_HELPER_STRATEGY_NAMES := ecc_montg_helper_views ecc_point_copy_steps jpoint_double_trace \
	basepoint_bytes basepoint_table_points wnaf3_precomp_points \
	wnaf3_predicate_cancellation
ECC_HELPER_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(ECC_HELPER_STRATEGY_NAMES)))
ECC_HELPER_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(ECC_HELPER_STRATEGY_NAMES)))
ADD_JPOINT_STRATEGY_NAMES := add_JPoint_boundary add_JPoint_trace
ADD_JPOINT_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(ADD_JPOINT_STRATEGY_NAMES)))
ADD_JPOINT_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(ADD_JPOINT_STRATEGY_NAMES)))
MONTG_ADD_JPOINT_STRATEGY_NAMES := \
	montg_add_jpoint_precompute \
	montg_add_jpoint_x \
	montg_add_jpoint_y \
	montg_add_jpoint_z \
	montg_add_jpoint_compare \
	montg_add_jpoint_cleanup \
	montg_add_jpoint_result
MONTG_ADD_JPOINT_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(MONTG_ADD_JPOINT_STRATEGY_NAMES)))
MONTG_ADD_JPOINT_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(MONTG_ADD_JPOINT_STRATEGY_NAMES)))
MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_NAMES := \
	montg_add_jpoint_and_apoint_precompute \
	montg_add_jpoint_and_apoint_x \
	montg_add_jpoint_and_apoint_y \
	montg_add_jpoint_and_apoint_compare \
	montg_add_jpoint_and_apoint_result \
	montg_add_jpoint_and_apoint_cleanup
MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_NAMES)))
MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_NAMES)))
RAW_STRATEGY_NAMES := raw_mul_arrays raw_pow_arrays
RAW_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(RAW_STRATEGY_NAMES)))
RAW_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(RAW_STRATEGY_NAMES)))
M5_STRATEGY_NAMES := byte_memory_views byte_pointer_views sm3_word_views sm3_ctx_views \
	sm2_protocol_views sm2_za_buffers
M5_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(M5_STRATEGY_NAMES)))
M5_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(M5_STRATEGY_NAMES)))
SM3_STREAM_STRATEGY_NAMES := sm3_streaming_memory_views
SM3_STREAM_STRATEGY_PROOFS := $(addprefix strategy/,$(addsuffix _strategy_proof.vo,$(SM3_STREAM_STRATEGY_NAMES)))
SM3_STREAM_STRATEGY_CHECKS := $(addprefix strategy/,$(addsuffix _strategy_goal_check.vo,$(SM3_STREAM_STRATEGY_NAMES)))
ALL_STRATEGY_NAMES := $(SM2_STRATEGY_NAMES) $(ECC_STRATEGY_NAMES) \
	$(ECC_AUX_STRATEGY_NAMES) $(ECC_HELPER_STRATEGY_NAMES) \
	$(ADD_JPOINT_STRATEGY_NAMES) $(MONTG_ADD_JPOINT_STRATEGY_NAMES) \
	$(MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_NAMES) \
	$(RAW_STRATEGY_NAMES) $(M5_STRATEGY_NAMES) $(SM3_STREAM_STRATEGY_NAMES)
BASICOP_CASES := \
	portable_addcarryx_u64 portable_mulx_u64 \
	raw_mul raw_pow \
	sm2n_mong_mul sm2n_mong_mul_core \
	sm2p_mong_mul sm2p_mong_mul_core sm2p_mong_pow \
	u32_add u32_eq u32_eq_one u32_eq_zero u32_ge u32_gr \
	u32_shl u32_shr u32_sub
FIELDOP_CASES := \
	MontgInvModn MontgInvModp \
	add_mod_n add_mod_p div_by_2_mod_p double_mod_p \
	get_random_u32_in_mod_n \
	inv_for_mul_mod_n inv_for_mul_mod_p mod_n \
	montg_back_mod_p montg_mul_mod_p montg_sqr_mod_p montg_to_mod_p \
	mul_by_2_mod_p mul_by_3_mod_p mul_mod_n mul_mod_p pow_mod_p \
	solinas_reduce sub_mod_n sub_mod_p
M3_ECC_CASES := \
	equ_to_AFPoint_one equ_to_JPoint_one is_on_curve affine_to_jacobian \
	jacobian_to_affine AFPoint_neg add_JPoint_and_AFPoint \
	montg_apoint_to_montg montg_inv_mod_n_ex \
	double_JPoint add_JPoint montg_double_jpoint montg_double_jpoint_ex \
	CopyJPoint
M4_FIXED_BASE_CASES := ML_mul_basepoint montg_times_base_point
M4_WNAF_ECC_CASES := get_naf_w3
M4_WNAF_ECC_MONTG_CASES := montg_pre_compute_naf_w3 montg_times_point_naf_w3
ECC_CASES := $(M3_ECC_CASES) $(M4_FIXED_BASE_CASES) $(M4_WNAF_ECC_CASES)
M3_ECC_MONTG_CASES := \
	bignum_is_equal bignum_set_to_zero copy_bignum \
	montg_equal_one montg_inv_mod_p_ex \
	montg_is_apoint_zero montg_is_jpoint_zero \
	montg_apoint_to_jpoint2 montg_jpoint_to_apoint \
	montg_jpoint_to_apoint2 montg_set_jpoint_to_zero \
	montg_add_jpoint montg_add_jpoint_and_apoint \
	montg_add_jpoint_ex montg_add_jpoint_and_apoint_ex
ECC_MONTG_CASES := $(M3_ECC_MONTG_CASES) $(M4_WNAF_ECC_MONTG_CASES)
BASICOP_GENERATE_TARGETS := $(addprefix generate-basicop-,$(BASICOP_CASES))
FIELDOP_GENERATE_TARGETS := $(addprefix generate-fieldop-,$(FIELDOP_CASES))
ECC_GENERATE_TARGETS := $(addprefix generate-ecc-,$(ECC_CASES))
ECC_MONTG_GENERATE_TARGETS := $(addprefix generate-ecc-montg-,$(ECC_MONTG_CASES))
BASICOP_CHECKS := $(addprefix vc/basicOp/,$(addsuffix _goal_check.vo,$(BASICOP_CASES)))
FIELDOP_CHECKS := $(addprefix vc/fieldOp/,$(addsuffix _goal_check.vo,$(FIELDOP_CASES)))
ECC_CHECKS := $(addprefix vc/ecc/,$(addsuffix _goal_check.vo,$(ECC_CASES)))
M2_FIELDOP_CASES := $(FIELDOP_CASES)
M2_FIELDOP_CHECKS := $(addprefix vc/fieldOp/,$(addsuffix _goal_check.vo,$(M2_FIELDOP_CASES)))
M3_ECC_CHECKS := $(addprefix vc/ecc/,$(addsuffix _goal_check.vo,$(M3_ECC_CASES)))
M3_ECC_MONTG_CHECKS := $(addprefix vc/ecc_montg/,$(addsuffix _goal_check.vo,$(M3_ECC_MONTG_CASES)))
ECC_MONTG_CHECKS := $(addprefix vc/ecc_montg/,$(addsuffix _goal_check.vo,$(ECC_MONTG_CASES)))
M4_FIXED_BASE_CHECKS := $(addprefix vc/ecc/,$(addsuffix _goal_check.vo,$(M4_FIXED_BASE_CASES)))
M4_WNAF_CHECKS := \
	$(addprefix vc/ecc/,$(addsuffix _goal_check.vo,$(M4_WNAF_ECC_CASES))) \
	$(addprefix vc/ecc_montg/,$(addsuffix _goal_check.vo,$(M4_WNAF_ECC_MONTG_CASES)))
M5_SM2_SIGN_CASES := \
	sm2_get_public_key sm2_keypair \
	sm2_get_id_digest sm2_get_message_digest \
	sm2_sign_dgst sm2_sign
M5_SM2_SIGN_CHECKS := \
	$(addprefix vc/sm2/,$(addsuffix _goal_check.vo,$(M5_SM2_SIGN_CASES)))
M5_EXTRA_CASES := str_reverse_in_place u1_to_u32
M5_EXTRA_CHECKS := \
	$(addprefix vc/extra/,$(addsuffix _goal_check.vo,$(M5_EXTRA_CASES)))
M5_SM2_VERIFY_CASES := sm2_verify_dgst sm2_verify
M5_SM2_VERIFY_CHECKS := \
	$(addprefix vc/sm2/,$(addsuffix _goal_check.vo,$(M5_SM2_VERIFY_CASES)))
SM3_CORE_CASES := sm3_compress sm3_init
SM3_STREAM_CASES := sm3_update sm3_final sm3
SM3_CASES := $(SM3_CORE_CASES) $(SM3_STREAM_CASES)
SM3_CHECKS := \
	$(addprefix vc/sm3/,$(addsuffix _goal_check.vo,$(SM3_CASES)))
SM3_STREAM_CHECKS := \
	$(addprefix vc/sm3/,$(addsuffix _goal_check.vo,$(SM3_STREAM_CASES)))
QCP_MEMORY_LIMIT_BYTES ?= 8589934592
QCP_MEMORY_GUARD := \
	prlimit --as=$(QCP_MEMORY_LIMIT_BYTES):$(QCP_MEMORY_LIMIT_BYTES) --
QCP_EXPERIMENT_ARGS ?=
QCP_EXEC_INFO_FLAG ?= --no-exec-info

COQ_FLAG := \
	-R flocq/src Flocq \
	-R SeparationLogic SimpleC.SL \
	-R unifysl Logic \
	-R sets SetsClass \
	-R compcert_lib compcert.lib \
	-R auxlibs AUXLib \
	-R examples SimpleC.EE \
	-R stdlib SimpleC.StdLib \
	-R StrategyLib SimpleC.StrategyLib \
	-R Common SimpleC.Common \
	-R fixedpoints FP \
	-R MonadLib MonadLib \
	-R listlib ListLib \
	-R MaxMinLib MaxMinLib \
	-R GraphLib GraphLib \
	-R SumLib SumLib \
	-R tracelib TraceLib \
	-R coq-record-update/src RecordUpdate \
	-Q algorithms Algorithms

QCP_ARGS := \
	--endian little \
	$(QCP_EXEC_INFO_FLAG) \
	-IQCP_examples/Applications_human/ \
	-I$(C_CASE_DIR)/include/ \
	-slp QCP_examples/Applications_human/ SimpleC.EE.Applications_human \
	-slp $(C_CASE_DIR)/ $(LOGIC_ROOT) \
	-slp $(C_CASE_DIR)/strategy/ $(STRATEGY_LOGIC_ROOT) \
	$(QCP_EXPERIMENT_ARGS)

.PRECIOUS: \
	strategy/%_strategy_goal.vo \
	strategy/%_strategy_proof.vo \
	vc/basicOp/%_goal.vo \
	vc/basicOp/%_proof_auto.vo \
	vc/basicOp/%_proof_manual.vo \
	vc/experiments/%_def.vo \
	vc/experiments/%_goal.vo \
	vc/fieldOp/%_def.vo \
	vc/fieldOp/%_goal.vo \
	vc/fieldOp/%_proof_auto.vo \
	vc/fieldOp/%_proof_manual.vo \
	vc/ecc/%_def.vo \
	vc/ecc/%_goal.vo \
	vc/ecc/%_proof_auto.vo \
	vc/ecc/%_proof_manual.vo \
	vc/sm2/%_def.vo \
	vc/sm2/%_goal.vo \
	vc/sm2/%_proof_auto.vo \
	vc/sm2/%_proof_manual.vo \
	vc/sm3/%_goal.vo \
	vc/sm3/%_proof_auto.vo \
	vc/sm3/%_proof_manual.vo \
	vc/ecc_montg/%_def.vo \
	vc/ecc_montg/%_goal.vo \
	vc/ecc_montg/%_proof_auto.vo \
	vc/ecc_montg/%_proof_manual.vo \
	vc/extra/%_def.vo \
	vc/extra/%_goal.vo \
	vc/extra/%_proof_auto.vo \
	vc/extra/%_proof_manual.vo

.PHONY: \
	generate refresh refresh-cases refresh-cases-after-raw-mul refresh-fieldop-after-div \
	generate-solinas generate-sm2-strategy \
	generate-solinas-case generate-solinas-minus-probe generate-ecc-% generate-ecc-montg-% generate-extra-% generate-sm2-protocol-% generate-sm3-% \
	solinas-libs solinas-strategy solinas-goal solinas-check
generate: generate-sm2-strategy
	mkdir -p vc/basicOp
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/basicOp/u32_shl_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/basicOp/u32_shl_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/basicOp/u32_shl_proof_manual.v \
		--coq-logic-path=$(VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/basicOp/u32_shl.c

generate-solinas: generate-sm2-strategy
	$(MAKE) generate-solinas-case

refresh:
	$(MAKE) -j1 generate-sm2-strategy
	$(MAKE) -j1 $(BASICOP_GENERATE_TARGETS) $(FIELDOP_GENERATE_TARGETS)

refresh-cases:
	$(MAKE) -j1 $(BASICOP_GENERATE_TARGETS) $(FIELDOP_GENERATE_TARGETS) \
		$(ECC_GENERATE_TARGETS) $(ECC_MONTG_GENERATE_TARGETS)

refresh-cases-after-raw-mul:
	$(MAKE) -j1 \
		$(filter-out generate-basicop-portable_addcarryx_u64 \
			generate-basicop-portable_mulx_u64 \
			generate-basicop-raw_mul,$(BASICOP_GENERATE_TARGETS)) \
		$(FIELDOP_GENERATE_TARGETS)

refresh-fieldop-after-div:
	$(MAKE) -j1 \
		$(filter-out generate-fieldop-MontgInvModn \
			generate-fieldop-MontgInvModp \
			generate-fieldop-add_mod_n \
			generate-fieldop-add_mod_p \
			generate-fieldop-div_by_2_mod_p,$(FIELDOP_GENERATE_TARGETS))

generate-sm2-strategy:
	$(MAKE) -j1 $(addprefix qcp-strategy-,$(ALL_STRATEGY_NAMES))

qcp-strategy-%:
	mkdir -p strategy
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(STRATEGY_CHECK) \
		$(STRATEGY_GEN_FLAGS) \
		$(QCP_ARGS) \
		--coq-output-dir=$(FORMAL_REPO_DIR)/strategy/ \
		--coq-logic-path=$(STRATEGY_LOGIC_ROOT) \
		--input-file=$(C_CASE_DIR)/strategy/$*.strategies

generate-solinas-case:
	mkdir -p vc/fieldOp
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/fieldOp/solinas_reduce_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/fieldOp/solinas_reduce_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/fieldOp/solinas_reduce_proof_manual.v \
		--coq-logic-path=$(FIELDOP_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/fieldOp/solinas_reduce.c

generate-solinas-minus-probe:
	mkdir -p vc/experiments
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/experiments/solinas_minus_probe_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/experiments/solinas_minus_probe_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/experiments/solinas_minus_probe_proof_manual.v \
		--coq-logic-path=$(EXPERIMENT_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/experiments/solinas_minus_probe.c

generate-experiment-%:
	mkdir -p vc/experiments
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/experiments/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/experiments/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/experiments/$*_proof_manual.v \
		--coq-logic-path=$(EXPERIMENT_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/experiments/$*.c

generate-basicop-%:
	mkdir -p vc/basicOp
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/basicOp/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/basicOp/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/basicOp/$*_proof_manual.v \
		--coq-logic-path=$(VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/basicOp/$*.c

generate-fieldop-%:
	mkdir -p vc/fieldOp
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/fieldOp/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/fieldOp/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/fieldOp/$*_proof_manual.v \
		--coq-logic-path=$(FIELDOP_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/fieldOp/$*.c

generate-ecc-%:
	mkdir -p vc/ecc
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/ecc/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/ecc/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/ecc/$*_proof_manual.v \
		--coq-logic-path=$(ECC_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/ecc/$*.c

generate-ecc-montg-%:
	mkdir -p vc/ecc_montg
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/ecc_montg/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/ecc_montg/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/ecc_montg/$*_proof_manual.v \
		--coq-logic-path=$(ECC_MONTG_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/ecc_montg/$*.c

generate-extra-%:
	mkdir -p vc/extra
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/extra/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/extra/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/extra/$*_proof_manual.v \
		--coq-logic-path=$(EXTRA_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/extra/$*.c

generate-sm2-protocol-%:
	mkdir -p vc/sm2
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/sm2/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/sm2/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/sm2/$*_proof_manual.v \
		--coq-logic-path=$(SM2_PROTOCOL_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/sm2/$*.c

generate-sm3-%:
	mkdir -p vc/sm3
	cd $(REPO_ROOT) && $(QCP_MEMORY_GUARD) $(SYMEXEC) \
		$(SYMEXEC_GEN_FLAGS) \
		--goal-file=$(FORMAL_REPO_DIR)/vc/sm3/$*_goal.v \
		--proof-auto-file=$(FORMAL_REPO_DIR)/vc/sm3/$*_proof_auto.v \
		--proof-manual-file=$(FORMAL_REPO_DIR)/vc/sm3/$*_proof_manual.v \
		--coq-logic-path=$(SM3_VC_LOGIC_ROOT) \
		$(QCP_ARGS) \
		--input-file=$(C_CASE_DIR)/sm3/$*.c

.PHONY: strategy-check
strategy-check: generate-sm2-strategy

.PHONY: libs strategies check basicop-check fieldop-check ecc-check ecc-montg-check all-check m2-fieldop-check m3-ecc-check m4-fixed-base-check m4-check m5-sm2-sign-check m5-sm2-verify-check sm3-check sm3-stream-check
libs: lib/u32_def.vo lib/ecc_point_def.vo lib/sm2_protocol_def.vo lib/sm2_c_layout.vo lib/limb_arithmetic.vo lib/byte_encoding.vo lib/bitwise.vo lib/sm3.vo lib/sm3_c_bridge.vo lib/sm3_def.vo lib/sm3_update_lib.vo lib/sm3_final_lib.vo lib/montgomery.vo lib/sm2_common_lib.vo lib/byte_memory.vo lib/sm2_curve_params.vo lib/sm2_primality.vo lib/sm2_curve.vo lib/sm2_generator_order.vo lib/sm2_no_three_torsion.vo lib/basicOp_lib.vo lib/almost_inverse.vo lib/fieldOp_lib.vo lib/ecc.vo lib/ec_math_refinement.vo lib/add_JPoint_and_AFPoint_lib.vo lib/add_JPoint_lib.vo lib/montg_add_jpoint_lib.vo lib/montg_add_jpoint_and_apoint_lib.vo lib/ecc_scalar_mul.vo lib/sm2_ecc_const_table.vo lib/sm2_basepoint_mul.vo lib/sm2_protocol.vo

strategies: $(SM2_STRATEGY_CHECKS) $(ECC_STRATEGY_CHECKS) $(ECC_AUX_STRATEGY_CHECKS) $(ECC_HELPER_STRATEGY_CHECKS) $(ADD_JPOINT_STRATEGY_CHECKS) $(MONTG_ADD_JPOINT_STRATEGY_CHECKS) $(MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_CHECKS) $(RAW_STRATEGY_CHECKS) $(M5_STRATEGY_CHECKS) $(SM3_STREAM_STRATEGY_CHECKS)

basicop-check: $(BASICOP_CHECKS)

fieldop-check: $(FIELDOP_CHECKS)

ecc-check: $(ECC_CHECKS)

ecc-montg-check: $(ECC_MONTG_CHECKS)

all-check: libs strategies basicop-check fieldop-check ecc-check ecc-montg-check m5-sm2-sign-check m5-sm2-verify-check sm3-check

check: all-check

m2-fieldop-check: $(M2_FIELDOP_CHECKS)

m3-ecc-check: $(M3_ECC_CHECKS) $(M3_ECC_MONTG_CHECKS)

m4-fixed-base-check: $(M4_FIXED_BASE_CHECKS)

m4-check: $(M4_FIXED_BASE_CHECKS) $(M4_WNAF_CHECKS)

m5-sm2-sign-check: $(M5_SM2_SIGN_CHECKS)

m5-sm2-verify-check: $(M5_EXTRA_CHECKS) $(M5_SM2_VERIFY_CHECKS)

sm3-check: $(SM3_CHECKS)

sm3-stream-check: $(SM3_STREAM_CHECKS)

solinas-libs: \
	lib/u32_def.vo \
	lib/limb_arithmetic.vo \
	lib/sm2_common_lib.vo \
	lib/montgomery.vo \
	lib/basicOp_lib.vo \
	lib/fieldOp_lib.vo

solinas-strategy: solinas-libs \
	$(SM2_STRATEGY_CHECKS)

solinas-goal: solinas-strategy vc/fieldOp/solinas_reduce_goal.vo

solinas-check: vc/fieldOp/solinas_reduce_goal_check.vo

lib/limb_arithmetic.vo: lib/limb_arithmetic.v
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/u32_def.vo: lib/u32_def.v
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/ecc_point_def.vo: lib/ecc_point_def.v lib/u32_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_protocol_def.vo: lib/sm2_protocol_def.v lib/u32_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_c_layout.vo: lib/sm2_c_layout.v lib/ecc_point_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_common_lib.vo: lib/sm2_common_lib.v lib/u32_def.vo lib/limb_arithmetic.vo lib/montgomery.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/byte_encoding.vo: lib/byte_encoding.v lib/limb_arithmetic.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/byte_memory.vo: lib/byte_memory.v lib/byte_encoding.vo lib/sm2_common_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/bitwise.vo: lib/bitwise.v
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm3.vo: lib/sm3.v lib/byte_encoding.vo lib/bitwise.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm3_c_bridge.vo: lib/sm3_c_bridge.v lib/sm3.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm3_def.vo: lib/sm3_def.v lib/sm3_c_bridge.vo lib/byte_memory.vo lib/sm2_c_layout.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm3_update_lib.vo: lib/sm3_update_lib.v lib/sm3_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm3_final_lib.vo: lib/sm3_final_lib.v lib/sm3_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_protocol.vo: \
	lib/sm2_protocol.v \
	lib/sm2_protocol_def.vo \
	lib/sm3_def.vo \
	lib/sm2_generator_order.vo \
	lib/sm2_ecc_const_table.vo \
	lib/sm2_basepoint_mul.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/montgomery.vo: lib/montgomery.v
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_primality.vo: lib/sm2_primality.v lib/sm2_common_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_curve_params.vo: lib/sm2_curve_params.v lib/sm2_common_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_curve.vo: lib/sm2_curve.v lib/sm2_curve_params.vo lib/sm2_primality.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_generator_order.vo: lib/sm2_generator_order.v lib/sm2_curve.vo lib/sm2_primality.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_no_three_torsion.vo: lib/sm2_no_three_torsion.v lib/sm2_generator_order.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/almost_inverse.vo: lib/almost_inverse.v lib/basicOp_lib.vo lib/montgomery.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/basicOp_lib.vo: \
	lib/basicOp_lib.v \
	lib/sm2_common_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/fieldOp_lib.vo: lib/fieldOp_lib.v lib/basicOp_lib.vo lib/sm2_primality.vo lib/almost_inverse.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/ecc.vo: lib/ecc.v lib/sm2_common_lib.vo lib/sm2_primality.vo lib/sm2_curve.vo lib/ecc_point_def.vo lib/sm2_c_layout.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/ec_math_refinement.vo: lib/ec_math_refinement.v lib/ecc.vo lib/fieldOp_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/add_JPoint_lib.vo: lib/add_JPoint_lib.v lib/ecc.vo lib/ec_math_refinement.vo lib/fieldOp_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/montg_add_jpoint_lib.vo: lib/montg_add_jpoint_lib.v lib/add_JPoint_lib.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/montg_add_jpoint_and_apoint_lib.vo: \
	lib/montg_add_jpoint_and_apoint_lib.v \
	lib/add_JPoint_lib.vo \
	lib/ec_math_refinement.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/add_JPoint_and_AFPoint_lib.vo: lib/add_JPoint_and_AFPoint_lib.v lib/ecc.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/ecc_scalar_mul.vo: lib/ecc_scalar_mul.v lib/ecc.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_ecc_const_table.vo: lib/sm2_ecc_const_table.v lib/ecc.vo lib/ec_math_refinement.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

lib/sm2_basepoint_mul.vo: lib/sm2_basepoint_mul.v lib/byte_memory.vo lib/sm2_generator_order.vo lib/sm2_ecc_const_table.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

strategy/%_strategy_goal.vo: \
	strategy/%_strategy_goal.v \
	lib/basicOp_lib.vo \
	lib/ecc_scalar_mul.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

strategy/ecc_representation_strategy_goal.vo: lib/ecc.vo lib/ecc_scalar_mul.vo
strategy/ecc_constants_strategy_goal.vo: lib/ecc.vo lib/ecc_scalar_mul.vo
strategy/ecc_point_overwrite_strategy_goal.vo: lib/ecc.vo lib/ecc_scalar_mul.vo
strategy/ecc_point_facts_strategy_goal.vo: lib/ecc.vo lib/ecc_scalar_mul.vo
strategy/ecc_point_copy_steps_strategy_goal.vo: lib/ecc.vo lib/ecc_scalar_mul.vo
strategy/jpoint_double_trace_strategy_goal.vo: lib/ecc.vo lib/ecc_scalar_mul.vo lib/ec_math_refinement.vo
strategy/add_JPoint_boundary_strategy_goal.vo: lib/add_JPoint_lib.vo
strategy/add_JPoint_trace_strategy_goal.vo: lib/add_JPoint_lib.vo
strategy/basepoint_bytes_strategy_goal.vo: lib/sm2_basepoint_mul.vo
strategy/basepoint_table_points_strategy_goal.vo: lib/sm2_basepoint_mul.vo lib/sm2_c_layout.vo
strategy/wnaf3_precomp_points_strategy_goal.vo: lib/ecc_scalar_mul.vo lib/sm2_c_layout.vo
strategy/wnaf3_predicate_cancellation_strategy_goal.vo: lib/ecc_scalar_mul.vo
strategy/byte_memory_views_strategy_goal.vo: lib/byte_memory.vo lib/sm3_def.vo
strategy/byte_pointer_views_strategy_goal.vo: lib/sm3_def.vo
strategy/sm3_word_views_strategy_goal.vo: lib/byte_memory.vo lib/sm3_def.vo
strategy/sm3_ctx_views_strategy_goal.vo: lib/sm3_def.vo
strategy/sm2_za_buffers_strategy_goal.vo: lib/sm3_def.vo
strategy/sm3_streaming_memory_views_strategy_goal.vo: lib/sm3_def.vo
strategy/sm2_protocol_views_strategy_goal.vo: lib/sm2_protocol.vo
$(addprefix strategy/,$(addsuffix _strategy_goal.vo,$(MONTG_ADD_JPOINT_STRATEGY_NAMES))): lib/montg_add_jpoint_lib.vo
$(addprefix strategy/,$(addsuffix _strategy_goal.vo,$(MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_NAMES))): lib/montg_add_jpoint_and_apoint_lib.vo

strategy/%_strategy_proof.vo: strategy/%_strategy_proof.v strategy/%_strategy_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

strategy/%_strategy_goal_check.vo: strategy/%_strategy_goal_check.v strategy/%_strategy_proof.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/u32_shl_goal.vo: vc/basicOp/u32_shl_goal.v lib/basicOp_lib.vo $(SM2_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/u32_shl_proof_auto.vo: vc/basicOp/u32_shl_proof_auto.v vc/basicOp/u32_shl_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/u32_shl_proof_manual.vo: vc/basicOp/u32_shl_proof_manual.v vc/basicOp/u32_shl_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/u32_shl_goal_check.vo: vc/basicOp/u32_shl_goal_check.v vc/basicOp/u32_shl_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/%_goal.vo: vc/basicOp/%_goal.v lib/basicOp_lib.vo $(SM2_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/raw_mul_goal.vo: strategy/raw_mul_arrays_strategy_proof.vo

vc/basicOp/raw_pow_goal.vo: strategy/raw_pow_arrays_strategy_proof.vo

vc/basicOp/%_proof_auto.vo: vc/basicOp/%_proof_auto.v vc/basicOp/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/%_proof_manual.vo: vc/basicOp/%_proof_manual.v vc/basicOp/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/%_goal_check.vo: \
	vc/basicOp/%_goal_check.v \
	vc/basicOp/%_goal.vo \
	vc/basicOp/%_proof_auto.vo \
	vc/basicOp/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/basicOp/u32_shl_goal.vo \
vc/basicOp/u32_shr_goal.vo \
vc/basicOp/u32_eq_goal.vo \
vc/basicOp/u32_eq_zero_goal.vo \
vc/basicOp/u32_eq_one_goal.vo \
vc/basicOp/u32_ge_goal.vo \
vc/basicOp/u32_gr_goal.vo \
vc/basicOp/u32_add_goal.vo \
vc/basicOp/u32_sub_goal.vo \
vc/basicOp/raw_mul_goal.vo \
vc/basicOp/raw_pow_goal.vo \
vc/basicOp/sm2p_mong_mul_core_goal.vo \
vc/basicOp/sm2n_mong_mul_core_goal.vo \
vc/basicOp/sm2p_mong_mul_goal.vo \
vc/basicOp/sm2n_mong_mul_goal.vo \
vc/basicOp/sm2p_mong_pow_goal.vo: \
	$(SM2_STRATEGY_PROOFS)

vc/experiments/%_def.vo: vc/experiments/%_def.v lib/u32_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/experiments/%_goal.vo: \
	vc/experiments/%_goal.v \
	vc/experiments/%_def.vo \
	lib/sm2_common_lib.vo \
	lib/ecc.vo \
	$(ECC_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

POINT_STRATEGY_PROBE_GOALS := \
	vc/experiments/afpoint_strategy_probe_goal.vo \
	vc/experiments/jpoint_strategy_probe_goal.vo

$(POINT_STRATEGY_PROBE_GOALS): vc/experiments/%_goal.vo: \
	vc/experiments/%_goal.v \
	lib/ecc.vo \
	$(ECC_STRATEGY_PROOFS) \
	strategy/sm2_representation_strategy_proof.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/experiments/%_proof_auto.vo: \
	vc/experiments/%_proof_auto.v \
	vc/experiments/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/experiments/%_proof_manual.vo: \
	vc/experiments/%_proof_manual.v \
	vc/experiments/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/experiments/%_goal_check.vo: \
	vc/experiments/%_goal_check.v \
	vc/experiments/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/extra/%_def.vo: vc/extra/%_def.v lib/u32_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

EXTRA_DEF_SOURCES := $(wildcard vc/extra/*_def.v)
EXTRA_DEF_GOALS := $(patsubst %_def.v,%_goal.vo,$(EXTRA_DEF_SOURCES))

$(EXTRA_DEF_GOALS): vc/extra/%_goal.vo: vc/extra/%_def.vo

vc/extra/%_goal.vo: \
	vc/extra/%_goal.v \
	lib/sm2_protocol.vo \
	$(SM2_STRATEGY_PROOFS) \
	$(M5_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/extra/%_proof_auto.vo: \
	vc/extra/%_proof_auto.v \
	vc/extra/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/extra/%_proof_manual.vo: \
	vc/extra/%_proof_manual.v \
	vc/extra/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/extra/%_goal_check.vo: \
	vc/extra/%_goal_check.v \
	vc/extra/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/solinas_reduce_goal.vo: \
	vc/fieldOp/solinas_reduce_goal.v \
	vc/fieldOp/solinas_reduce_def.vo \
	lib/fieldOp_lib.vo \
	$(SM2_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/solinas_reduce_def.vo: vc/fieldOp/solinas_reduce_def.v lib/u32_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/solinas_reduce_proof_auto.vo: \
	vc/fieldOp/solinas_reduce_proof_auto.v \
	vc/fieldOp/solinas_reduce_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/solinas_reduce_proof_manual.vo: \
	vc/fieldOp/solinas_reduce_proof_manual.v \
	vc/fieldOp/solinas_reduce_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/solinas_reduce_goal_check.vo: \
	vc/fieldOp/solinas_reduce_goal_check.v \
	vc/fieldOp/solinas_reduce_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/%_def.vo: vc/fieldOp/%_def.v lib/u32_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

FIELDOP_DEF_SOURCES := $(wildcard vc/fieldOp/*_def.v)
FIELDOP_DEF_GOALS := $(patsubst %_def.v,%_goal.vo,$(FIELDOP_DEF_SOURCES))

$(FIELDOP_DEF_GOALS): vc/fieldOp/%_goal.vo: vc/fieldOp/%_def.vo

vc/fieldOp/%_goal.vo: \
	vc/fieldOp/%_goal.v \
	lib/u32_def.vo \
	lib/fieldOp_lib.vo \
	$(SM2_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/add_mod_p_goal.vo \
vc/fieldOp/sub_mod_p_goal.vo \
vc/fieldOp/div_by_2_mod_p_goal.vo \
vc/fieldOp/mul_by_2_mod_p_goal.vo \
vc/fieldOp/mul_by_3_mod_p_goal.vo: lib/ec_math_refinement.vo

vc/fieldOp/%_proof_auto.vo: \
	vc/fieldOp/%_proof_auto.v \
	vc/fieldOp/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/%_proof_manual.vo: \
	vc/fieldOp/%_proof_manual.v \
	vc/fieldOp/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/fieldOp/%_goal_check.vo: \
	vc/fieldOp/%_goal_check.v \
	vc/fieldOp/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc/%_def.vo: vc/ecc/%_def.v lib/u32_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

ECC_POINT_DEF_CASES := ML_mul_basepoint add_JPoint_and_AFPoint montg_times_base_point
$(addprefix vc/ecc/,$(addsuffix _def.vo,$(ECC_POINT_DEF_CASES))): lib/ecc_point_def.vo

ECC_DEF_SOURCES := $(wildcard vc/ecc/*_def.v)
ECC_DEF_GOALS := $(patsubst %_def.v,%_goal.vo,$(ECC_DEF_SOURCES))

$(ECC_DEF_GOALS): vc/ecc/%_goal.vo: vc/ecc/%_def.vo

vc/ecc/%_goal.vo: \
	vc/ecc/%_goal.v \
	lib/ecc.vo \
	$(SM2_STRATEGY_PROOFS) \
	$(ECC_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc/montg_apoint_to_montg_goal.vo: lib/fieldOp_lib.vo
vc/ecc/montg_inv_mod_n_ex_goal.vo: lib/fieldOp_lib.vo
vc/ecc/double_JPoint_goal.vo: lib/ec_math_refinement.vo
vc/ecc/add_JPoint_and_AFPoint_goal.vo: lib/add_JPoint_and_AFPoint_lib.vo
vc/ecc/add_JPoint_goal.vo: lib/add_JPoint_lib.vo $(ADD_JPOINT_STRATEGY_PROOFS)
vc/ecc/montg_double_jpoint_goal.vo: lib/ec_math_refinement.vo
vc/ecc/montg_double_jpoint_ex_goal.vo: lib/ec_math_refinement.vo
vc/ecc/ML_mul_basepoint_goal.vo \
vc/ecc/montg_times_base_point_goal.vo: \
	lib/sm2_basepoint_mul.vo \
	strategy/basepoint_bytes_strategy_proof.vo \
	strategy/basepoint_table_points_strategy_proof.vo

vc/ecc/montg_inv_mod_n_ex_goal.vo: \
	strategy/ecc_montg_helper_views_strategy_proof.vo

vc/ecc/AFPoint_neg_goal.vo \
vc/ecc/affine_to_jacobian_goal.vo \
vc/ecc/double_JPoint_goal.vo \
vc/ecc/add_JPoint_goal.vo \
vc/ecc/add_JPoint_and_AFPoint_goal.vo: \
	strategy/ecc_point_copy_steps_strategy_proof.vo

vc/ecc/double_JPoint_goal.vo \
vc/ecc/montg_double_jpoint_goal.vo: \
	strategy/jpoint_double_trace_strategy_proof.vo

vc/ecc/%_proof_auto.vo: \
	vc/ecc/%_proof_auto.v \
	vc/ecc/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc/%_proof_manual.vo: \
	vc/ecc/%_proof_manual.v \
	vc/ecc/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc/%_goal_check.vo: \
	vc/ecc/%_goal_check.v \
	vc/ecc/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc_montg/%_def.vo: vc/ecc_montg/%_def.v lib/u32_def.vo lib/ecc_point_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

ECC_MONTG_DEF_SOURCES := $(wildcard vc/ecc_montg/*_def.v)
ECC_MONTG_DEF_GOALS := $(patsubst %_def.v,%_goal.vo,$(ECC_MONTG_DEF_SOURCES))

$(ECC_MONTG_DEF_GOALS): vc/ecc_montg/%_goal.vo: vc/ecc_montg/%_def.vo

vc/ecc_montg/%_goal.vo: \
	vc/ecc_montg/%_goal.v \
	lib/basicOp_lib.vo \
	lib/ecc.vo \
	lib/fieldOp_lib.vo \
	$(SM2_STRATEGY_PROOFS) \
	$(ECC_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc_montg/montg_add_jpoint_goal.vo: \
	lib/montg_add_jpoint_lib.vo \
	$(ECC_AUX_STRATEGY_PROOFS) \
	$(MONTG_ADD_JPOINT_STRATEGY_PROOFS)

vc/ecc_montg/montg_add_jpoint_and_apoint_goal.vo: \
	lib/montg_add_jpoint_and_apoint_lib.vo \
	$(ECC_AUX_STRATEGY_PROOFS) \
	$(MONTG_ADD_JPOINT_AND_APOINT_STRATEGY_PROOFS)

vc/ecc_montg/montg_pre_compute_naf_w3_goal.vo: \
	lib/sm2_no_three_torsion.vo \
	strategy/ecc_point_copy_steps_strategy_proof.vo \
	strategy/ecc_point_overwrite_strategy_proof.vo \
	strategy/wnaf3_precomp_points_strategy_proof.vo

vc/ecc_montg/montg_times_point_naf_w3_goal.vo: \
	strategy/ecc_point_copy_steps_strategy_proof.vo \
	strategy/ecc_point_overwrite_strategy_proof.vo \
	strategy/wnaf3_precomp_points_strategy_proof.vo \
	strategy/wnaf3_predicate_cancellation_strategy_proof.vo

vc/ecc_montg/montg_apoint_to_jpoint2_goal.vo \
vc/ecc_montg/montg_jpoint_to_apoint_goal.vo \
vc/ecc_montg/montg_inv_mod_p_ex_goal.vo \
vc/ecc_montg/montg_is_apoint_zero_goal.vo \
vc/ecc_montg/montg_is_jpoint_zero_goal.vo: \
	strategy/ecc_montg_helper_views_strategy_proof.vo

vc/ecc_montg/%_proof_auto.vo: \
	vc/ecc_montg/%_proof_auto.v \
	vc/ecc_montg/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc_montg/%_proof_manual.vo: \
	vc/ecc_montg/%_proof_manual.v \
	vc/ecc_montg/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/ecc_montg/%_goal_check.vo: \
	vc/ecc_montg/%_goal_check.v \
	vc/ecc_montg/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/sm2/%_def.vo: vc/sm2/%_def.v lib/sm2_protocol_def.vo lib/ecc_point_def.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

SM2_PROTOCOL_DEF_SOURCES := $(wildcard vc/sm2/*_def.v)
SM2_PROTOCOL_DEF_GOALS := $(patsubst %_def.v,%_goal.vo,$(SM2_PROTOCOL_DEF_SOURCES))

$(SM2_PROTOCOL_DEF_GOALS): vc/sm2/%_goal.vo: vc/sm2/%_def.vo

vc/sm2/%_goal.vo: \
	vc/sm2/%_goal.v \
	lib/sm2_protocol.vo \
	lib/fieldOp_lib.vo \
	lib/sm2_basepoint_mul.vo \
	$(SM2_STRATEGY_PROOFS) \
	$(ECC_STRATEGY_PROOFS) \
	$(ECC_HELPER_STRATEGY_PROOFS) \
	$(M5_STRATEGY_PROOFS)
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/sm2/sm2_sign_dgst_goal.vo: $(ECC_AUX_STRATEGY_PROOFS)

vc/sm2/%_proof_auto.vo: \
	vc/sm2/%_proof_auto.v \
	vc/sm2/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/sm2/%_proof_manual.vo: \
	vc/sm2/%_proof_manual.v \
	vc/sm2/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/sm2/%_goal_check.vo: \
	vc/sm2/%_goal_check.v \
	vc/sm2/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/sm3/%_goal.vo: \
	vc/sm3/%_goal.v \
	lib/sm3_def.vo \
	strategy/byte_memory_views_strategy_proof.vo \
	strategy/sm3_ctx_views_strategy_proof.vo \
	strategy/sm3_word_views_strategy_proof.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

$(addprefix vc/sm3/,$(addsuffix _goal.vo,$(SM3_STREAM_CASES))): \
	$(SM3_STREAM_STRATEGY_PROOFS)

vc/sm3/%_proof_auto.vo: \
	vc/sm3/%_proof_auto.v \
	vc/sm3/%_goal.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/sm3/%_proof_manual.vo: \
	vc/sm3/%_proof_manual.v \
	vc/sm3/%_proof_auto.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<

vc/sm3/sm3_update_proof_manual.vo: lib/sm3_update_lib.vo
vc/sm3/sm3_final_proof_manual.vo: lib/sm3_final_lib.vo

vc/sm3/%_goal_check.vo: \
	vc/sm3/%_goal_check.v \
	vc/sm3/%_proof_manual.vo
	@echo COQC $<
	@cd $(SL_DIR) && $(COQC) $(COQ_FLAG) $(CASE_DIR)/$<
