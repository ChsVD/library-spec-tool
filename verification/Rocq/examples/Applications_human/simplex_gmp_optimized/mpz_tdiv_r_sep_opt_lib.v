From Coq Require Import ZArith Lia.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_lib.

Local Open Scope Z_scope.

(* The dividend and divisor are [zn] and [zd]. The existing TRUNC relation
   fixes the remainder [rv] even when either operand is negative. *)
Lemma simplex_tdiv_r_math_rem zn zd qv rv :
  mpz_div_qr_math GMP_DIV_TRUNC zn zd qv rv ->
  rv = Z.rem zn zd.
Proof.
  intro Hmath.
  unfold mpz_div_qr_math in Hmath.
  destruct Hmath as [Htrunc | [Hfloor | Hceil]].
  - destruct Htrunc as [Hzd [_ [Heq [Hbound Hsign]]]].
    unfold same_sign in Hsign.
    rewrite <- Z.rem_abs_r by exact Hzd.
    destruct (Z_le_gt_dec 0 zn) as [Hn | Hn].
    + assert (Hrv : 0 <= rv) by (destruct Hsign as [H0 | [Hs | Hs]]; lia).
      rewrite (Z.abs_eq rv Hrv) in Hbound.
      destruct (Z_le_gt_dec 0 zd) as [Hd | Hd].
      * apply Z.rem_unique with (q := qv).
        -- exact Hn.
        -- lia.
        -- rewrite Z.abs_eq by lia. nia.
      * apply Z.rem_unique with (q := -qv).
        -- exact Hn.
        -- lia.
        -- rewrite Z.abs_neq by lia. nia.
    + assert (Hrv : rv <= 0) by (destruct Hsign as [H0 | [Hs | Hs]]; lia).
      rewrite (Z.abs_neq rv Hrv) in Hbound.
      assert (Hneg : -rv = Z.rem (-zn) (Z.abs zd)).
      { destruct (Z_le_gt_dec 0 zd) as [Hd | Hd].
        - apply Z.rem_unique with (q := -qv).
          + lia.
          + lia.
          + rewrite Z.abs_eq by lia. nia.
        - apply Z.rem_unique with (q := qv).
          + lia.
          + lia.
          + rewrite Z.abs_neq by lia. nia. }
      rewrite Z.rem_opp_l in Hneg by (destruct zd; simpl in *; lia).
      lia.
  - destruct Hfloor as [_ [Hmode _]]. discriminate Hmode.
  - destruct Hceil as [_ [Hmode _]]. discriminate Hmode.
Qed.
