Require Import NArith ZArith ZModOffset Zmod Lia Numbers.ZmodDef.
Require Import Bool.Bool Lists.List Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Local Coercion N.pos : positive >-> N.
Local Coercion Z.of_N : N >-> Z.
Local Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
Local Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Module Export Dep.
Module Zmod.
Import Zmod.Base.Zmod.
Export ZmodDef.Zmod.

(** ** Bitvector operations that vary modulues *)

(** Effective use of the operations defined here with moduli that are not
   converitble to values requires substantial understanding of dependent types,
   in particular the equality type, the sigma type, and their eliminators. Even
   so, many applications are better served by [Z] or by adopting one
   common-denominator modulus. See [skipn_app] and [skipn_app'] for an example
   of the challenges. *)

Definition app {n m} (a : Zmod (2^n)) (b : Zmod (2^m)) : Zmod (2^(n+m)) :=
  of_Z _ (Z.lor a (Z.shiftl b n)).

Definition firstn n {w} (a : Zmod (2^w)) : Zmod (2^n) := of_Z _ a.

Definition skipn n {w} (a : Zmod (2^w)) : Zmod (2^(w-n)) := of_Z _ (Z.shiftr a n).

Definition extract start pastend {w} (a : Zmod (2^w)) : Zmod (2^(pastend-start)) :=
  firstn (pastend-start) (skipn start a).

Lemma to_Z_app {n m} a b : to_Z (@app n m a b) = Z.lor a (Z.shiftl b n).
Proof.
  cbv [app]. rewrite to_Z_of_Z, Z.mod_small; trivial.
  rewrite ?Pos2Z.inj_pow, ?Pos2Z.inj_add, ?Z.pow_add_r in * by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  (* lor <= add *)
  pose proof to_Z_range a; pose proof to_Z_range b.
  pose proof Z.lor_nonneg a (b * 2^n). pose proof Z.land_nonneg a (b * 2^n).
  pose proof Z.add_lor_land a (b * 2^n). nia.
Qed.

Lemma to_Z_firstn n {w} a : to_Z (@firstn n w a) = a mod 2^n.
Proof.
  cbv [firstn]. rewrite to_Z_of_Z, Pos2Z.inj_pow; trivial.
Qed.

Lemma to_Z_skipn n {w} a : to_Z (@skipn n w a) = Z.shiftr a n.
Proof.
  cbv [skipn]. rewrite to_Z_of_Z, Z.mod_small; trivial.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof to_Z_range a.
  rewrite ?Pos2Z.inj_pow, ?Pos2Z.inj_add, ?Z.pow_add_r in * by lia.
  case (Pos.ltb_spec n w) as [].
  { replace (Z.pos w) with (Pos.sub w n+n) in H by lia; rewrite Z.pow_add_r in H by lia.
    Z.div_mod_to_equations; nia. }
  { pose proof Z.pow_le_mono_r 2 w n; rewrite Z.div_small; lia. }
Qed.

Lemma to_Z_extract start pastend {w} (a : Zmod (2^w)) :
  to_Z (extract start pastend a) = Z.shiftr a start mod 2^(pastend-start).
Proof.
  cbv [extract].
  rewrite to_Z_firstn, to_Z_skipn; f_equal; f_equal.
Abort. (* FIXME TODO: can't take length-0 slice because of Pos.pow in type *)

Lemma firstn_app n m a b : firstn n (@app n m a b) = a.
Proof.
  apply to_Z_inj; rewrite to_Z_firstn, to_Z_app.
  symmetry. rewrite <-mod_to_Z at 1; symmetry.
  rewrite Pos2Z.inj_pow, <-!Z.land_ones by lia.
  apply Z.bits_inj'; intros i Hi.
  repeat rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.shiftl_spec, ?Z.testbit_ones,
    ?Z.mod_pow2_bits_high, ?testbit_high_pow2, ?(Z.testbit_neg_r(*workaround*)b),
    ?Zle_imp_le_bool, ?Bool.andb_true_l by lia; trivial.
  destruct (Z.ltb_spec i n); try Btauto.btauto.
  rewrite (Z.testbit_neg_r b) by lia; Btauto.btauto.
Qed.

Lemma skipn_app' n m a b : existT _ _ (skipn n (@app n m a b)) = existT _ _ b.
Proof.
  pose proof to_Z_range a. eapply to_Z_inj_dep. { f_equal. lia. }
  rewrite to_Z_skipn, to_Z_app, Z.shiftr_lor, Z.shiftr_shiftl_l by lia.
  erewrite Z.sub_diag, Z.shiftl_0_r, Z.shiftr_div_pow2, Z.div_small, Z.lor_0_l; lia.
Qed.

Lemma skipn_app n m a b pf : skipn n (@app n m a b) = eq_rect _ Zmod b _ pf.
Proof.
  pose proof skipn_app' n m a b as E; symmetry in E; inversion_sigma.
  apply to_Z_inj. rewrite to_Z_eq_rect, <-E2, to_Z_eq_rect; trivial.
Qed.

End Zmod.
End Dep.
