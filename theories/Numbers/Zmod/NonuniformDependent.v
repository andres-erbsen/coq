Require Import Coq.Numbers.Zmod.TODO_MOVE.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Numbers.Zmod.Base.

Local Open Scope Z_scope.
Import Zmod.Base.Coercions.

(** Operations that change the modulus *)

(* This module provides operations that vary m in [Zmod m], for example
 * concatenating bitvectors and combining congruences. *)

(* Effective use of the operations defined here with moduli that are not
   converitble to values requires substantial understanding of dependent types,
   in particular the equality type, the sigma type, and their eliminators. Even
   so, many applications are better served by [Z] or by adopting one
   common-denominator modulus.
   The next few lemmas will give a taste of the challenges. *)

Goal forall {m} (a : Zmod m) {n} (b : Zmod n), Prop.
  intros.
  assert_fails (assert (a = b)). (* type error: need n == m *)
  assert_fails (pose (add a b)). (* type error: need n == m *)
Abort.

Lemma to_N_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_N a = to_N b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_N_inj. Qed.

Lemma to_N_eq_rect {m} (a : Zmod m) n p : to_N (eq_rect _ _ a n p) = to_N a.
Proof. case p; trivial. Qed.

Lemma to_N_eq_rect_attempt {m} (a : Zmod m) n p : to_N (eq_rect (Zmod m) id a (Zmod n) p) = to_N a.
Proof. assert_fails (case p). Abort.

Lemma to_Z_eq_rect {m} (a : Zmod m) n p : to_Z (eq_rect _ _ a n p) = to_Z a.
Proof. case p; trivial. Qed.

Lemma to_Z_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_Z a = to_Z b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_Z_inj. Qed.

(* TODO: high part first or low part first? *)
Definition undivmodM {a b} (hi : Zmod a) (lo : Zmod b) : Zmod (a * b).
  refine (of_small_N _ (N.undivmod b hi lo) (fun _ => _))%N.
  abstract (cbv [N.undivmod]; pose proof to_N_range hi; pose proof to_N_range lo; nia).
Defined.

Lemma undivmodM_ok {a b} hi lo : @undivmodM a b hi lo = of_N _ (N.undivmod b hi lo).
Proof. apply of_small_N_ok. Qed.

Lemma to_N_undivmodM {a b} hi lo : to_N (@undivmodM a b hi lo) = N.undivmod b hi lo.
Proof. apply to_N_of_small_N. Qed.

Lemma to_Z_undivmodM {a b} hi lo : to_Z (@undivmodM a b hi lo) = b*hi + lo.
Proof. cbv [to_Z]. rewrite to_N_undivmodM. cbv [N.undivmod]. lia. Qed.

Definition divM a b (x : Zmod (a * b)) : Zmod a.
  refine (of_small_N _ (x / b) (fun _ => _))%N.
  abstract (pose proof to_N_range x; zify; Z.div_mod_to_equations; nia).
Defined.

Lemma divM_ok {a b} x : @divM a b x = of_N _ (x / b)%N.
Proof. apply of_small_N_ok. Qed.

Lemma to_N_divM {a b} x : to_N (@divM a b x) = (x / b)%N.
Proof. apply to_N_of_small_N. Qed.

Lemma divM_undivmodM {a b} x y : divM a b (undivmodM x y) = x.
Proof.
  apply to_N_inj. rewrite to_N_divM, to_N_undivmodM, N.div_undivmod;
    auto using to_N_range.
Qed.

Definition modM a b (x : Zmod (a * b)) := of_N b x.

Lemma modM_ok {a b} x : @modM a b x = of_N _ (x mod b)%N.
Proof. apply of_small_N_ok. Qed.

Lemma to_N_modM {a b} x : to_N (@modM a b x) = (x mod b)%N.
Proof. apply to_N_of_small_N. Qed.

Lemma modM_undivmodM {a b} x y : modM a b (undivmodM x y) = y.
Proof.
  apply to_N_inj. rewrite to_N_modM, to_N_undivmodM, N.mod_undivmod;
    auto using to_N_range.
Qed.

Definition crtM {a b} (x : Zmod a) (y : Zmod b) := of_Z (a*b) (Znumtheory.solvecong a b x y).

Lemma modM_crtM {a b : positive} x y (H : Z.gcd a b = 1) : modM a b (crtM x y) = y.
Proof.
  apply to_Z_inj; cbv [crtM modM].
  rewrite to_N_of_Z, to_Z_of_N, Z2N.id, <-Znumtheory.Zmod_div_mod; try lia.
  { rewrite (proj2 (Znumtheory.solvecong_coprime a b x y H)), mod_to_Z; trivial. }
  { exists a. lia. }
  { apply Z.mod_pos_bound. lia. }
Qed.

Lemma crtM_comm {a b} (x : Zmod a) (y : Zmod b) (H : Z.gcd a b = 1) :
  existT Zmod _ (crtM x y) = existT Zmod _ (crtM y x).
Proof.
  apply to_Z_inj_dep; try lia; cbv [crtM]; rewrite !to_Z_of_Z.
  rewrite Znumtheory.solvecong_comm; f_equal; try lia.
Qed.

Definition concatM {a b} (hi : Zmod (2^a)) (lo : Zmod (2^b)) : Zmod (2^(a+b)).
  refine (of_small_N _ (N.lor (N.shiftl hi b) lo) (fun _ => _))%N.
  abstract (
    rewrite <-N.undivmod_pow2, Pos.pow_add_r by auto using to_N_range;
    cbv [N.undivmod]; pose proof to_N_range hi; pose proof to_N_range lo; nia).
Defined.

Lemma concatM_ok {a b} hi lo : to_N (@concatM a b hi lo) = to_N (undivmodM hi lo).
Proof.
  cbv [concatM]; rewrite to_N_of_small_N, to_N_undivmodM.
  rewrite <-N.undivmod_pow2 by auto using to_N_range; trivial.
Qed.

Lemma concatM_ok_dep {a b} hi lo : existT _ _ (@concatM a b hi lo) = existT _ _ (undivmodM hi lo).
Proof. apply to_N_inj_dep; auto using concatM_ok, Pos.pow_add_r. Qed.
