Require Import NArith ZArith ZModOffset Lia Numbers.ZmodDef.
Require Import Bool.Bool Lists.List Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.
Local Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
Local Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Module Export Base.
Module Zmod.
Export ZmodDef.Zmod.

(** ** Unsigned conversions to [Z] *)

Lemma mod_unsigned {m} (x : Zmod m) : x mod m = x.
Proof. case x as [x H]; apply Private_small_iff, H. Qed.
Notation mod_to_Z := mod_unsigned (only parsing).

Local Lemma unsigned_range {m} (x : Zmod m) : 0 <= x < m \/ m = 0 \/ m < x <= 0.
Proof. apply Z.mod_id_iff, mod_to_Z. Qed.
Notation to_Z_range := unsigned_range (only parsing).

Lemma unsigned_pos_bound {m} (x : Zmod m) : 0 < m -> 0 <= x < m.
Proof. rewrite <-mod_to_Z. apply Z.mod_pos_bound. Qed.
Notation to_Z_pos_bound := unsigned_pos_bound (only parsing).

Lemma unsigned_neg_bound {m} (x : Zmod m) : m < 0 -> m < x <= 0.
Proof. rewrite <-mod_to_Z. apply Z.mod_neg_bound. Qed.
Notation to_Z_neg_bound := unsigned_neg_bound (only parsing).

Lemma unsigned_inj m (x y : Zmod m) : to_Z x = to_Z y -> x = y.
Proof. cbv [to_Z Private_to_Z]; destruct x, y, 1. apply f_equal, Is_true_hprop. Qed.
Notation to_Z_inj := unsigned_inj (only parsing).

Lemma unsigned_inj_iff {m} (x y : Zmod m) : to_Z x = to_Z y <-> x = y.
Proof. split; try apply to_Z_inj; congruence. Qed.
Notation to_Z_inj_iff := unsigned_inj_iff (only parsing).

Lemma unsigned_of_small_Z {m} n pf : to_Z (of_small_Z m n pf) = n.
Proof. exact eq_refl. Qed.
Notation to_Z_of_small_Z := unsigned_of_small_Z (only parsing).

Lemma unsigned_of_Z {m} z : to_Z (of_Z m z) = z mod m.
Proof. apply to_Z_of_small_Z. Qed.
Notation to_Z_of_Z := unsigned_of_Z (only parsing).

Lemma of_small_Z_ok {m} n pf : of_small_Z m n pf = of_Z m n.
Proof. apply to_Z_inj. rewrite to_Z_of_small_Z, to_Z_of_Z, (pf I); trivial. Qed.

Lemma of_Z_to_Z {m} x : of_Z m (to_Z x) = x.
Proof. apply to_Z_inj. rewrite to_Z_of_Z, mod_to_Z; trivial. Qed.

Lemma unsigned_of_Z_id_iff {m} n :
  to_Z (of_Z m n) = n <-> 0 <= n < m \/ m = 0 \/ m < n <= 0.
Proof. rewrite to_Z_of_Z; apply Z.mod_id_iff. Qed.
Notation to_Z_of_Z_id_iff := unsigned_of_Z_id_iff.

Lemma unsigned_of_Z_id {m} n (H : 0 <= n < m \/ m = 0 \/ m < n <= 0) :
  to_Z (of_Z m n) = n.
Proof. apply to_Z_of_Z_id_iff, H. Qed.
Notation to_Z_of_Z_id := unsigned_of_Z_id .

Lemma unsigned_of_Z_mod0 n : to_Z (of_Z 0 n) = n.
Proof. apply to_Z_of_Z_id; intuition idtac. Qed.
Notation  to_Z_of_Z_mod0 := unsigned_of_Z_mod0 (only parsing).

Lemma unsigned_of_Z_small {m} n (H : 0 <= n < m) : to_Z (of_Z m n) = n.
Proof. rewrite to_Z_of_Z, Z.mod_small; trivial. Qed.
Notation to_Z_of_Z_small := unsigned_of_Z_small.

Lemma of_Z_mod {m} x : of_Z m (x mod m) = of_Z m x.
Proof. apply to_Z_inj. rewrite ?to_Z_of_Z, ?Zmod_mod; trivial. Qed.

Lemma of_Z_inj {m} x y : of_Z m x = of_Z m y <-> x mod m = y mod m.
Proof.
  split.
  { intros H%(f_equal to_Z). rewrite 2to_Z_of_Z in *; trivial. }
  { rewrite <-of_Z_mod. rewrite <-(of_Z_mod y). congruence. }
Qed.

Lemma of_Z_inj_abs' {m} x y : of_Z m x = of_Z m y <-> x mod (Z.abs m) = y mod (Z.abs m).
Proof. rewrite Z.eq_mod_abs, of_Z_inj; reflexivity. Qed.

Lemma of_Z_inj_abs {m} x y : of_Z m x = of_Z m y <-> (Z.abs m <> 1 -> x mod (Z.abs m) = y mod (Z.abs m)).
Proof.
  rewrite of_Z_inj_abs'.
  case (Z.eq_dec (Z.abs m) 1) as [->|]; rewrite ?Z.mod_1_r; intuition idtac.
Qed.

Lemma of_Z_inj_cases {m} x y : of_Z m x = of_Z m y <->
  ((m = 0 -> x = y) /\ let m' := Z.abs m in 2 <= m' -> x mod m' = y mod m').
Proof.
  rewrite of_Z_inj_abs.
  split.
  { split.
    { intros ->. rewrite !Zmod_0_r in H; apply H; inversion 1. }
    { intros. subst. specialize (H ltac:(lia)).
      rewrite ?Z.abs_eq in * by lia; trivial. } }
  { intros [A B] ?. 
    case (Z.eq_dec m 0) as [->|].
    { rewrite A; trivial. }
    apply B; lia. }
Qed.

(** ** Signed conversions to [Z] *)

Lemma smod_unsigned {m} (x : Zmod m) : Z.smodulo (unsigned x) m = signed x.
Proof.
  pose proof to_Z_range x. cbv [signed Z.smodulo Z.omodulo] in *.
  case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
  rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq 1) by (Z.quot_rem_to_equations; lia);
    Z.quot_rem_to_equations; try lia.
Qed.

Lemma smod_signed {m} (x : Zmod m) : Z.smodulo (signed x) m = signed x.
Proof. rewrite <-smod_unsigned, Z.smod_smod; trivial. Qed.

Lemma signed_range {m} (x : Zmod m) :
  ltac:(let t := type of (Z.smod_small_iff (signed x) m) in
  match eval cbv zeta in t with ?P <-> _ => exact P end).
Proof. apply Z.smod_small_iff, smod_signed. Qed.

Lemma signed_pos_bound {m} (x : Zmod m) (Hm : 0 < m) : -m <= 2*signed x < m.
Proof. rewrite <-smod_unsigned. pose proof Z.smod_pos_bound x m; lia. Qed.

Lemma signed_neg_bound {m} (x : Zmod m) (Hm : m < 0) : m < 2*signed x <= - m.
Proof. rewrite <-smod_unsigned. pose proof Z.smod_neg_bound x m; lia. Qed.

Lemma signed_inj m (x y : Zmod m) : signed x = signed y -> x = y.
Proof.
  rewrite <-2 smod_unsigned; intros H%Z.mod_inj_smod; rewrite ?mod_to_Z in *.
  apply to_Z_inj, H.
Qed.

Lemma signed_inj_iff {m} (x y : Zmod m) : signed x = signed y <-> x = y.
Proof. split; try apply signed_inj; congruence. Qed.

Lemma mod_signed {m} (x : Zmod m) : signed x mod m = unsigned x.
Proof. rewrite <-smod_unsigned, Z.mod_smod, mod_to_Z; trivial. Qed.

Lemma signed_of_Z {m} z : signed (of_Z m z) = Z.smodulo z m.
Proof. rewrite <-smod_unsigned, to_Z_of_Z, Z.smod_mod; trivial. Qed.

Lemma signed_of_Z_small {m} z (H : - m <= 2 * z - Z.rem m 2 < m) :
  signed (of_Z m z) = z.
Proof. rewrite signed_of_Z, Z.smod_small; trivial. Qed.

Lemma signed_of_Z_even_small {m} (Hm : m mod 2 = 0)
  z (H : - m <= 2 * z < m) : signed (of_Z m z) = z.
Proof.
  rewrite signed_of_Z, Z.smod_even_small;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma of_Z_signed {m} x : of_Z m (signed x) = x.
Proof. apply signed_inj. rewrite signed_of_Z, smod_signed; trivial. Qed.

Lemma signed_small {m} (x : Zmod m) (H : 0 <= 2*x < m) : signed x = unsigned x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.

Lemma signed_large {m} (x : Zmod m) (H : 0 <= m <= 2*x) : signed x = x-m.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.

Lemma unsigned_pos {m} (x : Zmod m) (Hm : 0 <= m) (H : 0 <= signed x) : unsigned x = signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.
Notation to_Z_pos := unsigned_pos (only parsing).

Lemma unsigned_neg {m} (x : Zmod m) (Hm : 0 <= m) (H : signed x < 0) : unsigned x = m + signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.
Notation to_Z_neg := unsigned_neg (only parsing).

Lemma signed_neg_iff {m} (x : Zmod m) (Hm : 0 < m) :
  signed x < 0 <-> m <= 2 * unsigned x.
Proof.
  pose proof to_Z_range x.
  destruct (Z.leb_spec m (2 * unsigned x)); intuition try lia.
  { rewrite signed_large; lia. }
  { rewrite signed_small in *; lia. }
Qed.

Lemma signed_small_iff {m} (x : Zmod m) (Hm : 0 < m) :
  signed x = unsigned x <-> 2 * unsigned x < m.
Proof.
  pose proof to_Z_range x.
  destruct (Z.ltb_spec (2 * unsigned x) m); intuition try lia.
  { rewrite signed_small in *; lia. }
  { pose proof signed_neg_iff x; intuition try lia. }
Qed.

Lemma signed_nonneg_iff {m} (x : Zmod m) (Hm : 0 < m) :
  0 <= signed x <-> 2 * unsigned x < m.
Proof.
  pose proof to_Z_range x.
  destruct (Z.ltb_spec (2 * unsigned x) m); intuition try lia.
  { rewrite signed_small; lia. }
  { rewrite signed_large in *; lia. }
Qed.

Lemma signed_pos_iff {m} (x : Zmod m) (Hm : 0 < m) :
  0 < signed x <-> 0 < 2 * unsigned x < m.
Proof. pose proof signed_nonneg_iff x; pose proof signed_small_iff x; lia. Qed.

(** ** Constants *)

Lemma unsigned_0 m : @to_Z m zero = 0. Proof. trivial. Qed.
Notation to_Z_0 := unsigned_0 (only parsing).

Lemma unsigned_0_iff {m} x : @to_Z m x = 0 <-> x = zero.
Proof. rewrite <-to_Z_inj_iff, to_Z_0; reflexivity. Qed.
Notation to_Z_0_iff := unsigned_0_iff (only parsing).

Lemma of_Z_0 {m} : of_Z m 0 = zero. Proof. symmetry; apply of_small_Z_ok. Qed.

Lemma signed_0 m : @signed m zero = 0.
Proof. rewrite <-smod_unsigned, to_Z_0, Z.smod_0_l; trivial. Qed.

Lemma signed_0_iff {m} x : @signed m x = 0 <-> x = zero.
Proof. rewrite <-signed_inj_iff, signed_0; reflexivity. Qed.

Lemma of_Z_1 {m} : of_Z m 1 = one. Proof. apply to_Z_inj. trivial. Qed.

Lemma unsigned_1 {m} : @to_Z m one = 1 mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_1 := unsigned_1 (only parsing).

Lemma unsigned_1_pos {m} (Hm : 2 <= m) : @to_Z m one = 1.
Proof. cbv [one]; rewrite to_Z_of_Z_small; lia. Qed.
Notation to_Z_1_pos := unsigned_1_pos (only parsing).

Lemma unsigned_1_1 : @to_Z 1 one = 0. trivial. Qed.
Notation to_Z_1_1 := unsigned_1_1 (only parsing).

Lemma unsigned_1_neg {m} (Hm : m <= 0) : @to_Z m one = m+1.
Proof. cbv [one]; rewrite to_Z_of_Z, (Z.mod_diveq (-1)); try lia. Qed.
Notation to_Z_1_neg := unsigned_1_neg (only parsing).

Lemma unsigned_1_cases {m} : @to_Z m one =
  if 2 <=? m then 1 else if m =? 1 then 0 else m+1.
Proof.
  case (Z.leb_spec 2 m); auto using unsigned_1_pos.
  case (Z.eqb_spec m 1) as [->|]; auto using unsigned_1_pos.
  auto using unsigned_1_neg with zarith.
Qed.
Notation to_Z_1_cases := unsigned_1_cases (only parsing).

Lemma gcd_1_m {m} : Z.gcd (@one m) m = 1.
Proof. cbv [one]; rewrite Zmod.to_Z_of_Z, Z.gcd_mod_l, Z.gcd_1_l; trivial. Qed.

Lemma signed_1 {m} (Hm : 3 <= m) : @signed m one = 1.
Proof.
  cbv [one]; rewrite signed_of_Z, Z.smod_small;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_1_1 : @signed 1 one = 0. Proof. trivial. Qed.

Lemma signed_1_2 : @signed 2 one = -1. Proof. trivial. Qed.

Lemma unsigned_nz {m} (x : Zmod m) (H : x <> zero) : to_Z x <> 0.
Proof. intros X; apply H, to_Z_inj. rewrite X; trivial. Qed.
Notation to_Z_nz := unsigned_nz (only parsing).

Lemma one_eq_zero_mod_1 : @one 1 = zero. Proof. trivial. Qed.

Lemma one_eq_zero_iff {m} : one = zero :> Zmod m <-> Z.abs m = 1.
Proof.
  cbv [one zero].
  rewrite <-unsigned_inj_iff, unsigned_of_Z, unsigned_of_small_Z.
  rewrite <-(Zmod_0_l m), <-Z.eq_mod_abs.
  assert (Z.abs m = 0 \/ Z.abs m = 1 \/ 1 < Z.abs m) by lia.
  intuition try (Z.to_euclidean_division_equations; lia).
  rewrite !Z.mod_small in *; lia.
Qed.

Lemma one_neq_zero {m} (Hm : 2 <= Z.abs m) : one <> zero :> Zmod m.
Proof. rewrite one_eq_zero_iff; lia. Qed.

Lemma of_Z_nz {m} x (H : x mod m <> 0) : of_Z m x <> zero.
Proof.
  intro Hx. apply (f_equal to_Z) in Hx. rewrite to_Z_of_Z, to_Z_0 in Hx; contradiction.
Qed.

Lemma hprop_Zmod_1 (a b : Zmod 1) : a = b.
Proof.
  pose proof to_Z_range a; pose proof to_Z_range b; apply to_Z_inj; lia.
Qed.

Lemma hprop_Zmod_m1 (a b : Zmod (-1)) : a = b.
Proof.
  pose proof to_Z_range a; pose proof to_Z_range b; apply to_Z_inj; lia.
Qed.

Lemma unsigned_Zmod1 (a : Zmod 1) : to_Z a = 0.
Proof. pose proof to_Z_range a; lia. Qed.
Notation to_Z_Zmod1 := unsigned_Zmod1 (only parsing).

Lemma unsigned_Zmodm1 (a : Zmod (-1)) : to_Z a = 0.
Proof. pose proof to_Z_range a; lia. Qed.
Notation to_Z_Zmodm1 := unsigned_Zmodm1 (only parsing).

Lemma signed_Zmod1 (a : Zmod 1) : signed a = 0.
Proof. pose proof signed_pos_bound a; lia. Qed.

Lemma signed_Zmodm1 (a : Zmod (-1)) : signed a = 0.
Proof. pose proof signed_neg_bound a; lia. Qed.

Lemma wlog_eq_Zmod_2_pos {m} (a b : Zmod m) (Hm : 0 < m) (k : 2 <= m -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec 1 m) as [e|ne].
  { destruct e; auto using hprop_Zmod_1. }
  { apply k; lia. }
Qed.

Lemma wlog_eq_Zmod_2_neg {m} (a b : Zmod m) (Hm : m < 0) (k : m <= -2 -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec (-1) m) as [e|ne].
  { destruct e; auto using hprop_Zmod_m1. }
  { apply k; lia. }
Qed.

Lemma wlog_eq_Zmod_2_abs {m} (a b : Zmod m) (k : m = 0 \/ 2 <= Z.abs m -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec m 0) as [z|nz]; [apply k, or_introl, z|].
  destruct (Z.ltb_spec 0 m); [apply wlog_eq_Zmod_2_pos|apply wlog_eq_Zmod_2_neg];
    intros; try apply k; lia.
Qed.

(** ** Ring operations *)

Lemma unsigned_add {m} (x y : Zmod m) : to_Z (add x y) = (to_Z x + to_Z y) mod m.
Proof.
  pose proof to_Z_range x; pose proof to_Z_range y.
  cbv [add]. rewrite of_small_Z_ok, to_Z_of_Z.
  case (Z.ltb_spec (Z.abs (x + y)) (Z.abs m)) as [?|?]; trivial.
  rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq 1) by lia; lia.
Qed.
Notation to_Z_add := unsigned_add (only parsing).

Lemma eqb_spec {m} (x y : Zmod m) : BoolSpec (x = y) (x <> y) (eqb x y).
Proof.
  cbv [eqb]. case (Z.eqb_spec (to_Z x) (to_Z y));
    constructor; auto using to_Z_inj; congruence.
Qed.

Lemma eqb_eq {m} (x y : Zmod m) : eqb x y = true <-> x = y.
Proof. destruct (eqb_spec x y); intuition congruence. Qed.

Lemma eqb_refl {m} (x : Zmod m) : eqb x x = true.
Proof. apply eqb_eq; trivial. Qed.

Lemma signed_add {m} x y : signed (@add m x y) = Z.smodulo (signed x+signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_add, Z.smod_mod, Z.smod_idemp_add; trivial. Qed.

Lemma of_Z_add {m} (x y : Z) : of_Z m (Z.add x y) = add (of_Z m x) (of_Z m y).
Proof.
  apply to_Z_inj.
  rewrite to_Z_add, ?to_Z_of_Z, ?Zplus_mod_idemp_r, ?Zplus_mod_idemp_l; auto.
Qed.

Lemma unsigned_sub {m} (x y : Zmod m) : to_Z (sub x y) = (to_Z x - to_Z y) mod m.
Proof.
  pose proof to_Z_range x; pose proof to_Z_range y.
  cbv [sub]. rewrite of_small_Z_ok, to_Z_of_Z.
  case Z.eqb eqn:?; rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq (-1)) by lia; lia.
Qed.
Notation to_Z_sub := unsigned_sub (only parsing).

Lemma signed_sub {m} x y : signed (@sub m x y) = Z.smodulo (signed x-signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_sub, Z.smod_mod, Z.smod_idemp_sub; trivial. Qed.

Lemma of_Z_sub {m} (x y : Z) : of_Z m (Z.sub x y) = sub (of_Z m x) (of_Z m y).
Proof.
  apply to_Z_inj.
  rewrite to_Z_sub, ?to_Z_of_Z, ?Zminus_mod_idemp_r, ?Zminus_mod_idemp_l; auto.
Qed.

Lemma unsigned_opp {m} (x : Zmod m) : to_Z (opp x) = (- to_Z x) mod m.
Proof. apply to_Z_sub. Qed.
Notation to_Z_opp := unsigned_opp (only parsing).

Lemma signed_opp {m} x : signed (@opp m x) = Z.smodulo (-signed x) m.
Proof. rewrite <-!smod_unsigned, to_Z_opp, Z.smod_mod, Z.smod_idemp_opp; trivial. Qed.

Lemma unsigned_m1 {m : Z} : @to_Z m (opp one) = -1 mod m.
Proof. rewrite to_Z_opp, to_Z_1. apply (Znumtheory.mod_opp_mod_opp (-1)). Qed.

Lemma unsigned_m1_pos {m : Z} (H : 2 <= m) : @to_Z m (opp one) = m-1.
Proof. rewrite to_Z_opp, Z_mod_nz_opp_full; rewrite mod_to_Z, ?to_Z_1_pos; lia. Qed.
Notation to_Z_m1_pos := unsigned_m1_pos (only parsing).

Lemma unsigned_m1_1 : @to_Z 1 (opp one) = 0. Proof. trivial. Qed.
Notation to_Z_m1_1 := unsigned_m1_1 (only parsing).

Lemma unsigned_m1_m1 : @to_Z (-1) (opp one) = 0. Proof. trivial. Qed.
Notation to_Z_m1_m1 := unsigned_m1_m1 (only parsing).

Lemma unsigned_m1_neg {m : Z} (H : m <= -2) : @to_Z m (opp one) = -1.
Proof. rewrite to_Z_opp, to_Z_1_neg, (Z.mod_diveq (-1)); lia. Qed.
Notation to_Z_m1_neg := unsigned_m1_neg (only parsing).

Lemma unsigned_m1_cases {m} : @to_Z m (opp one) =
  if (m <=? -2) || (m =? 0) then -1
  else if Z.abs m =? 1 then 0
  else m-1.
Proof.
  case (Z.leb_spec m (-2)) as []; auto using to_Z_m1_neg.
  case (Z.eqb_spec m 0) as [->|]; auto using to_Z_of_Z_mod0.
  case (Z.eqb_spec (Z.abs m) 1) as [|].
  { assert (m = 1 \/ m = -1) as [->| ->] by lia; trivial. }
  apply to_Z_m1_pos; lia.
Qed.
Notation to_Z_m1_cases := unsigned_m1_cases (only parsing).

Lemma of_Z_m1 {m} : @of_Z m (-1) = opp one.
Proof.
  rewrite <-of_Z_to_Z.
  apply of_Z_inj_cases; split; intros; subst; trivial; subst m'.
  rewrite to_Z_opp, Z.mod_mod_abs'.
  cbv [one]; change (-1) with (-(1)).
  rewrite to_Z_of_Z, 2 Z.mod_opp_l_nz; rewrite ?Z.mod_mod_abs', ?Z.mod_small; try lia.
Qed.

Lemma signed_m1 {m} (Hm : 2 <= m) : @signed m (opp one) = -1.
Proof.
  destruct (Z.eq_dec m 2) as [->|]; trivial.
  rewrite signed_opp, signed_1, Z.smod_small; Z.to_euclidean_division_equations; lia.
Qed.

Lemma of_Z_opp {m} (x : Z) : of_Z m (Z.opp x) = opp (of_Z m x).
Proof. cbv [opp]. rewrite <-Z.sub_0_l, of_Z_sub, of_Z_0; trivial. Qed.

Lemma opp_zero {m} : @opp m zero = zero.
Proof. apply to_Z_inj. rewrite to_Z_opp, to_Z_0, Zmod_0_l; trivial. Qed.

Lemma opp_overflow {m} (Hm : m mod 2 = 0)
  (x : Zmod m) (Hx : signed x = -m/2) : opp x = x.
Proof.
  apply signed_inj. rewrite signed_opp.
  rewrite (Z.smod_diveq 1); Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_opp_odd {m} (x : Zmod m) (H : m mod 2 = 1) :
  signed (opp x) = Z.opp (signed x).
Proof.
  pose proof signed_range x.
  rewrite signed_opp, (Z.smod_diveq 0); try lia.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_opp_small {m} (x : Zmod m) (H : signed x = -m/2 -> m mod 2 = 1) :
  signed (opp x) = Z.opp (signed x).
Proof.
  rewrite signed_opp.
  case (Z.eq_dec m 0) as [->|]; [apply Z.smod_0_r|].
  apply Z.smod_small_iff; pose proof signed_range x.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma unsigned_mul {m} (x y : Zmod m) : to_Z (mul x y) = (to_Z x * to_Z y) mod m.
Proof. cbv [mul]; rewrite ?to_Z_of_Z; trivial. Qed.
Notation to_Z_mul := unsigned_mul (only parsing).

Lemma signed_mul {m} x y : signed (@mul m x y) = Z.smodulo (signed x*signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_mul, Z.smod_mod, Z.smod_idemp_mul; trivial. Qed.

Lemma of_Z_mul {m} (x y : Z) : of_Z m (Z.mul x y) = mul (of_Z m x) (of_Z m y).
Proof.
  apply to_Z_inj.
  rewrite to_Z_mul, ?to_Z_of_Z, ?Zmult_mod_idemp_r, ?Zmult_mod_idemp_l; auto.
Qed.

Local Ltac r := try apply to_Z_inj; cbv [one];
  (* Note: rewrite is slow, and autorewrite isn't faster *)
  repeat rewrite ?to_Z_of_Z, ?to_Z_add, ?to_Z_mul, ?to_Z_sub, ?to_Z_opp,
    ?mod_to_Z, ?Zmod_0_l, ?Z.mul_1_l, ?Z.add_0_l, ?Zplus_mod_idemp_l,
    ?Zplus_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r,
    ?Z.add_opp_diag_r, ?to_Z_0;
  try (f_equal; lia).

Lemma add_0_l {m} a : @add m zero a = a. Proof. r. Qed.
Lemma add_comm {m} a b : @add m a b = add b a. Proof. r. Qed.
Lemma mul_comm {m} a b : @mul m a b = mul b a. Proof. r. Qed.
Lemma add_assoc {m} a b c : @add m a (add b c) = add (add a b) c. Proof. r. Qed.
Lemma mul_assoc {m} a b c : @mul m a (mul b c) = mul (mul a b) c. Proof. r. Qed.
Lemma mul_add_l {m} a b c : @mul m (add a b) c = add (mul a c) (mul b c). Proof. r. Qed.
Lemma mul_1_l {m} a : @mul m one a = a. Proof. r. Qed.
Lemma add_opp_r {m} a b : @add m a (opp b) = sub a b. Proof. r. Qed.
Lemma add_opp_same_r {m} a : @add m a (opp a) = zero. Proof. r. Qed.

Lemma sub_same {m} a : @sub m a a = zero.
Proof. rewrite <-add_opp_r, add_opp_same_r; trivial. Qed.

Lemma ring_theory m : @ring_theory (Zmod m) zero one add mul sub opp eq.
Proof. split; auto using eq_sym, add_0_l, add_comm, mul_comm, add_assoc, mul_assoc, mul_add_l, mul_1_l, add_opp_r, add_opp_same_r. Qed.

Section WithRing.
  Context {m : Z}.
  Add Ring __Private__Zmod_base_ring : (ring_theory m).
  Implicit Types a b c : Zmod m.
  Lemma opp_0 : opp zero = zero :> Zmod m. Proof. ring. Qed.
  Lemma add_0_r a : add a zero = a. Proof. ring. Qed.
  Lemma sub_0_l a : sub zero a = opp a. Proof. ring. Qed.
  Lemma sub_0_r a : sub a zero = a. Proof. ring. Qed.
  Lemma mul_1_r a : mul a one = a. Proof. ring. Qed.
  Lemma mul_m1_l a : mul (opp one) a = opp a. Proof. ring. Qed.
  Lemma mul_m1_r a : mul a (opp one) = opp a. Proof. ring. Qed.
  Lemma mul_0_l a : mul zero a = zero. Proof. ring. Qed.
  Lemma mul_0_r a : mul a zero = zero. Proof. ring. Qed.
  Lemma opp_opp a : opp (opp a) = a. Proof. ring. Qed.
  Lemma opp_inj a b : opp a = opp b -> a = b. Proof. intros H; ring [H]. Qed.
  Lemma opp_inj_iff a b : opp a = opp b <-> a = b. Proof. split. apply opp_inj. congruence. Qed.
  Lemma add_opp_l a b : add (opp a) b = sub b a. Proof. ring. Qed.
  Lemma sub_opp_r a b : sub a (opp b) = add a b. Proof. ring. Qed.
  Lemma sub_opp_l a b : sub (opp a) b = opp (add a b). Proof. ring. Qed.
  Lemma add_sub_r a b c : add a (sub b c) = sub (add a b) c. Proof. ring. Qed.
  Lemma add_sub_l a b c : add (sub a b) c = sub (add a c) b. Proof. ring. Qed.
  Lemma sub_sub_r a b c : sub a (sub b c) = sub (add a c) b. Proof. ring. Qed.
  Lemma sub_sub_l a b c : sub (sub a b) c = sub a (add b c). Proof. ring. Qed.
  Lemma mul_add_r a b c : mul a (add b c) = add (mul a b) (mul a c). Proof. ring. Qed.
  Lemma add_opp_same_l a : @add m (opp a) a = zero. Proof. ring. Qed.
  Lemma mul_sub_l a b c : mul (sub a b) c = sub (mul a c) (mul b c). Proof. ring. Qed.
  Lemma mul_sub_r a b c : mul a (sub b c) = sub (mul a b) (mul a c). Proof. ring. Qed.
  Lemma mul_opp_l a b : mul (opp a) b = opp (mul a b). Proof. ring. Qed.
  Lemma mul_opp_r a b : mul a (opp b) = opp (mul a b). Proof. ring. Qed.
  Lemma mul_opp_opp a b : mul (opp a) (opp b) = mul a b. Proof. ring. Qed.
  Local Lemma square_roots_opp_prime_subproof a b :
    sub (mul a a) (mul b b) = mul (sub a (opp b)) (sub a b). Proof. ring. Qed.
End WithRing.

(** ** Properties of division operators *)

Lemma udiv_0_r {m} x : @udiv m x zero = opp one.
Proof. cbv [udiv]. pose proof to_Z_0 m. case Z.eq_dec as []; congruence. Qed.

Lemma unsigned_udiv {m} (x y : Zmod m) (Hy : y <> 0 :> Z) : to_Z (@udiv m x y) = Z.div x y mod m.
Proof.
  cbv [udiv]; case Z.eq_dec as []; [lia|].
  pose proof unsigned_range x.
  pose proof unsigned_range y.
  rewrite to_Z_of_small_Z.
  destruct m as [|m|m]; cbn [Z.sgn Z.opp]; intuition try lia.
  { case Z.eqb; rewrite Zmod_0_r, ?Z.add_0_r; trivial. }
  { case Z.eqb eqn:?; [|rewrite Z.mod_small]; Z.to_euclidean_division_equations; nia. }
  case (Z.eqb_spec (Z.sgn (x/y)) 1) as []; trivial.
  rewrite (Z.mod_diveq (-1)); Z.to_euclidean_division_equations; nia.
  rewrite (Z.mod_diveq 0); Z.to_euclidean_division_equations; nia.
Qed.
Notation to_Z_udiv := unsigned_udiv (only parsing).

Lemma unsigned_udiv_nonneg {m} (x y : Zmod m) (Hm : 0 <= m) (Hy : y <> 0 :> Z) : to_Z (@udiv m x y) = Z.div x y.
Proof.
  rewrite to_Z_udiv by trivial.
  pose proof unsigned_range x.
  pose proof unsigned_range y.
  destruct m as [|m|m]; [apply Zmod_0_r| |lia].
  apply Z.mod_small; Z.to_euclidean_division_equations; nia.
Qed.
Notation to_Z_udiv_nonneg := unsigned_udiv_nonneg (only parsing).

Lemma of_Z_div_small {m} (x y : Z) (Hx : 0 <= x < m) (Hy : 0 < y < m) :
  of_Z m (x / y) = udiv (of_Z _ x) (of_Z _ y).
Proof.
  apply to_Z_inj; rewrite ?to_Z_udiv; rewrite ?to_Z_of_Z, ?Z.mod_small;
    Z.to_euclidean_division_equations; nia.
Qed.

Lemma unsigned_umod {m} x y : to_Z (@umod m x y) = Z.modulo x y.
Proof. apply to_Z_of_small_Z. Qed.
Notation to_Z_umod := unsigned_umod (only parsing).

Lemma of_Z_umod_small {m} (x y : Z) (Hx : 0 <= x < m) (Hy : 0 <= y < m) :
  of_Z m (x mod y) = umod (of_Z _ x) (of_Z _ y).
Proof.
  apply to_Z_inj; rewrite ?to_Z_umod; rewrite ?to_Z_of_Z, ?(Z.mod_small _ m);
    Z.to_euclidean_division_equations; nia.
Qed.

Lemma umod_0_r {m} x : @umod m x zero = x.
Proof. cbv [umod]. apply to_Z_inj. rewrite to_Z_of_small_Z, to_Z_0, Zmod_0_r; trivial. Qed.

Lemma signed_squot {m} x y : @signed m (squot x y) =
  Z.smodulo (if signed y =? 0 then -1 else signed x ÷ signed y) m.
Proof. apply signed_of_Z. Qed.

Lemma signed_squot_nz {m} x y : signed y <> 0 -> @signed m (squot x y) = Z.smodulo (signed x ÷ signed y) m.
Proof. cbv [squot]. rewrite signed_of_Z. case (signed y); trivial; congruence. Qed.

Lemma signed_srem {m} x y : @signed m (srem x y) = Z.smodulo (Z.rem (signed x) (signed y)) m.
Proof. apply signed_of_Z. Qed.

Lemma squot_0_r {m} x : @squot m x zero = opp one.
Proof. cbv [squot]. rewrite signed_0, of_Z_m1; trivial. Qed.

Lemma smod_0_r {m} x : @srem m x zero = x.
Proof. cbv [srem]. apply signed_inj. rewrite signed_of_Z, signed_0, Z.rem_0_r_ext, smod_signed; trivial. Qed.

Lemma signed_squot_small {m} x y (Hm : 0 <= m) (Hy : signed y <> 0) :
  ~ (signed x = -m/2 /\ signed y = -1 /\ m mod 2 = 0) ->
  @signed m (squot x y) = signed x ÷ signed y.
Proof.
  intros H; rewrite signed_squot_nz by trivial.
  pose proof signed_range x; pose proof signed_range y.
  case (Z.eqb_spec m 0) as [->|]; auto using Z.smod_0_r.
 apply Z.smod_small; Z.to_euclidean_division_equations; nia.
Qed.

Lemma squot_overflow {m} x y
  (Hm : m mod 2 = 0) (Hx : signed x = -m/2) (Hy : signed y = -1) :
  @squot m x y = x.
Proof.
  apply signed_inj; rewrite signed_squot_nz, Hx, Hy by lia.
  rewrite (Z.smod_diveq 1); Z.to_euclidean_division_equations; nia.
Qed.

Lemma squot_m1_r {m} (x : Zmod m) (Hm : 0 < m) : @squot m x (opp one) = opp x.
Proof.
  eapply wlog_eq_Zmod_2_pos; trivial; intro Hm'.
  apply signed_inj.
  rewrite signed_squot_nz; rewrite ?signed_m1; try lia.
  change (-1) with (Z.opp 1); rewrite Z.quot_opp_r, Z.quot_1_r by lia.
  rewrite signed_opp; trivial.
Qed.

Lemma unsigned_inv {m} x : to_Z (@inv m x) = Znumtheory.invmod x m.
Proof. apply to_Z_of_small_Z. Qed.
Notation to_Z_inv := unsigned_inv (only parsing).

Lemma inv_0 {m} : @inv m zero = zero.
Proof. apply to_Z_inj, to_Z_of_small_Z. Qed.

Lemma unsigned_mdiv {m} x y : to_Z (@mdiv m x y) = x * Znumtheory.invmod y m mod m.
Proof. cbv [mdiv]. rewrite to_Z_mul, to_Z_inv; trivial. Qed.
Notation to_Z_mdiv := unsigned_mdiv (only parsing).

Lemma mdiv_0_r {m} x : @mdiv m x zero = zero.
Proof. cbv [mdiv]. rewrite inv_0, mul_0_r; trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = mdiv x y.
Proof. apply to_Z_inj. cbv [mdiv inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r {m} x y : mul x (@inv m y) = mdiv x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

(** ** Bitwise operations *)
Import Nbitwise.

Lemma unsigned_and {m} x y : @to_Z m (and x y) = Z.land x y mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_and := unsigned_and (only parsing).

Lemma unsigned_and_small {m} (Hm : 0 <= m) x y : @to_Z m (and x y) = Z.land x y.
Proof.
  rewrite to_Z_and.
  case (Z.eqb_spec m 0) as [->|]; auto using Zmod_0_r.
  apply Z.mod_small.
  pose proof to_Z_range x; pose proof to_Z_range y.
  pose proof N.land_mono (Z.to_N x) (Z.to_N y).
  pose proof N2Z.inj_land (Z.to_N x) (Z.to_N y).
  rewrite 2Z2N.id in *; try apply to_Z_range; intuition try lia.
Qed.
Notation to_Z_and_small := unsigned_and_small (only parsing).

Lemma unsigned_ndn {m} x y : @to_Z m (ndn x y) = Z.ldiff x y mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_ndn  := unsigned_ndn (only parsing).

Lemma unsigned_ndn_small {m} x y (Hm : 0 <= m) : @to_Z m (ndn x y) = Z.ldiff x y.
Proof.
  rewrite to_Z_ndn.
  case (Z.eqb_spec m 0) as [->|]; auto using Zmod_0_r.
  apply Z.mod_small.
  pose proof to_Z_range x; pose proof to_Z_range y.
  pose proof N.ldiff_mono (Z.to_N x) (Z.to_N y).
  pose proof N2Z.inj_ldiff (Z.to_N x) (Z.to_N y).
  rewrite 2Z2N.id in *; try apply to_Z_range; intuition try lia.
Qed.
Notation to_Z_ndn_small := unsigned_ndn_small (only parsing).

(** ** Shifts *)

Lemma unsigned_sru {m} x n : @to_Z m (sru x n) = Z.shiftr x n mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_sru := unsigned_sru (only parsing).

Lemma unsigned_sru_small {m} x n (Hm : 0 <= m) (Hn : 0 <= n) : @to_Z m (sru x n) = Z.shiftr x n.
Proof.
  rewrite to_Z_sru.
  case (Z.eqb_spec m 0) as [->|]; auto using Zmod_0_r.
  apply Z.mod_small; pose proof (to_Z_range x).
  rewrite Z.shiftr_div_pow2; Z.to_euclidean_division_equations; nia.
Qed.
Notation to_Z_sru_small := unsigned_sru_small (only parsing).

(* TODO
Lemma signed_srs {m} x n : @signed m (srs x n) = Z.shiftr (signed x) n.
Proof.
  cbv [srs]; rewrite signed_of_Z; apply Z.smod_small.
  rewrite Z.shiftr_div_pow2 by lia; pose proof signed_range x.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma unsigned_srs {m} x n : @to_Z m (srs x n) = Z.shiftr (signed x) n mod m.
Proof. rewrite <-mod_to_Z, <-Z.mod_smod, <-signed_srs, <-signed_of_Z, of_Z_to_Z; trivial. Qed.
Notation to_Z_srs := unsigned_srs (only parsing).
*)

Lemma unsigned_slu {m} x n : @to_Z m (slu x n) = Z.shiftl x n mod m.
Proof. cbv [slu]; rewrite to_Z_of_Z; trivial. Qed.
Notation to_Z_slu := unsigned_slu (only parsing).


(** ** Lemmas for equalities with different moduli *)

Lemma unsigned_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_Z a = to_Z b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_Z_inj. Qed.
Notation to_Z_inj_dep := unsigned_inj_dep (only parsing).

Lemma unsigned_inj_dep_iff {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n /\ to_Z a = to_Z b <-> existT _ _ a = existT _ _ b.
Proof.
  split. { intros []; auto using to_Z_inj_dep. }
  intros H; inversion_sigma; subst; auto.
Qed.
Notation to_Z_inj_dep_iff := unsigned_inj_dep_iff (only parsing).

Lemma unsigned_eq_rect {m} (a : Zmod m) n p : to_Z (eq_rect _ _ a n p) = to_Z a.
Proof. case p; trivial. Qed.
Notation to_Z_eq_rect := unsigned_eq_rect (only parsing).

Lemma signed_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> signed a = signed b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, signed_inj. Qed.

Lemma signed_inj_dep_iff {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n /\ signed a = signed b <-> existT _ _ a = existT _ _ b.
Proof.
  split. { intros []; auto using signed_inj_dep. }
  intros H; inversion_sigma; subst; auto.
Qed.

Lemma signed_eq_rect {m} (a : Zmod m) n p : signed (eq_rect _ _ a n p) = signed a.
Proof. case p; trivial. Qed.


(** ** [pow] *)

Lemma pow_0_r {m} x : @pow m x 0 = one.
Proof. trivial. Qed.

Lemma pow_1_r {m} x : @pow m x 1 = x.
Proof. trivial. Qed.

Lemma pow_2_r {m} x : @pow m x 2 = mul x x.
Proof. trivial. Qed.

Local Notation pow_N := ZmodDef.Zmod.Private_pow_N.

Lemma Private_pow_nonneg {m} (x : Zmod m) z (Hz : 0 <= z) : pow x z = pow_N x (Z.to_N z).
Proof. cbv [pow]; case (Z.ltb_spec z 0) as []; trivial; lia. Qed.

Lemma Private_pow_neg {m} (x : Zmod m) z (Hz : z < 0) : pow x z = inv (pow_N x (Z.to_N (-z))).
Proof. cbv [pow]; case (Z.ltb_spec z 0) as []; trivial; lia. Qed.

Lemma pow_neg {m} (x : Zmod m) z (Hz : z < 0) : pow x z = inv (pow x (-z)).
Proof. rewrite Private_pow_neg, Private_pow_nonneg by lia; trivial. Qed.

Lemma Private_pow_N_correct {m} a n : @pow_N m a n = N.iter n (mul a) one.
Proof. apply N.iter_op_correct; auto using mul_1_r, mul_assoc. Qed.

Lemma Private_pow_N_0_r {m} (x : Zmod m) : @pow_N m x 0 = one.
Proof. rewrite Private_pow_N_correct; reflexivity. Qed.

Lemma Private_pow_N_succ_r {m} (x : Zmod m) n : pow_N x (N.succ n) = mul x (pow_N x n).
Proof. rewrite !Private_pow_N_correct, N.iter_succ; trivial. Qed.

Lemma pow_succ_nonneg_r {m} (x : Zmod m) n (H : 0 <= n) : pow x (Z.succ n) = mul x (pow x n).
Proof.
  cbv [pow].
  case (Z.ltb_spec (Z.succ n) 0), (Z.ltb_spec n 0); try lia.
  rewrite Z2N.inj_succ, Private_pow_N_succ_r; trivial; lia.
Qed.
Notation pow_succ_r_nonneg := pow_succ_nonneg_r.

Lemma pow_add_r_nonneg {m} (x : Zmod m) a b (Ha : 0 <= a) (Hb : 0 <= b) :
  pow x (a+b) = mul (pow x a) (pow x b).
Proof.
  generalize dependent b; generalize dependent a; refine (natlike_ind _ _ _).
  { intros; rewrite Z.add_0_l, pow_0_r, mul_1_l; trivial. }
  intros a Ha IH b Hb.
  rewrite ?Z.add_succ_l, ?Z.add_pred_l, ?pow_succ_nonneg_r, ?IH, ?mul_assoc by lia; trivial.
Qed.

Lemma pow_mul_l_nonneg {m} (x y : Zmod m) n (Hn : 0 <= n) :
  pow (mul x y) n = mul (pow x n) (pow y n).
Proof.
  revert y; revert x; generalize dependent n; refine (natlike_ind _ _ _).
  { intros. rewrite ?pow_0_r, ?mul_1_r; trivial. }
  intros a Ha IH b Hb.
  rewrite ?Z.add_succ_l, ?Z.add_pred_l, ?pow_succ_nonneg_r, ?IH by lia; trivial.
  rewrite ?mul_assoc; f_equal; rewrite <-?mul_assoc; f_equal; auto using mul_comm.
Qed.

Local Coercion Z.of_N : N >-> Z.
Lemma Private_to_Z_pow_N {m} x n : @to_Z m (pow_N x n) = to_Z x ^ n mod m.
Proof.
  revert x; induction n using N.peano_ind; intros; try apply to_Z_of_small_Z.
  rewrite  ?Private_pow_N_succ_r, ?to_Z_mul,
    ?N2Z.inj_succ, ?Z.pow_succ_r, ?IHn, ?Zmult_mod_idemp_r; trivial; lia.
Qed.

Lemma unsigned_pow_nonneg_r {m} x z (Hz : 0 <= z) : @to_Z m (pow x z) = x^z mod m.
Proof. rewrite Private_pow_nonneg, Private_to_Z_pow_N; f_equal; f_equal; lia. Qed.
Notation to_Z_pow_nonneg_r := unsigned_pow_nonneg_r (only parsing).

Lemma unsigned_pow_neg_r {m} x z (Hz : z < 0) : @to_Z m (pow x z) = Znumtheory.invmod (to_Z x^(-z)) m.
Proof.
  rewrite pow_neg, to_Z_inv, to_Z_pow_nonneg_r by lia.
  rewrite Znumtheory.invmod_mod_l; f_equal; f_equal; lia.
Qed.
Notation to_Z_pow_neg_r := unsigned_pow_neg_r (only parsing).

Lemma signed_pow_nonneg_r {m} x z (Hz : 0 <= z) : @signed m (pow x z) = Z.smodulo (signed x ^ z) m.
Proof.
  rewrite <-!smod_unsigned, to_Z_pow_nonneg_r, Z.smod_mod, Z.smod_pow_l; trivial.
Qed.
Notation signed_pow_nonneg := signed_pow_nonneg_r.

Lemma of_Z_pow {m} x n (H : 0 <= n) : of_Z m (x ^ n) = pow (of_Z m x) n.
Proof.
  apply to_Z_inj. rewrite to_Z_pow_nonneg_r, !to_Z_of_Z, Z.mod_pow_l; trivial.
Qed.

Lemma Private_pow_N_0_l {m} n (Hn : n <> 0%N) : @pow_N m zero n = zero.
Proof. apply to_Z_inj; rewrite Private_to_Z_pow_N, to_Z_0, ?Z.pow_0_l; trivial; lia. Qed.

Lemma pow_0_l {m} n (Hn : n <> 0) : @pow m zero n = zero.
Proof. cbv [pow]; case Z.ltb eqn:?; rewrite Private_pow_N_0_l, ?inv_0 by lia; auto. Qed.


(** ** Misc *)

Lemma sub_eq_0 {m} a b (H : @sub m a b = zero) : a = b.
Proof.
  apply (f_equal to_Z) in H.
  rewrite to_Z_sub in H. eapply Znumtheory.cong_iff_0 in H.
  rewrite 2 mod_to_Z in *; auto using to_Z_inj.
Qed.

Lemma sub_eq_0_iff {m} a b : @sub m a b = zero <-> a = b.
Proof. split; try apply sub_eq_0. intros; subst; try apply sub_same. Qed.

Lemma add_eq_0 {m} a b (H : @add m a b = zero) : b = opp a.
Proof.
  rewrite <-(opp_opp a), add_opp_l in H.
  apply sub_eq_0 in H; trivial.
Qed.

Lemma add_eq_0_iff {m} a b : @add m a b = zero <-> b = opp a.
Proof. split; try apply add_eq_0. intros ->. rewrite add_opp_r, sub_same; auto. Qed.

Lemma opp_1_neq_1 {m} (Hm : 3 <= Z.abs m) : @opp m one <> one.
Proof.
  intros H%(f_equal to_Z); rewrite to_Z_m1_cases, to_Z_1_cases in H.
  repeat match goal with
         | H : context [ Z.leb ?a ?b ] |- _ => destruct (Z.leb_spec a b) in *
         | H : context [ Z.eqb ?a ?b ] |- _ => destruct (Z.eqb_spec a b) in *
         | _ => progress cbn [andb orb] in *
         end; try lia.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  apply to_Z_inj. rewrite to_Z_inv, to_Z_1_cases.
  case Z.leb_spec; try case Z.eqb_spec; intros; trivial.
  { rewrite ?Znumtheory.invmod_1_l, ?Znumtheory.invmod_0_l, ?Z.mod_small by lia; trivial. }
  pose proof Znumtheory.invmod_mod_l 1 m.
  rewrite Znumtheory.invmod_1_l, (Z.mod_diveq (-1)) in * by lia.
  assert ((1 - m * -1) = m+1) by lia. congruence.
Qed.

Lemma mdiv_1_r {m} x : @mdiv m x one = x.
Proof. cbv [mdiv]. rewrite inv_1, mul_1_r; trivial. Qed.

(** ** Absolute value *)

Lemma abs_0 m : @abs m zero = zero.
Proof. cbv [abs]. rewrite signed_0; trivial. Qed.

Lemma abs_1 m : @abs m one = one.
Proof.
  cbv [abs signed].
  case (Z.ltb_spec (Z.double _) _); case Z.ltb_spec; trivial; rewrite ?to_Z_1_cases;
    repeat case Z.leb_spec; repeat case Z.eqb_spec; try lia.
  intros; assert (2 = m) as <- by lia; trivial.
Qed.

Lemma abs_nonneg {m} x : 0 <= @signed m x -> abs x = x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_neg {m} x : @signed m x < 0 -> abs x = opp x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_pos {m} x : 0 < @signed m x -> abs x = x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_opp {m} x : @abs m (opp x) = abs x.
Proof.
  eapply signed_inj; case (Z.eqb_spec (signed x) (-m/2)) as []; cycle 1.
  2: case (Z.eqb_spec (m mod 2) 0) as []; cycle 1.
  1,2: cbv [abs]; rewrite ?opp_opp; repeat case Z.ltb_spec; intros; trivial;
    rewrite signed_opp_small in *; Z.to_euclidean_division_equations; lia.
  cbv [abs]; rewrite ?opp_opp; repeat case Z.ltb_spec; trivial;
  rewrite !opp_overflow; trivial; pose proof signed_range x; 
  intuition try (Z.to_euclidean_division_equations; nia).
Qed.

Lemma abs_abs {m} (x : Zmod m) : abs (abs x) = abs x.
Proof. unfold abs at 2; case Z.ltb; rewrite ?abs_opp; trivial. Qed.

Lemma signed_abs_small {m} x (H : signed x <> - m / 2) :
  @signed m (abs x) = Z.abs (signed x).
Proof.
  cbv [abs]; destruct (Z.ltb_spec (signed x) 0); [rewrite signed_opp_small|]; lia.
Qed.

Lemma signed_abs_odd {m} (Hm : m mod 2 = 1) x :
  @signed m (abs x) = Z.abs (signed x).
Proof.
  cbv [abs]; destruct (Z.ltb_spec (signed x) 0); [rewrite signed_opp_small|];
    (pose proof signed_range x; Z.div_mod_to_equations; nia).
Qed.

Lemma abs_overflow {m} (Hm : m mod 2 = 0)
  (x : Zmod m) (Hx : signed x = -m/2) : abs x = x.
Proof.
  cbv [abs]. rewrite Hx.
  case (Z.ltb_spec (-m/2) 0) as []; auto using opp_overflow.
Qed.

Lemma signed_abs_nonneg_small {m} (x : Zmod m) (H : signed x <> - m / 2):
  0 <= signed (abs x).
Proof. rewrite signed_abs_small; lia. Qed.

Lemma signed_abs_nonneg_odd {m} (Hm : m mod 2 = 1) (x : Zmod m) :
  0 <= signed (abs x).
Proof. rewrite signed_abs_odd; lia. Qed.

Lemma abs_mul_abs_l {m} (x y : Zmod m) : abs (mul (abs x) y) = abs (mul x y).
Proof.
  destruct (Z_lt_le_dec (signed x) 0); rewrite ?(abs_nonneg x), ?(abs_neg x) by lia;
  rewrite ?mul_opp_opp, ?mul_opp_l, ?mul_opp_r, ?abs_opp; trivial.
Qed.

Lemma abs_mul_abs_r {m} (x y : Zmod m) : abs (mul x (abs y)) = abs (mul x y).
Proof.
  destruct (Z_lt_le_dec (signed y) 0); rewrite ?(abs_nonneg y), ?(abs_neg y) by lia;
  rewrite ?mul_opp_opp, ?mul_opp_l, ?mul_opp_r, ?abs_opp; trivial.
Qed.

Lemma abs_mul_abs_abs {m} (x y : Zmod m) : abs (mul (abs x) (abs y)) = abs (mul x y).
Proof. rewrite ?abs_mul_abs_l, ?abs_mul_abs_r; trivial. Qed.

Lemma gcd_opp_m {m} x : Z.gcd (@opp m x) m = Z.gcd x m.
Proof. rewrite to_Z_opp, Z.gcd_mod_l, Z.gcd_opp_l; try lia. Qed.

Lemma gcd_abs_m_odd {m} (Hm : m mod 2 = 1) x :
  Z.gcd (@abs m x) m = Z.gcd x m.
Proof. rewrite <-2mod_signed, 2Z.gcd_mod_l, signed_abs_odd, Z.gcd_abs_l; lia. Qed.

Lemma pow_opp_2 {m} (x : Zmod m) : pow (opp x) 2 = pow x 2.
Proof. rewrite !pow_2_r. rewrite ?mul_opp_opp; trivial. Qed.

Lemma pow_abs_2 {m} (x : Zmod m) : pow (abs x) 2 = pow x 2.
Proof. rewrite !pow_2_r. cbv [abs]; case Z.ltb; rewrite ?mul_opp_opp; trivial. Qed.

Lemma eq_abs_iff m (x y : Zmod m) : abs x = abs y <-> (y = x \/ y = opp x).
Proof.
  split.
  { cbv [abs]; do 2 case Z.ltb_spec; intros; subst; auto using opp_inj, opp_opp. }
  { intros [H|H]; apply (f_equal abs) in H; rewrite ?abs_opp in H; congruence. }
Qed.

(** Elements *)

Lemma length_elements m : length (elements m) = Z.abs_nat m.
Proof. cbv [elements]. rewrite List.length_map, List.length_seq; trivial. Qed.

Lemma nth_error_elements {m} n : List.nth_error (elements m) n =
  if (Nat.ltb n (Z.abs_nat m)) then Some (of_Z _ (Z.of_nat n)) else None.
Proof.
  cbv [elements].
  rewrite List.nth_error_map, List.nth_error_seq.
  case Nat.ltb; trivial.
Qed.

Lemma in_elements {m} a (Hm : m <> 0) : List.In a (elements m).
Proof.
  apply List.nth_error_In with (n:=Z.to_nat (a mod Z.abs m)).
  rewrite nth_error_elements. pose proof to_Z_range a.
  case Nat.ltb_spec; [|Z.to_euclidean_division_equations; lia]; intros.
  rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
  rewrite <-of_Z_mod, Z.mod_mod_abs, of_Z_mod, of_Z_to_Z; trivial.
Qed.

Lemma NoDup_elements m : List.NoDup (elements m).
Proof.
  cbv [elements].
  eapply List.NoDup_map_inv with (f := fun x : Zmod m => Z.to_nat (x mod (Z.abs m))).
  erewrite List.map_map, List.map_ext_in, List.map_id; trivial using List.seq_NoDup.
  intros a Ha. apply List.in_seq in Ha; cbn [Nat.add] in Ha.
  rewrite to_Z_of_Z, Z.mod_mod_abs', Z.mod_small, Nat2Z.id; lia.
Qed.

(* (* TODO *)
Lemma elements_by_sign m : elements m = [zero] ++ positives m ++ negatives m.
Proof.
  cbv [elements positives negatives].
  replace [zero] with (map (fun i => of_Z m (Z.of_nat i)) (seq O 1)) by reflexivity.
  rewrite <-!map_app, <-!seq_app.
  f_equal; f_equal. Z.div_mod_to_equations; nia.
Qed.

Lemma in_positives m x : In x (positives m) <-> 0 < signed x.
Proof.
  cbv [positives]. rewrite signed_pos_iff, in_map_iff; setoid_rewrite in_seq.
  split; [intros (?&<-&?)|eexists (Z.to_nat x); split]; auto using of_nat_to_nat;
  rewrite ?Z2Nat.id, ?to_Z_of_Z, ?of_Z_to_Z, ?Z.mod_small;
  trivial; Z.div_mod_to_equations; lia.
Qed.

Lemma in_negatives m x : In x (negatives m) <-> signed x < 0.
Proof.
  cbv [negatives]. rewrite signed_neg_iff, in_map_iff; setoid_rewrite in_seq.
  split; [intros (?&<-&?)|eexists (Z.to_nat x); split]; auto using of_nat_to_nat;
  rewrite ?Z2Nat.id, ?to_Z_of_Z, ?of_Z_to_Z, ?Z.mod_small; try pose proof to_Z_range x;
  trivial; Z.div_mod_to_equations; try nia.
Qed.

Lemma NoDup_positives m : NoDup (positives m).
Proof.
  pose proof NoDup_elements m as H; rewrite elements_by_sign in H.
  eauto using NoDup_app_remove_l, NoDup_app_remove_r.
Qed.

Lemma NoDup_negatives m : NoDup (negatives m).
Proof.
  pose proof NoDup_elements m as H; rewrite elements_by_sign in H.
  eauto using NoDup_app_remove_l, NoDup_app_remove_r.
Qed.

Lemma length_positives m : length (positives m) = Z.to_nat ((m-1)/2).
Proof. cbv [positives]. rewrite length_map, length_seq; trivial. Qed.

Lemma length_negatives m : length (negatives m) = Z.to_nat (m/2).
Proof. cbv [negatives]. rewrite length_map, length_seq; trivial. Qed.

Lemma negatives_as_positives_odd (m : positive) (Hm : m mod 2 = 1) :
  negatives m = map opp (rev (positives m)).
Proof.
  cbv [positives negatives]; rewrite <-map_rev, map_map.
  apply nth_error_ext; intros i; rewrite ?nth_error_map, ?nth_error_rev, ?nth_error_seq, ?length_seq.
  repeat match goal with
         |- context [Nat.ltb ?a ?b] => case (Nat.ltb_spec a b) as []
         end; trivial; try solve [zify; Z.div_mod_to_equations; lia].
  cbn [option_map]; f_equal; apply to_Z_inj; rewrite ?to_Z_opp, ?to_Z_of_Z.
  assert (Z.of_nat (1 + _) = - (Z.of_nat i - (m-1)/2)) as -> by lia.
  rewrite Znumtheory.mod_opp_mod_opp, Z.mod_small , (Z.mod_diveq (-1));
    zify; Z.div_mod_to_equations; nia.
Qed.
 *)

Lemma invertibles_prime p (H : Znumtheory.prime p) :
  invertibles p = List.tl (elements p).
Proof.
  cbv [invertibles elements]; pose proof Znumtheory.prime_ge_2 p H.
  replace (Z.abs_nat p) with (S (Z.to_nat p-1)) by lia;
    progress cbn [List.seq List.tl List.map List.filter].
  rewrite Z.gcd_0_l; destruct (Z.eqb_spec (Z.abs p) 1).
  { pose proof Znumtheory.prime_ge_2 p H; lia. }
  case Z.eqb_spec; intros; [lia|].
  erewrite filter_map_swap, filter_ext_in, filter_true; trivial; cbv beta.
  intros i ?%List.in_seq; apply Z.eqb_eq.
  eapply Znumtheory.Zgcd_1_rel_prime, Znumtheory.rel_prime_le_prime; trivial.
  rewrite Zmod.to_Z_of_Z, Z.mod_small; lia.
Qed.

Lemma length_invertibles_prime p (H : Znumtheory.prime p) :
  length (invertibles p) = Z.to_nat (p-1).
Proof.
  pose proof Znumtheory.prime_ge_2 p H.
  rewrite invertibles_prime, List.tl_length, Zmod.length_elements; trivial; lia.
Qed.

End Zmod.

Module bitvec.
Import Base.Zmod ZmodDef.Zmod ZmodDef.bitvec.

(** ** Specialized versions of [Zmod] lemmas *)

Notation to_Z_0 := to_Z_0 (only parsing).
Notation unsigned_0 := unsigned_0 (only parsing).

Lemma unsigned_1 {n : Z} (Hm : 1 <= n) : @to_Z (2^n) one = 1.
Proof. apply to_Z_1_pos; pose (Z.pow_le_mono_r 2 1 n); lia. Qed.
Notation to_Z_1 := unsigned_1 (only parsing).

Lemma signed_1 {n} (Hm : 2 <= n) : @signed (2^n) one = 1.
Proof. apply signed_1. transitivity (2^2); try apply Z.pow_le_mono_r; lia. Qed.

Lemma unsigned_m1 {n} : @to_Z (2^n) (opp one) = Z.ones n.
Proof.
  assert (2^n = 0 \/ 2^n = 1 \/ 2 <= 2^n) as [H|[H|H]] by lia.
  1,2 : rewrite to_Z_m1_cases; repeat case Z.eqb_spec;
    rewrite ?Bool.orb_false_r, ?Bool.orb_false_r, ?Z.ones_equiv, ?H; cbn; lia.
  rewrite to_Z_m1_pos, Z.ones_equiv; trivial.
Qed.
Notation to_Z_m1 := unsigned_m1 (only parsing).

Lemma signed_m1 {n} (Hm : 1 <= n) : @signed (2^n) (opp one) = -1.
Proof.
  apply signed_m1.
  apply (Z.pow_le_mono_r 2 1 n); trivial; exact eq_refl.
Qed.

Lemma one_neq_zero {n} (Hm : 1 <= n) : one <> zero :> bitvec n.
Proof. apply one_neq_zero. pose proof (Z.pow_le_mono_r 2 1 n); lia. Qed.

Lemma unsigned_of_Z {n} (z : Z) : to_Z (of_Z n z) = z mod 2^n.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_of_Z := unsigned_of_Z.

Lemma unsigned_of_Z_small {n} z (H : 0 <= z < 2^n) : to_Z (bitvec.of_Z n z) = z.
Proof. apply to_Z_of_Z_small, H. Qed.
Notation to_Z_of_Z_small := unsigned_of_Z_small (only parsing).

Lemma unsigned_of_Z_mod0 {n} (Hn : n < 0) x : unsigned (of_Z n x) = x.
Proof. rewrite Z.pow_neg_r; trivial using to_Z_of_Z_mod0. Qed.

Lemma unsigned_width {n} (Hn : 0 <= n) : unsigned (bitvec.of_Z n n) = n.
Proof. apply to_Z_of_Z_small. pose proof Z.pow_gt_lin_r 2 n; lia. Qed.
Notation to_Z_width := unsigned_width.

Lemma unsigned_range {n} (x : bitvec n) (Hn : 0 <= n) : 0 <= x < 2^n.
Proof. apply Zmod.unsigned_pos_bound. lia. Qed.
Notation to_Z_range := unsigned_range.

Lemma signed_of_Z {n} z : signed (of_Z n z) = Z.smodulo z (2^n).
Proof. apply signed_of_Z. Qed.

Lemma signed_range {n} (x : bitvec n) (Hn : 0 <= n) : -2^n <= 2*signed x < 2^n.
Proof. apply signed_pos_bound; lia. Qed.

Lemma signed_range' {n} (x : bitvec n) (Hn : 1 <= n) : -2^(n-1) <= signed x < 2^(n-1).
Proof.
  pose proof signed_range x ltac:(lia).
  rewrite <-(Z.succ_pred n) in H at 1 4; rewrite Z.pow_succ_r in H; lia.
Qed.

Lemma unsigned_width0 (a : bitvec 0) : to_Z a = 0.
Proof. pose proof to_Z_range a ltac:(lia); lia. Qed.
Notation to_Z_width0 := unsigned_width0 (only parsing).

Lemma signed_width0 (a : bitvec 0) : signed a = 0.
Proof. pose proof Zmod.signed_pos_bound a; lia. Qed.

Lemma of_Z_mod {n} x : bitvec.of_Z n (x mod 2^n) = bitvec.of_Z n x.
Proof. apply to_Z_inj. rewrite ?to_Z_of_Z, ?Zmod_mod; lia. Qed.

Lemma of_Z_inj {n} x y : bitvec.of_Z n x = bitvec.of_Z n y <-> x mod 2^n = y mod 2^n.
Proof. rewrite of_Z_inj. reflexivity. Qed.

Lemma mod_to_Z {n} (x : bitvec n) : to_Z x mod 2^n = to_Z x.
Proof.
  case (Z.ltb_spec n 0) as []. { rewrite Z.pow_neg_r at 2 by trivial. apply Zmod_0_r. }
  rewrite Z.mod_small; auto using to_Z_range.
Qed.

Lemma mod_signed {n} (x : bitvec n) : signed x mod 2^n = unsigned x.
Proof. apply mod_signed. Qed.

Lemma smod_unsigned {n} (x : bitvec n) : Z.smodulo (unsigned x) (2^n) = signed x.
Proof. apply smod_unsigned. Qed.

Lemma smod_signed {n} (x : bitvec n) : Z.smodulo (signed x) (2^n) = signed x.
Proof. rewrite <-smod_unsigned, Z.smod_smod; trivial. Qed.

Lemma signed_small {n} (x : bitvec n) (H : 0 <= 2*x < 2^n) : signed x = unsigned x.
Proof. apply signed_small, H. Qed.

Lemma signed_large {n} (x : bitvec n) (H : 2^n <= 2*x) : signed x = x-2^n.
Proof. rewrite signed_large; lia. Qed.

Lemma signed_neg_iff {n} (x : bitvec n) (Hn : 0 <= n) :
  signed x < 0 <-> 2^n <= 2 * unsigned x.
Proof. apply signed_neg_iff. lia. Qed.

Lemma signed_small_iff {n} (x : bitvec n) (Hn : 0 <= n) :
  signed x = unsigned x <-> 2 * unsigned x < 2^n.
Proof. rewrite signed_small_iff; lia. Qed.

Lemma signed_nonneg_iff {n} (x : bitvec n) (Hn : 0 <= n) :
  0 <= signed x <-> 2 * unsigned x < 2^n.
Proof. rewrite signed_nonneg_iff; lia. Qed.

Lemma signed_pos_iff {n} (x : bitvec n) (Hn : 0 <= n) :
  0 < signed x <-> 0 < 2 * unsigned x < 2^n.
Proof. rewrite signed_pos_iff; lia. Qed.

Lemma unsigned_opp {n} (x : bitvec n) : to_Z (opp x) = (- to_Z x) mod 2^n.
Proof. rewrite to_Z_opp; trivial. Qed.
Notation to_Z_opp := unsigned_opp (only parsing).
Lemma signed_opp {n} (x : bitvec n) : signed (opp x) = Z.smodulo (-signed x) (2^n).
Proof. rewrite signed_opp; trivial. Qed.
Lemma unsigned_add {n} (x y : bitvec n) : to_Z (add x y) = (to_Z x + to_Z y) mod 2^n. 
Proof. rewrite to_Z_add; trivial. Qed.
Notation to_Z_add := unsigned_add (only parsing).
Lemma signed_add {n} (x y : bitvec n) : signed (add x y) = Z.smodulo (signed x+signed y) (2^n).
Proof. rewrite signed_add; trivial. Qed.
Lemma unsigned_sub {n} (x y : bitvec n) : to_Z (sub x y) = (to_Z x - to_Z y) mod 2^n.
Proof. rewrite to_Z_sub; trivial. Qed.
Notation to_Z_sub := unsigned_sub (only parsing).
Lemma signed_sub {n} (x y : bitvec n) : signed (sub x y) = Z.smodulo (signed x-signed y) (2^n).
Proof. rewrite signed_sub; trivial. Qed.
Lemma unsigned_mul {n} (x y : bitvec n) : to_Z (mul x y) = (to_Z x * to_Z y) mod 2^n.
Proof. rewrite to_Z_mul; trivial. Qed.
Notation to_Z_mul := unsigned_mul (only parsing).
Lemma signed_mul {n} (x y : bitvec n) : signed (mul x y) = Z.smodulo (signed x*signed y) (2^n).
Proof. rewrite signed_mul; trivial. Qed.
Lemma to_Z_slu {n} (x : bitvec n) y : to_Z (slu x y) = Z.shiftl x y mod 2^n.
Proof. rewrite to_Z_slu; trivial. Qed.
(* (* TODO *)
Lemma to_Z_srs {n} (x : bitvec n) y : to_Z (srs x y) = Z.shiftr (signed x) y mod 2^n.
Proof. rewrite to_Z_srs; trivial. Qed.
Lemma signed_srs {n} (x : bitvec n) y : signed (srs x y) = Z.shiftr (signed x) y.
Proof. apply signed_srs. Qed.
*)
Lemma of_Z_div {n} (x y : Z) (Hx : 0 <= x < 2^n) (Hy : 0 < y < 2^n) :
  bitvec.of_Z n (x / y) = udiv (of_Z _ x) (of_Z _ y).
Proof. apply of_Z_div_small; trivial. Qed.
Lemma of_Z_umod {n} (x y : Z) (Hx : 0 <= x < 2^n) (Hy : 0 <= y < 2^n) :
  bitvec.of_Z n (x mod y) = umod (of_Z _ x) (of_Z _ y).
Proof. rewrite of_Z_umod_small; trivial. Qed.
Lemma to_Z_mdiv {n} (x y : bitvec n) : to_Z (mdiv x y) = x * Znumtheory.invmod y (2^n) mod 2^n.
Proof. rewrite to_Z_mdiv; trivial. Qed.
Lemma to_Z_pow_nonneg_r {n} (x : bitvec n) z (Hz : 0 <= z) : to_Z (pow x z) = x^z mod 2^n.
Proof. rewrite to_Z_pow_nonneg_r; trivial. Qed.
Notation to_Z_pow_nonneg := to_Z_pow_nonneg_r (only parsing).
Lemma signed_pow_nonneg_r {n} (x z : bitvec n) (Hz : 0 <= z) : signed (pow x z) = Z.smodulo (signed x ^ z) (2^n).
Proof. rewrite signed_pow_nonneg_r; trivial. Qed.
Notation signed_pow_nonneg := signed_pow_nonneg_r.

Lemma of_Z_nz {n} (x : bitvec n) (H : (x mod 2^n <> 0)%Z) : bitvec.of_Z n x <> zero.
Proof. apply of_Z_nz. trivial. Qed.

Lemma opp_overflow {n} (x : bitvec n) (Hn : 0 <= n) (Hx : signed x = -2^(n-1)) : opp x = x.
Proof.
  case (Z.eqb_spec n 0) as [->|]; [apply hprop_Zmod_1|].
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as H.
    replace (Z.succ (n-1)) with (n) in H by lia.
  apply opp_overflow; rewrite ?Hx, ?H; Z.to_euclidean_division_equations; lia.
Qed.

Lemma abs_overflow {n} (x : bitvec n) (Hn : 0 <= n) (Hx : signed x = -2^(n-1)) : abs x = x.
Proof.
  cbv [abs]. rewrite Hx.
  case (Z.ltb_spec (-2^(n-1)) 0) as []; auto using opp_overflow.
Qed.

Lemma squot_overflow {n} (x y : bitvec n) (Hn : 0 <= n) (Hx : signed x = -2^(n-1)) (Hy : signed y = -1) :
  squot x y = x.
Proof.
  case (Z.eqb_spec n 0) as [->|]; [apply hprop_Zmod_1|].
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as H;
    replace (Z.succ (n-1)) with n in H by lia.
  apply squot_overflow; rewrite ?Pos2Z.inj_shiftl_1; Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_squot_small {n} (x y : bitvec n) (Hn : 0 <= n) (Hy : signed y <> 0) :
  ~ (signed x = -2^(n-1) /\ signed y = -1) ->
  signed (squot x y) = signed x ÷ signed y.
Proof.
  intros; case (Z.eqb_spec n 0) as [->|]. { rewrite !signed_width0; trivial. }
  apply signed_squot_small; try lia.
  intros (X&Y&_); apply H; clear H; split; trivial.
  rewrite X.
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as H;
    replace (Z.succ (n-1)) with n in H by lia;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_srem {n} (x y : bitvec n) : signed (srem x y) = Z.smodulo (Z.rem (signed x) (signed y)) (2^n).
Proof. apply signed_of_Z. Qed.

Lemma signed_squot {n} (x y : bitvec n) : signed (squot x y) =
  Z.smodulo (if signed y =? 0 then -1 else signed x ÷ signed y) (2^n).
Proof. apply signed_of_Z. Qed.

Lemma signed_squot_nz {n} (x y : bitvec n) : signed y <> 0 -> signed (squot x y) = Z.smodulo (signed x ÷ signed y) (2^n).
Proof. intros; rewrite signed_squot_nz; trivial. Qed.

(** ** Bitwise operations *)

Lemma testbit_high {n} (x : bitvec n) i (Hn : 0 <= n) (Hi : (n <= i)%Z) : Z.testbit x i = false.
Proof. rewrite <-mod_to_Z, Z.mod_pow2_bits_high; lia. Qed.

Lemma testbit_m1 {n} i (Hn : 0 <= n) : Z.testbit (@Zmod.opp (2^n) one) i = (0 <=? i) && (i <? n).
Proof. rewrite to_Z_m1, Z.testbit_ones; lia. Qed.

Lemma testbit_sign {n} (x : bitvec n) (Hn : 0 <= n) : Z.testbit x (n-1) = (signed x <? 0).
Proof.
  intros; case (Z.eqb_spec n 0) as [->|]. { rewrite !signed_width0; trivial. }
  apply eq_true_iff_eq. rewrite Z.testbit_true, Z.ltb_lt, signed_neg_iff by lia.
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as R;
    replace (Z.succ (n-1)) with n in R by lia.
  pose proof to_Z_range x.
  rewrite Z.mod_small; Z.to_euclidean_division_equations; nia.
Qed.

Lemma testbit_signed_high {n} (x : bitvec n) i (Hn : 0 <= n) (Hi : (n <= i)%Z) :
  Z.testbit (signed x) i = (signed x <? 0).
Proof.
  intros; case (Z.eqb_spec n 0) as [->|]. { rewrite !signed_width0, ?Z.testbit_0_l; trivial. }
  case (Z.eq_dec (signed x) 0) as [->|]; [case i; trivial|].
  pose proof signed_range x.
  apply eq_true_iff_eq. rewrite <-Z.bits_iff_neg, Z.ltb_lt; try reflexivity.
  apply Z.log2_lt_pow2; try lia.
  eapply Z.lt_le_trans with (m:=2^n); [|apply Z.pow_le_mono_r]; lia.
Qed.

Lemma unsigned_and {n} (x y : bitvec n) : unsigned (and x y) = Z.land x y.
Proof. apply unsigned_and_small. lia. Qed.

Lemma unsigned_or {n} (x y : bitvec n) : to_Z (or x y) = Z.lor x y.
Proof.
  cbv [or]; rewrite to_Z_of_Z.
  case (Z.ltb_spec n 0) as []. { rewrite Z.pow_neg_r at 3 by trivial; apply Zmod_0_r. }
  apply Z.bits_inj; intros i; destruct (Z.ltb_spec i n);
  repeat rewrite ?Z.lor_spec, ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?testbit_high by lia; trivial.
Qed.
Notation to_Z_or := unsigned_or (only parsing).

Lemma unsigned_xor {n} (x y : bitvec n) : to_Z (xor x y) = Z.lxor x y.
Proof.
  cbv [xor]; rewrite to_Z_of_Z.
  case (Z.ltb_spec n 0) as []. { rewrite Z.pow_neg_r at 3 by trivial; apply Zmod_0_r. }
  apply Z.bits_inj; intros i; destruct (Z.ltb_spec i n);
  repeat rewrite ?Z.lxor_spec, ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?testbit_high by lia; trivial.
Qed.
Notation to_Z_xor := unsigned_xor (only parsing).

Lemma xor_zero_iff {n} (x y : bitvec n) : xor x y = zero <-> x = y.
Proof.
  rewrite <-2to_Z_inj_iff, to_Z_0, to_Z_xor, Z.lxor_eq_0_iff; reflexivity.
Qed.

Lemma eqb_xor_zero {n} (x y : bitvec n) : eqb (xor x y) zero = eqb x y.
Proof.
  pose proof xor_zero_iff x y.
  destruct (eqb_spec (xor x y) zero), (eqb_spec x y); intuition congruence.
Qed.

Module Z.
Lemma ones_neg n (Hn : n < 0) : Z.ones n = -1.
Proof. rewrite Z.ones_equiv, Z.pow_neg_r; trivial. Qed.
End Z.

Lemma to_Z_not {n} (x : bitvec n) : to_Z (not x) = Z.ldiff (Z.ones n) x.
Proof.
  cbv [not]; rewrite to_Z_of_Z, ?Pos2Z.inj_shiftl_1; apply Z.bits_inj'; intros i Hi.
  case (Z.leb_spec 0 n) as []; case (Z.ltb_spec i n) as [];
  repeat rewrite ?Z.pow_neg_r (* does not work...*) ,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.ldiff_spec,
    ?Z.ones_spec_high, ?Z.ones_spec_low, ?testbit_high,
    ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial; try lia.
  rewrite (Z.pow_neg_r 2 n) at 2 by lia; rewrite Zmod_0_r.
  repeat rewrite ?Z.pow_neg_r (* does not work...*) ,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.ldiff_spec,
    ?Z.ones_spec_high, ?Z.ones_spec_low, ?testbit_high,
    ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial; try lia.
Qed.

Lemma to_Z_not' {n} (x : bitvec n) : to_Z (not x) = Z.ones n - x.
Proof.
  rewrite to_Z_not, Z.sub_nocarry_ldiff; trivial.
  apply Z.bits_inj'; intros i Hi;
  case (Z.leb_spec 0 n) as []; case (Z.ltb_spec i n) as [];
    repeat rewrite ?andb_false_r,
    ?Z.ldiff_spec, ?Z.testbit_ones, ?Z.testbit_0_l, ?testbit_high, 
    ?(proj2 (Z.ltb_lt _ _)), ?(proj2 (Z.leb_le _ _)), ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial.
Qed.

Lemma of_Z_lnot {n} z : bitvec.of_Z n (Z.lnot z) = not (bitvec.of_Z n z).
Proof.
  apply Zmod.to_Z_inj. rewrite to_Z_not, to_Z_of_Z, to_Z_of_Z.
  apply Z.bits_inj'; intros i Hi;
  case (Z.leb_spec 0 n) as []; case (Z.ltb_spec i n) as [];
  repeat rewrite ?Z.ldiff_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.testbit_ones,
    ?(proj2 (Z.ltb_lt _ _)), (proj2 (Z.leb_le _ _)), ?(proj2 (Z.ltb_nlt _ _))
    by lia; trivial.
  rewrite (Z.pow_neg_r 2 n) at 2 by lia; rewrite Zmod_0_r.
  rewrite (Z.pow_neg_r 2 n) at 1 by lia; rewrite Zmod_0_r.
  repeat rewrite ?Z.pow_neg_r (* does not work...*) ,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.ldiff_spec,
    ?Z.ones_spec_high, ?Z.ones_spec_low, ?testbit_high,
    ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial; try lia.
Qed.

Lemma not_not {n} (x : bitvec n) : not (not x) = x.
Proof. apply to_Z_inj. rewrite !to_Z_not'; lia. Qed.

Lemma not_0 {n} : not zero = opp one :> bitvec n.
Proof. apply Zmod.to_Z_inj; rewrite to_Z_not', to_Z_0, Z.sub_0_r, to_Z_m1; trivial. Qed.

Lemma not_m1 {n} : not (opp one) = zero :> bitvec n.
Proof. rewrite <-not_0, not_not; trivial. Qed.

(** ** Bitvector operations that vary the modulus *)

Lemma to_Z_app {n m} a b (Hn : 0 <= n) (Hm : ~(-n <= m < 0)) :
  to_Z (@app n m a b) = Z.lor a (Z.shiftl b n).
Proof.
  cbv [app]. rewrite to_Z_of_Z, Z.shiftl_mul_pow2; trivial.
  case (Z.ltb_spec (n+m) 0) as []. { rewrite (Z.pow_neg_r 2 (_+_)), Zmod_0_r; lia. }
  apply Z.mod_small.
  rewrite Z.pow_add_r by lia.
  (* lor <= add *)
  pose proof to_Z_range a; pose proof to_Z_range b.
  pose proof Z.lor_nonneg a (b * 2^n). pose proof Z.land_nonneg a (b * 2^n).
  pose proof Z.add_lor_land a (b * 2^n). nia.
Qed.

Lemma to_Z_firstn {n m} a : to_Z (@firstn n m a) = a mod 2^n.
Proof. apply to_Z_of_Z. Qed.

Lemma to_Z_skipn {n m} a (Hn : 0 <= n) : to_Z (@skipn n m a) = a/2^n.
Proof.
  cbv [skipn]; rewrite to_Z_of_Z, Z.shiftr_div_pow2 by trivial.
  case (Z.ltb_spec m n) as []. { rewrite (Z.pow_neg_r 2 (_-_)), Zmod_0_r; lia. }
  pose proof to_Z_range a ltac:(lia).
  apply Z.mod_small; split. { Z.div_mod_to_equations; nia. }
  apply Zdiv_lt_upper_bound; [lia|].
  rewrite <-Z.pow_add_r, Z.sub_add; lia.
Qed.

Lemma to_Z_extract start pastend {w} (a : bitvec w) (H : 0 <= start <= pastend) :
  to_Z (extract start pastend a) = a/2^start mod 2^(pastend-start).
Proof. cbv [extract]. rewrite to_Z_firstn, to_Z_skipn; lia. Qed.

Lemma firstn_app {n m} a b (Hn : 0 <= n) (Hm : ~ (- n <= m < 0)) :
  firstn n (@app n m a b) = a.
Proof.
  apply to_Z_inj; rewrite to_Z_firstn, to_Z_app; try lia.
  symmetry. rewrite <-mod_to_Z at 1; symmetry.
  rewrite <-!Z.land_ones by lia.
  apply Z.bits_inj'; intros i Hi.
  repeat rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.shiftl_spec, ?Z.testbit_ones,
    ?Z.mod_pow2_bits_high, ?testbit_high_pow2, ?(Z.testbit_neg_r(*workaround*)b),
    ?Zle_imp_le_bool, ?Bool.andb_true_l by lia; trivial.
  destruct (Z.ltb_spec i n); try Btauto.btauto.
  rewrite (Z.testbit_neg_r b) by lia; Btauto.btauto.
Qed.

Lemma skipn_app {n m} a b (Hn : 0 <= n) (Hm : ~ (- n <= m < 0)) :
  existT _ _ (skipn n (@app n m a b)) = existT _ _ b.
Proof.
  pose proof to_Z_range a. eapply to_Z_inj_dep. { f_equal. lia. }
  rewrite to_Z_skipn, <-Z.shiftr_div_pow2, to_Z_app, Z.shiftr_lor, Z.shiftr_shiftl_l; try lia.
  erewrite Z.shiftr_div_pow2, Z.sub_diag, Z.shiftl_0_r, Z.div_small, Z.lor_0_l; lia.
Qed.

Lemma skipn_app' {n m} a b (Hn : 0 <= n) (Hm : ~ (- n <= m < 0)) :
  exists pf, skipn n (@app n m a b) = eq_rect _ Zmod b _ pf.
Proof.
  pose proof skipn_app a b ltac:(lia) ltac:(lia) as E.
  symmetry in E; inversion_sigma. exists E1.
  apply to_Z_inj. rewrite to_Z_eq_rect, <-E2, to_Z_eq_rect; trivial.
Qed.

Lemma skipn_app'' {n m} a b pf (Hn : 0 <= n) (Hm : ~ (- n <= m < 0)) :
  skipn n (@app n m a b) = eq_rect _ Zmod b _ pf.
Proof.
  case (skipn_app' a b) as [?->]; trivial.
  apply to_Z_inj; rewrite !to_Z_eq_rect; trivial.
Qed.

Lemma skipn_app''' {n m} a b (Hn : 0 <= n) (Hm : ~ (- n <= m < 0)) :
  skipn n (@app n m a b) = of_Z _ (to_Z (skipn n (@app n m a b))).
Proof.
  case (skipn_app' a b) as [?->]; trivial.
  apply to_Z_inj; rewrite to_Z_eq_rect, to_Z_of_Z.
  rewrite Z.add_simpl_l, mod_to_Z; trivial.
Qed.

Lemma app_assoc {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l)
  (Hn : 0 <= n) (Hm : 0 <= m) (Hl : 0 <= l) :
  existT _ _ (app a (app b c)) = existT _ _ (app (app a b) c).
Proof.
  pose proof to_Z_range a. eapply to_Z_inj_dep. { f_equal. lia. }
  rewrite ?to_Z_app by lia.
  apply Z.bits_inj'; intros i Hi; case (Z.leb_spec 0 (i - n)) as [];
  repeat rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.shiftl_spec, ?Z.testbit_ones,
    ?Z.sub_add_distr, ?N2Z.inj_add, ?Bool.orb_assoc,
    (*workaround:*) ?(Z.testbit_neg_r (Z.shiftl c m)), ?(Z.testbit_neg_r c)
    by lia; trivial.
Qed.

Lemma app_assoc' {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l)
  (Hn : 0 <= n) (Hm : 0 <= m) (Hl : 0 <= l) :
  exists pf, app a (app b c) = eq_rect _ _ (app (app a b) c) _ pf.
Proof.
  pose proof app_assoc a b c Hn Hm Hl as E; symmetry in E; inversion_sigma.
  exists E1. apply to_Z_inj; rewrite <-E2, !to_Z_eq_rect; trivial.
Qed.

Lemma app_assoc'' {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l) pf
  (Hn : 0 <= n) (Hm : 0 <= m) (Hl : 0 <= l) :
  app a (app b c) = eq_rect _ _ (app (app a b) c) _ pf.
Proof.
  case (app_assoc' a b c) as [?->]; trivial.
  apply to_Z_inj; rewrite !to_Z_eq_rect; trivial.
Qed.

Lemma app_assoc''' {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l)
  (Hn : 0 <= n) (Hm : 0 <= m) (Hl : 0 <= l) :
  app a (app b c) = of_Z _ (to_Z (app (app a b) c)).
Proof.
  ecase (app_assoc' a b c) as [?->]; trivial. apply to_Z_inj;
    rewrite !to_Z_eq_rect, !to_Z_of_Z, ?Z.add_assoc, mod_to_Z; trivial.
Qed.

End bitvec.


Module Zstar.
Import Znumtheory Zmod Zstar.

(** ** Conversions to [Zmod] *)

Lemma coprime_to_Zmod {m} (a : Zstar m) : Z.gcd (to_Zmod a) m = 1.
Proof.
  case a as [a H]; cbv [Zmod.to_Z Zmod.Private_to_Z to_Zmod Private_to_Z Zmod.of_small_Z].
   apply Is_true_eq_true, andb_true_iff in H; lia.
Qed.
Notation to_Zmod_range := coprime_to_Zmod (only parsing).

Lemma to_Zmod_inj {m} (x y : Zstar m) : to_Zmod x = to_Zmod y -> x = y.
Proof.
  cbv [to_Zmod Private_to_Z]; destruct x, y.
  intros H%(f_equal Zmod.to_Z); rewrite !Zmod.to_Z_of_small_Z in H.
  destruct H.
  apply f_equal, Is_true_hprop.
Qed.

Lemma to_Zmod_inj_iff {m} (x y : Zstar m) : to_Zmod x = to_Zmod y <-> x = y.
Proof. split; auto using to_Zmod_inj; congruence. Qed.

Lemma to_Zmod_of_coprime_Zmod {m} (x : Zmod m) pf : to_Zmod (of_coprime_Zmod x pf) = x.
Proof.
  apply to_Z_inj; pose proof Zmod.to_Z_range x.
  cbv [to_Zmod of_coprime_Zmod Private_to_Z]; rewrite to_Z_of_small_Z; lia.
Qed.

Lemma to_Zmod_of_Zmod' {m} (x : Zmod m) :
  to_Zmod (of_Zmod x) = if Z.eqb (Z.gcd x m) 1 then x else Zmod.one.
Proof. apply to_Zmod_of_coprime_Zmod. Qed.

Lemma to_Zmod_of_Zmod {m} (x : Zmod m) (H : Z.gcd x m = 1) : to_Zmod (of_Zmod x) = x.
Proof. rewrite to_Zmod_of_Zmod'; case (Z.eqb_spec (Z.gcd x m) 1); congruence. Qed.

Lemma of_Zmod_to_Zmod {m} x : @of_Zmod m (to_Zmod x) = x.
Proof. pose (to_Zmod_range x). apply to_Zmod_inj. rewrite to_Zmod_of_Zmod; auto. Qed.

Lemma to_Zmod_1 {m} : @to_Zmod m one = Zmod.one.
Proof. apply to_Zmod_of_Zmod, Zmod.gcd_1_m. Qed.

Lemma of_Zmod_inj {m} (x y : Zmod m) :
  Z.gcd x m = 1 -> Z.gcd y m = 1 -> of_Zmod x = of_Zmod y -> x = y.
Proof. intros ? ? H%(f_equal to_Zmod); rewrite 2 to_Zmod_of_Zmod in H; trivial. Qed.

Lemma to_Zmod_0_iff {m} (a : Zstar m) : to_Zmod a = zero <-> Z.abs m = 1.
Proof.
  rewrite <-to_Z_0_iff.
  pose proof to_Z_range a.
  case (Z.eq_dec a 0) as [E|]; try lia.
  pose proof to_Zmod_range a as X; rewrite E, Z.gcd_0_l in X; lia.
Qed.

Lemma to_Zmod_nz {m} (a : Zstar m) (Hm : 2 <= m) : to_Zmod a <> zero.
Proof. rewrite to_Zmod_0_iff; lia. Qed.

Lemma eqb_spec {m} (x y : Zstar m) : BoolSpec (x = y) (x <> y) (eqb x y).
Proof.
  cbv [eqb]. case (eqb_spec x y);
    constructor; auto using to_Zmod_inj; congruence.
Qed.

Lemma eqb_eq {m} (x y : Zstar m) : eqb x y = true <-> x = y.
Proof. destruct (eqb_spec x y); intuition congruence. Qed.

Lemma eqb_refl {m} (x : Zstar m) : eqb x x = true.
Proof. apply eqb_eq; trivial. Qed.

Lemma hprop_Zstar_1 (a b : Zstar 1) : a = b.
Proof. apply to_Zmod_inj,  hprop_Zmod_1. Qed.

Lemma hprop_Zstar_2 (a b : Zstar 2) : a = b.
Proof.
  pose proof to_Zmod_range a; pose proof to_Zmod_range b.
  pose proof Zmod.to_Z_range a; pose proof Zmod.to_Z_range b.
  apply to_Zmod_inj, Zmod.to_Z_inj;
  assert (to_Z a = 0 \/ to_Z a = 1) as [Ha|Ha] by lia;
  assert (to_Z b = 0 \/ to_Z b = 1) as [Hb|Hb] by lia;
  rewrite ?Ha, ?Hb in *; cbn in *; intuition try lia.
Qed.

Lemma wlog_eq_Zstar_3_pos {m} (a b : Zstar m) (Hm : 0 < m) (k : 3 <= m -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec 1 m) as [e|].
  { destruct e; auto using hprop_Zstar_1. }
  destruct (Z.eq_dec 2 m) as [e'|].
  { destruct e'; auto using hprop_Zstar_2. }
  { apply k; lia. }
Qed.

Lemma of_Zmod_1 {m} : @of_Zmod m Zmod.one = one.
Proof.
  apply to_Zmod_inj. rewrite to_Zmod_1, to_Zmod_of_Zmod; trivial using Zmod.gcd_1_m.
Qed.

Lemma to_Z_0_iff {m} (a : Zstar m) : to_Z a = 0 <-> Z.abs m = 1.
Proof. rewrite unsigned_0_iff, to_Zmod_0_iff; reflexivity. Qed.

Lemma to_Z_nz_iff {m} (a : Zstar m) : to_Z a <> 0 <-> Z.abs m <> 1.
Proof. rewrite to_Z_0_iff; reflexivity. Qed.

Lemma to_Z_nz {m} (a : Zstar m) : Z.abs m <> 1 -> to_Z a <> 0.
Proof. apply to_Z_nz_iff. Qed.

(** ** [opp] *)

Lemma to_Zmod_opp {m} (a : Zstar m) : to_Zmod (opp a) = Zmod.opp a.
Proof.
  apply to_Zmod_of_Zmod.
  rewrite to_Z_opp, Z.gcd_mod_l, Z.gcd_opp_l.
  apply coprime_to_Zmod.
Qed.

Lemma opp_opp {m} (a : Zstar m) : opp (opp a) = a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_opp. apply Zmod.opp_opp. Qed.

Lemma opp_inj {m} (a b : Zstar m) : opp a = opp b -> a = b.
Proof. rewrite <-2to_Zmod_inj_iff, 2to_Zmod_opp. apply opp_inj. Qed.

Lemma opp_distinct_odd {m} (Hm : m mod 2 = 1) (Hm' : 3 <= m) a :
  a <> opp a :> Zstar m.
Proof.
  intro X; pose proof to_Z_range a; pose proof to_Z_nz a ltac:(lia).
  apply to_Zmod_inj_iff, Zmod.to_Z_inj_iff in X.
  rewrite ?to_Zmod_opp, Zmod.to_Z_opp, Z_mod_nz_opp_full in *;
    rewrite ?mod_to_Z in *; Z.div_mod_to_equations; nia.
Qed.

Lemma opp_1_neq_1 {m} (Hm : 3 <= Z.abs m) : opp one <> one :> Zstar m.
Proof.
  intros H%(f_equal to_Zmod); rewrite to_Zmod_opp, to_Zmod_1 in H.
  apply (Zmod.opp_1_neq_1 Hm); trivial.
Qed.

(** ** [abs] *)

Lemma to_Zmod_abs {m} (a : Zstar m) : to_Zmod (abs a) = Zmod.abs a.
Proof.
  cbv [abs Zmod.abs]; case Z.ltb; fold (opp a);
  rewrite ?to_Zmod_opp, ?to_Zmod_of_Zmod; auto using coprime_to_Zmod.
Qed.

Lemma abs_1 m : @abs m one = one.
Proof. apply to_Zmod_inj. rewrite to_Zmod_abs, ?to_Zmod_1, Zmod.abs_1; trivial. Qed.

Lemma abs_nonneg {m} (x : Zstar m) : 0 <= @signed m x -> abs x = x.
Proof. intros. apply to_Zmod_inj. rewrite to_Zmod_abs, abs_nonneg; trivial. Qed.

Lemma abs_neg {m} (x : Zstar m) : @signed m x < 0 -> abs x = opp x.
Proof. intros. apply to_Zmod_inj. rewrite to_Zmod_abs, to_Zmod_opp, abs_neg; trivial. Qed.

Lemma abs_pos {m} (x : Zstar m) : 0 < @signed m x -> abs x = x.
Proof. intros. apply to_Zmod_inj. rewrite to_Zmod_abs, abs_pos; trivial. Qed.

Lemma abs_opp {m} x : @abs m (opp x) = abs x.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_abs, ?to_Zmod_opp, abs_opp; trivial. Qed.

Lemma abs_abs {m} (x : Zstar m) : abs (abs x) = abs x.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_abs, abs_abs; trivial. Qed.

Lemma abs_overflow {m} (Hm : m mod 2 = 0)
  (x : Zstar m) (Hx : signed x = -m/2) : abs x = x.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_abs, abs_overflow; trivial. Qed.

(** ** [mul] *)

Lemma to_Zmod_mul {m} (a b : Zstar m) : @to_Zmod m (mul a b) = Zmod.mul a b.
Proof. cbv [mul]. rewrite to_Zmod_of_coprime_Zmod; trivial. Qed.

Lemma of_Zmod_mul {m} (a b : Zmod m) (Ha : Z.gcd a m = 1) (Hb : Z.gcd b m = 1) :
  @of_Zmod m (Zmod.mul a b) = mul (of_Zmod a) (of_Zmod b).
Proof.
  apply to_Zmod_inj; rewrite to_Zmod_mul, ?to_Zmod_of_Zmod; trivial.
  rewrite to_Z_mul, Z.gcd_mod_l; apply Z.coprime_mul_l; auto.
Qed.

Lemma mul_assoc {m} a b c : @mul m a (mul b c) = mul (mul a b) c.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul. apply Zmod.mul_assoc. Qed.
Lemma mul_comm {m} a b : @mul m a b = mul b a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul; apply Zmod.mul_comm. Qed.
Lemma mul_1_l {m} a : @mul m one a = a. Proof.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, to_Zmod_1. apply Zmod.mul_1_l. Qed.
Lemma mul_1_r {m} a : @mul m a one = a. Proof. rewrite <-mul_comm; apply mul_1_l. Qed.
Lemma mul_m1_l {m} a : @mul m (opp one) a = opp a.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_mul, ?to_Zmod_opp, ?to_Zmod_1, Zmod.mul_m1_l; trivial. Qed.
Lemma mul_m1_r {m} a : @mul m a (opp one) = opp a. Proof. rewrite mul_comm; apply mul_m1_l. Qed.

Lemma mul_opp_l {m} (a b : Zstar m) : mul (opp a) b = opp (mul a b).
Proof. apply to_Zmod_inj; repeat rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_l. Qed.
Lemma mul_opp_r {m} (a b : Zstar m) : mul a (opp b) = opp (mul a b).
Proof. apply to_Zmod_inj; repeat rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_r. Qed.
Lemma mul_opp_opp {m} a b : @mul m (opp a) (opp b) = mul a b.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_opp. Qed.

Lemma abs_mul_abs_l {m} (x y : Zstar m) : abs (mul (abs x) y) = abs (mul x y).
Proof.
  intros. apply to_Zmod_inj.
  repeat rewrite ?to_Zmod_abs, ?to_Zmod_mul, ?abs_mul_abs_l; trivial.
Qed.

Lemma abs_mul_abs_r {m} (x y : Zstar m) : abs (mul x (abs y)) = abs (mul x y).
Proof.
  intros. apply to_Zmod_inj.
  repeat rewrite ?to_Zmod_abs, ?to_Zmod_mul, ?abs_mul_abs_r; trivial.
Qed.

Lemma abs_mul_abs_abs {m} (x y : Zstar m) : abs (mul (abs x) (abs y)) = abs (mul x y).
Proof.
  intros. apply to_Zmod_inj.
  repeat rewrite ?to_Zmod_abs, ?to_Zmod_mul, ?abs_mul_abs_abs; trivial.
Qed.

Local Notation "∏ xs" := (List.fold_right mul one xs) (at level 40).

(** ** [inv] and [div] *)

Lemma to_Zmod_inv {m} x : to_Zmod (@inv m x) = Zmod.inv x.
Proof.
  cbv [inv]. rewrite to_Zmod_of_Zmod; trivial.
  rewrite to_Z_inv; auto using coprime_invmod, to_Zmod_range.
Qed.

Lemma not_of_Zmod_inv (m := 6) (x := Zmod.of_Z _ 4) : of_Zmod (@Zmod.inv m x) <> inv (of_Zmod x).
Proof. inversion 1. Qed.

Lemma to_Zmod_div {m} x y : to_Zmod (@div m x y) = Zmod.mdiv x y.
Proof. cbv [div]. rewrite to_Zmod_mul, to_Zmod_inv, mul_inv_r; trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = div x y.
Proof. apply to_Zmod_inj. cbv [div inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r {m} x y : mul x (@inv m y) = div x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

Lemma div_same {m} (a : Zstar m) : div a a = one.
Proof.
  apply to_Zmod_inj, to_Z_inj. pose proof coprime_to_Zmod a.
  rewrite to_Zmod_div, to_Z_mdiv, Z.mul_comm, invmod_coprime', to_Zmod_1, to_Z_1; trivial.
Qed.

Lemma div_mul_l {m} (a b c : Zstar m) : div (mul a b) c = mul a (div b c).
Proof. rewrite <-mul_inv_l, mul_comm, <-mul_assoc, mul_inv_r; trivial. Qed.

Lemma mul_inv_same_l {m} x : mul (@inv m x) x = one.
Proof. rewrite mul_inv_l, div_same; trivial. Qed.

Lemma mul_inv_same_r {m} x : mul x (@inv m x) = one.
Proof. rewrite mul_comm; apply mul_inv_same_l; trivial. Qed.

Lemma inv_inv {m} x : inv (@inv m x) = x.
Proof.
  rewrite <-mul_1_r, <-(mul_inv_same_l (inv x)), (mul_comm _ (inv x)); auto.
  rewrite mul_assoc, (mul_comm x), (mul_inv_same_l x), mul_1_l; auto.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  case (Z.eq_dec m 0) as [->|]; trivial.
  symmetry; rewrite <-mul_1_l, mul_inv_r, div_same; trivial.
Qed.

Lemma div_1_r {m} x : @div m x one = x.
Proof. cbv [div]; rewrite inv_1, mul_1_r; trivial. Qed.

Lemma mul_cancel_l {m} (a b c : Zstar m) (H : mul a b = mul a c) : b = c.
Proof.
  case (Z.eq_dec m 0) as [->|]; trivial.
  { apply (f_equal (fun x => unsigned (to_Zmod x))) in H.
    rewrite !to_Zmod_mul, !to_Z_mul, !Zmod_0_r in H.
    eapply to_Zmod_inj, to_Z_inj, Z.mul_cancel_l; eauto.
    pose proof to_Zmod_range a; rewrite Z.gcd_0_r in *; lia. }
  apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_l_iff {m} (a b c : Zstar m) : mul a b = mul a c <-> b = c.
Proof. split. apply mul_cancel_l. congruence. Qed.

Lemma mul_cancel_r {m} (a b c : Zstar m) (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l in H; trivial. Qed.

Lemma mul_cancel_r_iff {m} (a b c : Zstar m) : mul b a = mul c a <-> b = c.
Proof. split. apply mul_cancel_r. congruence. Qed.

Lemma mul_div_r_same_r {m} (a b : Zstar m) : mul a (div b a) = b.
Proof.
  rewrite <-mul_inv_r, (mul_comm b), mul_assoc, mul_inv_same_r, mul_1_l; auto.
Qed.

Lemma inv_mul {m} (a b : Zstar m) : inv (mul a b) = mul (inv a) (inv b).
Proof.
  pose proof mul_inv_same_r (mul a b) as H.
  apply (f_equal (mul (inv b))), (f_equal (mul (inv a))) in H; trivial.
  rewrite mul_1_r in H; rewrite <-H; clear H; set (inv (mul _ _)) as x.
  rewrite !mul_assoc, (mul_comm (inv _)), <-(mul_assoc (inv _)).
  repeat rewrite ?mul_inv_same_l, ?mul_1_r, ?mul_1_l; trivial.
Qed.

Lemma div_div_r_same {m} (a b : Zstar m) : div a (div a b) = b.
Proof. rewrite <-!mul_inv_r, inv_mul, mul_assoc, inv_inv, mul_inv_same_r, mul_1_l; trivial. Qed.

Lemma inv_div {m} (x y : Zstar m) : inv (div x y) = div y x.
Proof. rewrite <-!mul_inv_l, inv_mul, inv_inv, mul_comm; trivial. Qed.

Lemma eq_inv_iff {m} (x y : Zstar m) : inv x = y <-> mul x y = one.
Proof. rewrite <-mul_cancel_l_iff, mul_inv_same_r; intuition congruence. Qed.

Lemma inv_opp {m} (x : Zstar m) : inv (opp x) = opp (inv x).
Proof. apply eq_inv_iff; rewrite ?mul_opp_opp, ?mul_inv_same_r; trivial. Qed.

(** ** [prod] *)

Lemma prod_Permutation {m} one (xs ys : list (Zstar m)) (H : Permutation xs ys) :
  List.fold_right mul one xs = List.fold_right mul one ys.
Proof. induction H; cbn; repeat rewrite ?mul_assoc, ?(mul_comm x); try congruence.
Qed.

Lemma prod_singleton {m} (x : Zstar m) : ∏ [x] = x. Proof. apply mul_1_r. Qed.

Lemma prod_app {m} xs ys : ∏ (xs ++ ys) = mul (∏ xs) (∏ ys) :> Zstar m.
Proof.
  induction xs; cbn; cbn [List.fold_right List.app];
    rewrite ?mul_1_l, ?IHxs, ?mul_assoc; trivial.
Qed.

Lemma prod_flat_map {A} {m} (f : A -> _) (xs : list A) :
  ∏ flat_map f xs = ∏ (map (fun x => ∏ f x) xs) :> Zstar m.
Proof. induction xs; cbn; rewrite ?prod_app, ?IHxs; eauto. Qed.

Lemma prod_concat [m] xss : ∏ concat xss = ∏ (map (fun xs => ∏ xs)) xss :> Zstar m.
Proof. induction xss; cbn; rewrite <-?IHxss; trivial using prod_app. Qed.

Lemma prod_rev {m} (xs : list (Zstar m)) : ∏ rev xs = ∏ xs.
Proof. induction xs; cbn; rewrite ?prod_app, ?prod_singleton, ?IHxs, ?(mul_comm a); trivial. Qed.

(** ** [pow] *)

Lemma to_Zmod_pow {m} (a : Zstar m) z : @to_Zmod m (pow a z) = Zmod.pow a z.
Proof.
  pose proof coprime_to_Zmod a; apply to_Zmod_of_Zmod.
  case (ltac:(lia):z = 0 \/ z < 0 \/ 0 < z) as [->|[]].
  { rewrite pow_0_r; apply Zmod.gcd_1_m. }
  all : rewrite ?to_Z_pow_nonneg_r, ?to_Z_pow_neg_r by lia.
  { apply coprime_invmod, Z.coprime_pow_l; lia. }
  { rewrite Z.gcd_mod_l, Z.coprime_pow_l; try lia. }
Qed.

Lemma pow_0_r {m} x : @pow m x 0 = one.
Proof. trivial. Qed.

Lemma pow_1_r {m} x : @pow m x 1 = x.
Proof. apply to_Zmod_inj. rewrite to_Zmod_pow, pow_1_r; trivial. Qed.

Lemma pow_2_r {m} x : @pow m x 2 = mul x x.
Proof. apply to_Zmod_inj. rewrite to_Zmod_pow, to_Zmod_mul, pow_2_r; trivial. Qed.

Lemma pow_opp_2 {m} (x : Zstar m) : pow (opp x) 2 = pow x 2.
Proof. apply to_Zmod_inj. rewrite !to_Zmod_pow, to_Zmod_opp, pow_opp_2; trivial. Qed.

Lemma pow_abs_2 {m} (x : Zstar m) : pow (abs x) 2 = pow x 2.
Proof. apply to_Zmod_inj. rewrite !to_Zmod_pow, to_Zmod_abs, pow_abs_2; trivial. Qed.

Lemma eq_abs_iff m (x y : Zstar m) : abs x = abs y <-> (y = x \/ y = opp x).
Proof.
  rewrite <-!to_Zmod_inj_iff, !to_Zmod_abs, !to_Zmod_opp. apply Zmod.eq_abs_iff.
Qed.

Lemma Private_coprime_Zmodpow {m} (a : Zstar m) z (H : 0 <= z ) : Z.gcd (Zmod.pow a z) m = 1.
Proof.
  pose proof coprime_to_Zmod a.
  rewrite Zmod.to_Z_pow_nonneg_r, Z.gcd_mod_l, Z.coprime_pow_l; lia.
Qed.

Lemma pow_opp_r {m} a (z : Z) : @pow m a (-z) = inv (pow a z).
Proof.
  pose proof Private_coprime_Zmodpow a as G.
  case (Z.ltb_spec (-z) 0) as [].
  { cbv [pow inv]; f_equal.
    rewrite pow_neg, Z.opp_involutive, to_Zmod_of_Zmod; trivial. apply G; lia. }
  case (Z.eqb_spec z 0) as [->|].
  { cbv [pow inv]; f_equal.
    rewrite !Zmod.pow_0_r, to_Zmod_of_Zmod, Zmod.inv_1; trivial using Zmod.gcd_1_m. }
  { symmetry; rewrite <-inv_inv; symmetry; f_equal. cbv [pow inv]; f_equal.
    rewrite (pow_neg _ z), to_Zmod_of_Zmod; trivial; try lia. apply G; lia. }
Qed.

Local Lemma Private_pow_succ_r_nonneg {m} (x : Zstar m) z (H : 0 <= z) :
  pow x (Z.succ z) = mul x (pow x z).
Proof.
  cbv [pow]; apply to_Zmod_inj.
  rewrite to_Zmod_mul, Zmod.pow_succ_nonneg_r, !to_Zmod_of_Zmod; trivial;
    rewrite ?to_Z_mul, ?Z.gcd_mod_l, ?Z.coprime_mul_l, ?Private_coprime_Zmodpow;
    auto using coprime_to_Zmod.
Qed.

Lemma pow_succ_r {m} (x : Zstar m) z : pow x (Z.succ z) = mul x (pow x z).
Proof.
  pose proof coprime_to_Zmod x.
  case (Z.leb_spec 0 z) as []; try auto using Private_pow_succ_r_nonneg.
  case (Z.eqb_spec z (-1)) as [->|?N].
  { cbv [pow]; cbn. fold (@inv m x).
    case (Z.eqb_spec m 0) as [->|].
    2: rewrite of_Zmod_1, mul_inv_r, div_same by lia; trivial. 
    assert (to_Z x = 1 \/ to_Z x = -1) by (rewrite Z.gcd_0_r in H; lia).
    assert (x = of_Zmod (of_Z 0 1) \/ x = of_Zmod (of_Z 0 (-1))) as [->| ->].
    { case H1; [left|right]; apply to_Zmod_inj, to_Z_inj; rewrite H2; trivial. }
    trivial.
    trivial. }
  remember (Z.pred (- z)) as n.
  assert (0 < n) by lia.
  assert (Z.succ z = -n) as -> by lia; assert (z = -Z.succ n)  as -> by lia.
  rewrite !pow_opp_r, Private_pow_succ_r_nonneg by lia.
  case (Z.eqb_spec m 0) as [->|].
  2:rewrite inv_mul, !mul_assoc, mul_inv_same_r, mul_1_l by lia; trivial.
  apply to_Zmod_inj, to_Z_inj.
  repeat rewrite ?to_Zmod_inv, ?to_Zmod_mul, ?to_Z_mul, ?to_Z_inv, ?to_Zmod_pow, ?to_Z_pow, ?Zmod_0_r, ?invmod_0_r.
  rewrite Z.sgn_mul.
  assert (to_Z x = 1 \/ to_Z x = -1) as [->| ->] by (rewrite Z.gcd_0_r in H; lia).
  all : cbn [Z.sgn]; lia.
Qed.

Lemma pow_pred_r {m} (x : Zstar m) z : pow x (Z.pred z) = div (pow x z) x.
Proof.
  remember (Z.pred z) as n. assert (z = Z.succ n) as -> by lia.
  rewrite pow_succ_r, div_mul_l, mul_div_r_same_r; trivial; try lia.
Qed.

Lemma pow_1_l {m} z : @pow m one z = one.
Proof.
  induction z using Z.peano_ind;
    rewrite ?pow_0_r, ?pow_succ_r, ?pow_pred_r, ?IHz, ?mul_1_r, ?div_1_r; trivial.
Qed.

Lemma pow_add_r {m} (x : Zstar m) a b : pow x (a+b) = mul (pow x a) (pow x b).
Proof.
  induction a using Z.peano_ind;
    rewrite ?Z.add_0_l, ?Z.add_succ_l, ?Z.add_pred_l;
    rewrite ?pow_0_r, ?mul_1_l, ?pow_succ_r, ?pow_pred_r, ?IHa,
      <-?mul_inv_r, ?mul_assoc by lia; trivial.
  rewrite <-(mul_assoc _ (inv _)), (mul_comm (inv _)), mul_assoc; trivial.
Qed.

Lemma pow_sub_r {m} (x : Zstar m) a b  : pow x (a-b) = div (pow x a) (pow x b).
Proof. rewrite <-Z.add_opp_r, pow_add_r, pow_opp_r, mul_inv_r; trivial. Qed.

Lemma pow_mul_r {m} (x : Zstar m) a b : pow x (a*b) = pow (pow x a) b.
Proof.
  induction b using Z.peano_ind; rewrite ?Z.mul_0_r, ?Z.mul_succ_r, ?Z.mul_pred_r,
    ?pow_0_r, ?pow_1_l, ?pow_pred_r, ?pow_succ_r, ?pow_add_r, ?pow_sub_r, ?IHb;
    auto using mul_comm.
Qed.

Lemma pow_mul_l {m} (x y : Zstar m) n : pow (mul x y) n = mul (pow x n) (pow y n).
Proof.
  induction n using Z.peano_ind; rewrite ?pow_0_r, ?mul_1_l,
    ?pow_pred_r, ?pow_succ_r, ?pow_sub_r, ?IHn, <-?mul_inv_r, ?inv_mul;
    rewrite ?mul_assoc; f_equal; rewrite <-?mul_assoc; f_equal; auto using mul_comm.
Qed.

Lemma inv_pow_m1 m n : @inv m (pow (opp one) n) = pow (opp one) n.
Proof.
  induction n using Z.peano_ind;
  repeat rewrite ?pow_0_r, ?inv_1, ?pow_pred_r, ?pow_succ_r, <-?mul_inv_r,
    ?inv_mul, ?inv_opp, ?IHn by lia; trivial.
Qed.

Lemma prod_repeat {m} (a : Zstar m) n : ∏ repeat a n = pow a (Z.of_nat n).
Proof.
  induction n as [|n]; cbn [List.fold_right List.repeat];
    rewrite ?pow_0_r, ?mul_1_r, ?Nat2Z.inj_succ, ?pow_succ_r, ?IHn by lia; trivial.
Qed.

Lemma prod_map_mul {m} (a : Zstar m) xs :
  ∏ List.map (mul a) xs = mul (pow a (Z.of_nat (length xs))) (∏ xs).
Proof.
  induction xs as [|x xs]; cbn [List.fold_right List.map length];
    rewrite ?pow_0_r, ?mul_1_r, ?Nat2Z.inj_succ, ?pow_succ_r, ?IHxs by lia; trivial.
  repeat rewrite ?mul_assoc, ?(mul_comm _ x); trivial.
Qed.

Lemma prod_pow {m} z xs : ∏ map (fun x => pow x z) xs = pow (∏ xs) z :> Zstar m.
Proof.
  induction xs; intros; cbn [fold_right map]; rewrite ?pow_1_l, ?IHxs, ?pow_mul_l; trivial.
Qed.

Lemma prod_opp {m} xs : ∏ map (@opp m) xs = mul (pow (opp one) (Z.of_nat (length xs))) (∏ xs).
Proof.
  induction xs; cbn -[pow Z.of_nat];
    rewrite ?Nat2Z.inj_succ, ?pow_0_r, ?pow_succ_r, ?mul_1_l by lia; trivial.
  rewrite  ?mul_m1_l, ?IHxs, ?mul_opp_l, ?(mul_comm a), ?mul_assoc; trivial.
Qed.

(** ** [elements] *)

Lemma in_of_Zmod_filter {m} x (l : list (Zmod m)) :
  In x (map of_Zmod (filter (fun y : Zmod m => Z.gcd y m =? 1) l)) <-> In (to_Zmod x) l.
Proof.
  rewrite in_map_iff; setoid_rewrite filter_In; setoid_rewrite Z.eqb_eq.
  split. { intros (?&?&?&?); subst; rewrite to_Zmod_of_Zmod; auto. }
  exists x; eauto using of_Zmod_to_Zmod, Zmod.in_elements, to_Zmod_range.
Qed.

Lemma in_elements {m} (x : Zstar m) : In x (elements m).
Proof.
  cbv [elements]; pose proof coprime_to_Zmod x.
  case Z.eqb_spec; intros.
  { subst m; rewrite Z.gcd_0_r in H; cbv [In].
    rewrite <-2to_Zmod_inj_iff, !to_Zmod_opp, !to_Zmod_1.
    rewrite <-2unsigned_inj_iff, !unsigned_opp, !unsigned_1_neg, Zmod_0_r; lia. }
  rewrite in_of_Zmod_filter. auto using in_elements.
Qed.

Lemma NoDup_elements m : NoDup (elements m).
Proof.
  cbv [elements].
  case Z.eqb_spec; intros.
  { subst m. repeat constructor; cbv [In]; inversion_clear 1; trivial.
    eapply eqb_eq in H0; cbv in H0; discriminate. }
  eapply FinFun.Injective_map_NoDup_in, List.NoDup_filter, NoDup_elements.
  intros ?????%of_Zmod_inj; rewrite filter_In in *; trivial; lia.
Qed.

Lemma to_Zmod_elements m : List.map to_Zmod (elements m) = Zmod.invertibles m.
Proof.
  cbv [elements Zmod.invertibles].
  case Z.eqb_spec; intros; subst; trivial.
  erewrite map_map, map_ext_in, map_id; trivial.
  intros x [_ Hx]%List.filter_In; rewrite to_Zmod_of_Zmod; trivial; lia.
Qed.

(* (* TODO*)
Lemma in_positives {m} (x : Zstar m) : In x (positives m) <-> 0 < signed x.
Proof. cbv [positives]; rewrite in_of_Zmod_filter, <-in_positives; reflexivity. Qed.

Lemma in_negatives {m} (x : Zstar m) : In x (negatives m) <-> signed x < 0.
Proof. cbv [negatives]; rewrite in_of_Zmod_filter, <-in_negatives; reflexivity. Qed.

Lemma negatives_as_positives_odd (m : positive) (Hm : m mod 2 = 1) :
  negatives m = map opp (rev (positives m)).
Proof.
  cbv [positives negatives]; rewrite negatives_as_positives_odd by trivial.
  rewrite <-map_rev, <-filter_rev; set (rev _).
  erewrite map_map, map_ext_in with (f:=fun x => opp _), <-(map_map Zmod.opp of_Zmod).
  2: { intros ? [? ?%Z.eqb_eq]%filter_In.
    apply to_Zmod_inj; rewrite to_Zmod_opp, !to_Zmod_of_Zmod; trivial.
    rewrite to_Z_opp, Z.gcd_mod_l, Z.gcd_opp_l; trivial. }
  rewrite filter_map_swap; f_equal; f_equal; apply filter_ext.
  intros. rewrite to_Z_opp, Z.gcd_mod_l, Z.gcd_opp_l; trivial.
Qed.

Lemma NoDup_positives m : NoDup (positives m).
Proof.
  eapply FinFun.Injective_map_NoDup_in, List.NoDup_filter, NoDup_positives.
  intros ?????%of_Zmod_inj; rewrite filter_In in *; trivial; lia.
Qed.

Lemma NoDup_negatives m : NoDup (negatives m).
Proof.
  eapply FinFun.Injective_map_NoDup_in, List.NoDup_filter, NoDup_negatives.
  intros ?????%of_Zmod_inj; rewrite filter_In in *; trivial; lia.
Qed.

Lemma elements_by_sign {m} (Hm : m <> xH) : elements m = positives m ++ negatives m.
Proof.
  cbv [elements negatives positives].
  rewrite elements_by_sign; cbn [map filter List.app]; rewrite Z.gcd_0_l.
  case Z.eqb eqn:?; try lia.
  rewrite filter_app, map_app; reflexivity.
Qed.

Local Hint Unfold FinFun.Injective List.incl : core.
Lemma Permutation_mul_elements {m} (a : Zstar m) :
  Permutation (List.map (mul a) (elements m)) (elements m).
Proof.
  eauto 6 using Permutation.Permutation_map_same_l, FinFun.Injective_map_NoDup, NoDup_elements, mul_cancel_l, in_elements, of_Zmod_inj.
Qed.

Theorem euler {m} (a : Zstar m) : pow a (Z.of_nat (length (elements m))) = one.
Proof.
  epose proof prod_map_mul a (elements m) as P.
  erewrite prod_Permutation in P by eapply Permutation_mul_elements.
  rewrite <-mul_1_l in P at 1. eapply mul_cancel_r, eq_sym in P; trivial.
Qed.

Lemma to_Zmod_elements_prime p (H : prime p) :
  List.map to_Zmod (elements p) = List.tl (Zmod.elements p).
Proof. rewrite to_Zmod_elements, Zmod.invertibles_prime; trivial. Qed.

Lemma length_elements_prime p (H : prime p) : length (elements p) = Z.to_nat (p-1).
Proof.
  erewrite <-List.length_map, to_Zmod_elements, Zmod.length_invertibles_prime; trivial.
Qed.

Lemma length_positives_length_negatives_odd (m : positive) (Hm : m mod 2 = 1) :
  length (positives m) = length (negatives m).
Proof.
  rewrite negatives_as_positives_odd by trivial.
  rewrite ?length_map, ?filter_rev, ?length_rev; trivial.
Qed.

Lemma length_positives_odd {m : positive} (H : m mod 2 = 1) :
  length (positives m) = (length (elements m) / 2)%nat.
Proof.
  case (Pos.eqb_spec m 1) as [->|]; trivial.
  erewrite elements_by_sign, length_app, <-length_positives_length_negatives_odd; trivial.
  zify. rewrite Nat2Z.inj_div, Nat2Z.inj_add. zify; Z.to_euclidean_division_equations; lia.
Qed.

Lemma length_negatives_odd {m : positive} (H : m mod 2 = 1) :
  length (negatives m) = (length (elements m) / 2)%nat.
Proof.
  rewrite <-length_positives_length_negatives_odd, length_positives_odd; trivial.
Qed.

Lemma length_positives_prime (m : positive) (H : prime m) : length (positives m) = N.to_nat (Pos.pred_N m / 2).
Proof.
  pose proof @prime_ge_2 _ H.
  case (Pos.eq_dec m 2) as [->|]; trivial.
  pose proof odd_prime _ H ltac:(lia).
  pose proof length_positives_length_negatives_odd m.
  pose proof @length_elements_prime _ H as L.
  rewrite elements_by_sign, ?length_app in L by lia.
  zify; Z.to_euclidean_division_equations; nia.
Qed.

Lemma length_negatives_prime (m : positive) (H : prime m) : length (negatives m) = N.to_nat (m / 2).
Proof.
  pose proof @prime_ge_2 _ H.
  case (Pos.eq_dec m 2) as [->|]; trivial.
  pose proof odd_prime _ H ltac:(lia).
  rewrite <-length_positives_length_negatives_odd, length_positives_prime  by trivial.
  zify; Z.to_euclidean_division_equations; nia.
Qed.

Theorem fermat {m} (a : Zstar m) (H : prime m) : pow a (Z.pred m) = one.
Proof. erewrite <-euler, length_elements_prime; trivial; f_equal; lia. Qed.

Theorem fermat_inv {m} (a : Zstar m) (H : prime m) : pow a (m-2) = inv a.
Proof.
  eapply mul_cancel_l; rewrite mul_inv_same_r.
  erewrite <-pow_succ_r, <-euler, ?length_elements_prime; f_equal; trivial; lia.
Qed.

Theorem euler_criterion_square {p : positive} (Hp : prime p)
  (a sqrt_a : Zstar p) (Ha : pow sqrt_a 2 = a) : pow a ((p-1)/2) = one.
Proof.
  apply wlog_eq_Zstar_3; intro Hp'; pose proof odd_prime _ Hp Hp'.
  rewrite pow_2_r in Ha.
  rewrite <-(fermat sqrt_a Hp), <-Ha, <-pow_2_r, <-pow_mul_r; f_equal.
  Z.to_euclidean_division_equations; nia.
Qed.
*)

End Zstar.
End Base.

Module Export Inv.
Module Zmod.
Import Znumtheory Zmod.

Lemma mdiv_same {m} (a : Zmod m) : mdiv a a = of_Z m (Z.gcd a m).
Proof.
  rewrite <-mul_inv_l. apply to_Z_inj. rewrite to_Z_mul, to_Z_inv,
    to_Z_of_Z, invmod_ok; trivial.
Qed.

Lemma in_invertibles m (x : Zmod m) : List.In x (invertibles m) <-> Z.gcd x m = 1.
Proof.
  rewrite <-Zstar.to_Zmod_elements, in_map_iff; split.
  { intros (?&?&?); subst. apply Zstar.coprime_to_Zmod. }
  { eexists; rewrite Zstar.to_Zmod_of_Zmod; auto using Zstar.in_elements. }
Qed.

Lemma NoDup_invertibles {m} : List.NoDup (invertibles m).
Proof. 
  rewrite <-Zstar.to_Zmod_elements.
  eapply FinFun.Injective_map_NoDup, Zstar.NoDup_elements.
  cbv [FinFun.Injective]; auto using Zstar.to_Zmod_inj.
Qed.

Lemma mdiv_same_coprime {m} (a : Zmod m) (H : Z.gcd a m = 1) : mdiv a a = one.
Proof.
  case (Z.eqb_spec m 0) as [->|].
  { apply unsigned_inj; rewrite unsigned_mdiv; rewrite Z.gcd_0_r in *.
    assert (to_Z a = -1 \/ to_Z a = 1) as [->| ->] by lia; trivial. }
  rewrite mdiv_same, H; trivial. Qed.

Lemma mdiv_same_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) : mdiv x x = one.
Proof.
  pose proof prime_ge_2 _ Hm.
  apply mdiv_same_coprime. apply to_Z_nz in H. pose proof to_Z_range x.
  apply Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia.
Qed.

Lemma mul_inv_same_l_coprime {m} (x : Zmod m) (H : Z.gcd x m = 1) :
  mul (inv x) x = one.
Proof.
  pose proof Zstar.mul_inv_same_l (Zstar.of_Zmod x) as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_mul, Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in E by trivial; exact E.
Qed.

Lemma mul_inv_same_r_coprime {m} (x : Zmod m) (H : Z.gcd x m = 1) :
  mul x (inv x) = one.
Proof. rewrite mul_comm, mul_inv_same_l_coprime; trivial. Qed.

Lemma mul_inv_same_l_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) :
  mul (inv x) x = one.
Proof. intros; rewrite ?mul_inv_l, ?mdiv_same_prime; trivial. Qed.

Lemma mul_inv_same_r_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) :
  mul x (inv x) = one.
Proof. rewrite mul_comm, mul_inv_same_l_prime; trivial. Qed.

Lemma field_theory m (Hm : prime m) :
  @Field_theory.field_theory (Zmod m) zero one add mul sub opp mdiv inv eq.
Proof.
  split; auto using ring_theory, prime_ge_2, mul_inv_r, mul_inv_same_l_prime.
  apply one_neq_zero; pose proof prime_ge_2 _ Hm; lia.
Qed.

Lemma inv_nz_prime {m} (x : Zmod m) (Hm : prime m) (Hx : x <> zero) : inv x <> zero.
Proof.
  pose proof prime_ge_2 _ Hm as Hm'.
  intro HX; exfalso; apply (@one_neq_zero m); [lia|].
  pose proof mul_inv_same_l_prime x Hm Hx as H; rewrite HX, mul_0_l in H; auto.
Qed.

Lemma inv_inv {m} (x : Zmod m) (H : Z.gcd x m = 1): inv (inv x) = x.
Proof.
  pose proof Zstar.inv_inv (Zstar.of_Zmod x) as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite 2Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod in E by trivial; exact E.
Qed.

Lemma inv_inv_prime {m} (x : Zmod m) (Hm : prime m): inv (inv x) = x.
Proof.
  case (eqb_spec x zero) as [|Hx]; subst.
  { apply to_Z_inj. rewrite to_Z_inv, invmod_0_l; trivial. }
  pose proof to_Z_nz x ltac:(trivial); pose proof to_Z_range x.
  pose proof prime_ge_2 _ Hm.
  apply inv_inv, Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  case (Z.eq_dec m 1); intros; subst; trivial.
  symmetry; rewrite <-mul_1_l, mul_inv_r, mdiv_same_coprime; trivial.
  apply Zmod.gcd_1_m.
Qed.

Lemma div_1_r {m} x : @mdiv m x one = x.
Proof. cbv [mdiv]. rewrite inv_1, mul_1_r; trivial. Qed.

Lemma mul_cancel_l_coprime {m} (a b c : Zmod m)
  (Ha : Z.gcd a m = 1) (H : mul a b = mul a c) : b = c.
Proof.
  apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l_coprime, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_r_coprime {m} (a b c : Zmod m)
  (Ha : Z.gcd a m = 1) (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l_coprime in H; trivial. Qed.

Lemma mul_cancel_l_prime {m} (a b c : Zmod m) (Hm : prime m) (Ha : a <> zero)
  (H : mul a b = mul a c) : b = c.
Proof.
  apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l_prime, !mul_1_l in H; trivial.
Qed.

Lemma mul_0_iff_prime {p} (Hp : prime p) (a b : Zmod p) :
  mul a b = zero <-> a = zero \/ b = zero.
Proof.
  case (eqb_spec a zero) as [], (eqb_spec b zero) as [];
    split; (intros [|]||intros); subst; rewrite ?mul_0_l, ?mul_0_r in *; auto.
  case H. apply (f_equal (mul (inv b))) in H1; rewrite mul_0_r in H1.
  rewrite mul_comm, <-mul_assoc, mul_inv_same_r_prime, mul_1_r in H1; trivial.
Qed.

Lemma pow_succ_r_coprime {m} (x : Zmod m) z (H : Z.gcd x m = 1) : pow x (Z.succ z) = mul x (pow x z).
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_succ_r (Zstar.of_Zmod x) z) as E.
  rewrite Zstar.to_Zmod_mul, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_pred_r_coprime {m} (x : Zmod m) z (H : Z.gcd x m = 1) : pow x (Z.pred z) = mdiv (pow x z) x.
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_pred_r (Zstar.of_Zmod x) z) as E.
  rewrite Zstar.to_Zmod_div, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_add_r_coprime {m} (x : Zmod m) a b (H : Z.gcd x m = 1) : pow x (a + b) = mul (pow x a) (pow x b).
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_add_r (Zstar.of_Zmod x) a b) as E.
  rewrite Zstar.to_Zmod_mul, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_mul_r_coprime {m} (x : Zmod m) a b (H : Z.gcd x m = 1) : pow x (a * b) = pow (pow x a) b.
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_mul_r (Zstar.of_Zmod x) a b) as E.
  rewrite ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_mul_l_coprime {m} (x y : Zmod m) z (Hx : Z.gcd x m = 1) (Hy : Z.gcd y m = 1) :
  pow (mul x y) z = mul (pow x z) (pow y z).
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_mul_l (Zstar.of_Zmod x) (Zstar.of_Zmod y) z) as E.
  rewrite ?Zstar.to_Zmod_mul, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_mul, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_1_l {m} z : @pow m one z = one.
Proof.
  epose proof f_equal Zstar.to_Zmod (Zstar.pow_1_l (m:=m) z) as E.
  rewrite ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_1 in E; trivial.
Qed.

Lemma pow_mul_r_nonneg {m} (x : Zmod m) a b (Ha : 0 <= a) (Hb : 0 <= b) :
  pow x (a*b) = pow (pow x a) b.
Proof.
  generalize dependent b; generalize dependent a; refine (natlike_ind _ _ _).
  { intros. rewrite Z.mul_0_l, ?pow_0_r, pow_1_l; trivial. }
  intros a Ha IH b Hb; rewrite Z.mul_succ_l, Z.add_comm.
  rewrite pow_succ_r_nonneg, pow_add_r_nonneg, IH, pow_mul_l_nonneg; auto; nia.
Qed.

Lemma square_roots_opp_prime {p} (Hp : prime p) (x y : Zmod p) :
  pow x 2 = pow y 2 <-> (x = y \/ x = opp y).
Proof.
  rewrite 2pow_2_r.
  intuition subst; rewrite ?mul_opp_opp; trivial; revert H.
  rewrite <-sub_eq_0_iff, Base.Zmod.square_roots_opp_prime_subproof.
  rewrite mul_0_iff_prime, 2sub_eq_0_iff ; intuition idtac.
Qed.

Lemma square_roots_1_prime {p} (Hp : prime p) (x : Zmod p) :
  pow x 2 = one <-> (x = one \/ x = opp one).
Proof.
  rewrite <-(mul_1_l one) at 1. rewrite <-pow_2_r.
  rewrite square_roots_opp_prime; intuition idtac.
Qed.

Lemma mul_cancel_r_prime {m} (a b c : Zmod m) (Hm : prime m) (Ha : a <> zero)
  (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l_prime in H; trivial. Qed.

Theorem fermat_nz {m} (a : Zmod m) (Ha : a <> zero) (H : prime m) :
  pow a (Z.pred m) = one.
Proof.
  rewrite <-to_Z_inj_iff, to_Z_0 in Ha; pose proof to_Z_range a as Ha'.
  pose proof Zstar.fermat (Zstar.of_Zmod a) H as G%(f_equal Zstar.to_Zmod).
  rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in G; trivial.
  apply Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia.
Qed.

Theorem fermat {m} (a : Zmod m) (H : prime m) : pow a m = a.
Proof.
  case (eqb_spec a zero); intros.
  { subst a. rewrite pow_0_l; trivial; lia. }
  { assert (Z.pos m = Z.succ (Z.pred m)) as -> by lia.
    rewrite Zmod.pow_succ_nonneg_r, fermat_nz, mul_1_r; trivial; lia. }
Qed.

Theorem fermat_inv {m} (a : Zmod m) (Ha : a <> zero) (H : prime m) :
  pow a (m-2) = inv a.
Proof.
  pose proof Zstar.fermat_inv (Zstar.of_Zmod a) H as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod in *; trivial.
  pose proof to_Z_range a; apply to_Z_nz in Ha.
  eapply Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia.
Qed.
End Zmod.

Module Z.
Import Znumtheory.

Theorem fermat_nz (m a : Z) (Hm : prime m) (Ha : a mod m <> 0) :
  a^(m-1) mod m = 1.
Proof.
  pose proof prime_ge_2 _ Hm; case m as [|m|]; try lia; [].
  apply Zmod.of_Z_nz in Ha; pose (Zmod.fermat_nz (Zmod.of_Z m a) Ha Hm) as E.
  apply (f_equal Zmod.to_Z) in E.
  rewrite Zmod.to_Z_pow_nonneg, Zmod.to_Z_of_Z, Z.mod_pow_l, Zmod.to_Z_1 in E; lia.
Qed.

Theorem fermat (m a : Z) (Hm : prime m) : a^m mod m = a mod m.
Proof.
  pose proof prime_ge_2 _ Hm; case m as [|m|]; try lia; [].
  pose (Zmod.fermat (Zmod.of_Z m a) Hm) as E.
  apply (f_equal Zmod.to_Z) in E.
  rewrite Zmod.to_Z_pow_nonneg, Zmod.to_Z_of_Z, Z.mod_pow_l in E; lia.
Qed.
End Z.

