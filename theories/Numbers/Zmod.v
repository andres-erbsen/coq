Require Import NArith ZArith ZModOffset Lia Numbers.ZmodDef.
Require Import Bool.Bool Lists.List Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Local Coercion N.pos : positive >-> N.
Local Coercion Z.of_N : N >-> Z.
Local Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
Local Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Module Export Base.
Module Zmod.
Export ZmodDef.Zmod.

(** ** Unsigned conversions to [Z] *)

Lemma to_Z_range {m} (x : Zmod m) : 0 <= to_Z x < Z.pos m.
Proof.
  case x as [x H]; cbv [to_Z Private_to_N].
  apply Is_true_eq_true, N.ltb_lt, N2Z.inj_lt in H; auto using N2Z.is_nonneg.
Qed.

Lemma to_Z_inj m (x y : Zmod m) : to_Z x = to_Z y -> x = y.
Proof.
  cbv [to_Z Private_to_N]; destruct x, y.
  intros H%N2Z.inj; destruct H.
  apply f_equal, Is_true_hprop.
Qed.

Lemma to_Z_inj_iff {m} (x y : Zmod m) : to_Z x = to_Z y <-> x = y.
Proof. split; try apply to_Z_inj; congruence. Qed.

Lemma to_Z_of_small_Z {m} n pf : to_Z (of_small_Z m n pf) = n.
Proof. apply Z2N.id; lia. Qed.

Lemma to_Z_of_Z {m} z : to_Z (of_Z m z) = z mod (Z.pos m).
Proof. apply to_Z_of_small_Z. Qed.

Lemma of_small_Z_ok {m} n pf : of_small_Z m n pf = of_Z m n.
Proof. apply to_Z_inj. rewrite to_Z_of_small_Z, to_Z_of_Z, Z.mod_small; lia. Qed.

Lemma of_Z_to_Z {m} x : of_Z m (to_Z x) = x.
Proof. apply to_Z_inj. rewrite to_Z_of_Z, Z.mod_small; trivial; apply to_Z_range. Qed.

Lemma to_Z_of_Z_small {m} n (H : 0 <= n < Z.pos m) : to_Z (of_Z m n) = n.
Proof. rewrite to_Z_of_Z, Z.mod_small; trivial. Qed.

Lemma mod_to_Z {m} (x : Zmod m) : to_Z x mod (Z.pos m) = to_Z x.
Proof. rewrite Z.mod_small; auto using to_Z_range. Qed.

Lemma of_Z_mod {m} x : of_Z m (x mod Z.pos m) = of_Z m x.
Proof. apply to_Z_inj. rewrite ?to_Z_of_Z, ?Z.mod_mod; lia. Qed.

Lemma of_Z_inj {m} x y : of_Z m x = of_Z m y <-> x mod m = y mod m.
Proof.
  split.
  { intros H%(f_equal to_Z). rewrite 2to_Z_of_Z in *; trivial. }
  { rewrite <-of_Z_mod. rewrite <-(of_Z_mod y). congruence. }
Qed.

(** ** Signed conversions to [Z] *)

Lemma smod_unsigned {m} (x : Zmod m) : Z.smodulo (unsigned x) m = signed x.
Proof.
  pose proof to_Z_range x. cbv [signed Z.smodulo Z.omodulo] in *.
  case (Z.ltb_spec (Z.double x) m) as []; cycle 1;
  rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq 1) by (Z.quot_rem_to_equations; lia);
    Z.quot_rem_to_equations; try lia.
Qed.

Lemma signed_range {m} (x : Zmod m) : -m <= 2*signed x < m.
Proof. rewrite <-smod_unsigned. pose proof Z.smod_pos_bound x m; lia. Qed.

Lemma signed_inj m (x y : Zmod m) : signed x = signed y -> x = y.
Proof.
  rewrite <-2 smod_unsigned; intros H%Z.mod_inj_smod; rewrite ?mod_to_Z in *.
  apply to_Z_inj, H.
Qed.

Lemma signed_inj_iff {m} (x y : Zmod m) : signed x = signed y <-> x = y.
Proof. split; try apply signed_inj; congruence. Qed.

Lemma mod_signed {m} (x : Zmod m) : signed x mod m = unsigned x.
Proof. rewrite <-smod_unsigned, Z.mod_smod, mod_to_Z; trivial. Qed.

Lemma smod_signed {m} (x : Zmod m) : Z.smodulo (signed x) m = signed x.
Proof. rewrite <-smod_unsigned, Z.smod_smod; trivial. Qed.

Lemma signed_of_Z {m} z : signed (of_Z m z) = Z.smodulo z m.
Proof. rewrite <-smod_unsigned, to_Z_of_Z, Z.smod_mod; trivial. Qed.

Lemma signed_of_Z_small {m} z (H : - Z.pos m <= 2 * z - Z.rem m 2 < m) :
  signed (of_Z m z) = z.
Proof. rewrite signed_of_Z, Z.smod_small; trivial. Qed.

Lemma signed_of_Z_even_small {m} (Hm : Z.rem (Z.pos m) 2 = 0)
  z (H : - Z.pos m <= 2 * z < m) : signed (of_Z m z) = z.
Proof. rewrite signed_of_Z, Z.smod_even_small; trivial. Qed.

Lemma signed_of_Z_pow2_small {w : positive} z (H : - 2^w <= 2 * z < 2^w) :
  signed (of_Z (2^w)%positive z) = z.
Proof. rewrite signed_of_Z, Pos2Z.inj_pow, Z.smod_pow2_small; lia. Qed.

Lemma signed_small {m} (x : Zmod m) (H : 2*x < m) : signed x = unsigned x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double x) m) as []; lia.
Qed.

Lemma signed_large {m} (x : Zmod m) (H : m <= 2*x) : signed x = x-m.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double x) m) as []; lia.
Qed.

Lemma to_Z_pos {m} (x : Zmod m) (H : 0 <= signed x) : unsigned x = signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *. case (Z.ltb_spec (Z.double x) m) as []; lia.
Qed.

Lemma to_Z_neg {m} (x : Zmod m) (H : signed x < 0) : unsigned x = m + signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *. case (Z.ltb_spec (Z.double x) m) as []; lia.
Qed.

Lemma signed_neg_iff {m} (x : Zmod m) :
  signed x < 0 <-> m <= 2 * unsigned x.
Proof.
  pose proof to_Z_range x.
  destruct (Z.leb_spec m (2 * unsigned x)); intuition try lia.
  { rewrite signed_large; lia. }
  { rewrite signed_small in *; lia. }
Qed.

Lemma signed_small_iff {m} (x : Zmod m) :
  signed x = unsigned x <-> 2 * unsigned x < m.
Proof.
  pose proof to_Z_range x.
  destruct (Z.ltb_spec (2 * unsigned x) m); intuition try lia.
  { rewrite signed_small in *; lia. }
  { pose proof signed_neg_iff x; intuition try lia. }
Qed.

Lemma signed_nonneg_iff {m} (x : Zmod m) :
  0 <= signed x <-> 2 * unsigned x < m.
Proof.
  pose proof to_Z_range x.
  destruct (Z.ltb_spec (2 * unsigned x) m); intuition try lia.
  { rewrite signed_small; lia. }
  { rewrite signed_large in *; lia. }
Qed.

Lemma signed_pos_iff {m} (x : Zmod m) :
  0 < signed x <-> 0 < 2 * unsigned x < m.
Proof. pose proof signed_nonneg_iff x; pose proof signed_small_iff x; lia. Qed.

(** ** Constants *)

Lemma to_Z_0 m : @to_Z m zero = 0. Proof. trivial. Qed.

Lemma to_Z_0_iff {m} x : @to_Z m x = 0 <-> x = zero.
Proof. rewrite <-to_Z_inj_iff, to_Z_0; reflexivity. Qed.

Lemma signed_0 m : @signed m zero = 0. Proof. trivial. Qed.

Lemma signed_0_iff {m} x : @signed m x = 0 <-> x = zero.
Proof. setoid_rewrite <-signed_inj_iff. reflexivity. Qed.

Lemma of_Z_0 {m} : of_Z m 0 = zero. Proof. trivial. Qed.

Lemma of_Z_1 {m} : of_Z m 1 = one. Proof. apply to_Z_inj. trivial. Qed.

Lemma to_Z_1 {m : positive} (Hm : 2 <= m) : @to_Z m one = 1.
Proof. cbv [one]; rewrite to_Z_of_Z_small; lia. Qed.

Lemma to_Z_1_1 : @to_Z 1 one = 0. trivial. Qed.

Lemma signed_1 {m : positive} (Hm : 3 <= m) : @signed m one = 1.
Proof. cbv [one]; rewrite signed_of_Z, Z.smod_small; Z.to_euclidean_division_equations; lia. Qed.

Lemma signed_1_1 : @signed 1 one = 0. Proof. trivial. Qed.

Lemma signed_1_2 : @signed 2 one = -1. Proof. trivial. Qed.

Lemma to_Z_nz {m} (x : Zmod m) (H : x <> zero) : to_Z x <> 0.
Proof. intros X; apply H, to_Z_inj. rewrite X; trivial. Qed.

Lemma one_neq_zero {m : positive} (Hm : 2 <= m) : one <> zero :> Zmod m.
Proof.
  intro H. apply (f_equal to_Z) in H.
  rewrite to_Z_1, to_Z_0 in H; lia.
Qed.

Lemma one_eq_zero_mod_1 : @one 1 = zero. Proof. trivial. Qed.

Lemma one_eq_zero_iff {m : positive} : one = zero :> Zmod m <-> m = xH.
Proof.
  case (Pos.eq_dec m xH) as [->|].
  { intuition auto using one_eq_zero_mod_1. }
  pose proof @one_neq_zero m ltac:(lia); intuition idtac.
Qed.

(** ** Ring operations *)

Lemma to_Z_add {m} (x y : Zmod m) : to_Z (add x y) = (to_Z x + to_Z y) mod m.
Proof.
  pose proof to_Z_range x; pose proof to_Z_range y.
  cbv [add]. rewrite of_small_Z_ok, to_Z_of_Z.
  case (Z.ltb_spec (x + y) m) as [?|?]; trivial.
  rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq 1) by lia; lia.
Qed.

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

Lemma to_Z_sub {m} (x y : Zmod m) : to_Z (sub x y) = (to_Z x - to_Z y) mod m.
Proof.
  pose proof to_Z_range x; pose proof to_Z_range y.
  cbv [sub]. rewrite of_small_Z_ok, to_Z_of_Z.
  case (Z.leb_spec 0 (x - y)) as [?|?]; trivial.
  rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq (-1)) by lia; lia.
Qed.

Lemma signed_sub {m} x y : signed (@sub m x y) = Z.smodulo (signed x-signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_sub, Z.smod_mod, Z.smod_idemp_sub; trivial. Qed.

Lemma to_Z_opp {m} (x : Zmod m) : to_Z (opp x) = (- to_Z x) mod m.
Proof. apply to_Z_sub. Qed.

Lemma signed_opp {m} x : signed (@opp m x) = Z.smodulo (-signed x) m.
Proof. rewrite <-!smod_unsigned, to_Z_opp, Z.smod_mod, Z.smod_idemp_opp; trivial. Qed.

Lemma opp_zero {m} : @opp m zero = zero.
Proof. apply to_Z_inj. rewrite to_Z_opp, to_Z_0, Z.mod_0_l; lia. Qed.

Lemma opp_overflow {m : positive} (Hm : m mod 2 = 0)
  (x : Zmod m) (Hx : signed x = -m/2) : opp x = x.
Proof.
  apply signed_inj. rewrite signed_opp.
  rewrite (Z.smod_diveq 1); Z.to_euclidean_division_equations; nia.
Qed.

Lemma signed_opp_small {m} (x : Zmod m) (H : signed x <> -m/2) :
  signed (opp x) = Z.opp (signed x).
Proof.
  rewrite signed_opp. apply Z.smod_small.
  pose proof signed_range x.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma to_Z_mul {m} (x y : Zmod m) : to_Z (mul x y) = (to_Z x * to_Z y) mod m.
Proof. cbv [mul]; rewrite ?to_Z_of_Z; trivial. Qed.

Lemma signed_mul {m} x y : signed (@mul m x y) = Z.smodulo (signed x*signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_mul, Z.smod_mod, Z.smod_idemp_mul; trivial. Qed.

Local Ltac r := try apply to_Z_inj; cbv [one];
  (* Note: rewrite is slow, and autorewrite isn't faster *)
  repeat rewrite ?to_Z_of_Z, ?to_Z_add, ?to_Z_mul, ?to_Z_sub, ?to_Z_opp,
    ?mod_to_Z, ?Z.mod_0_l, ?Z.mul_1_l, ?Z.add_0_l, ?Z.add_mod_idemp_l,
    ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
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
  Context {m : positive}.
  Add Ring __Private__Zmod_base_ring : (ring_theory m).
  Implicit Types a b c : Zmod m.
  Lemma mul_1_r a : mul a one = a. Proof. ring. Qed.
  Lemma mul_0_l a : mul zero a = zero. Proof. ring. Qed.
  Lemma mul_0_r a : mul a zero = zero. Proof. ring. Qed.
  Lemma opp_opp a : opp (opp a) = a. Proof. ring. Qed.
  Lemma opp_inj a b : opp a = opp b -> a = b. Proof. intros H; ring [H]. Qed.
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

Lemma to_Z_udiv {m} x y : to_Z (@udiv m x y) = Z.div x y.
Proof. apply to_Z_of_small_Z. Qed.

Lemma to_Z_umod {m} x y : to_Z (@umod m x y) = Z.modulo x y.
Proof. apply to_Z_of_small_Z. Qed.

Lemma udiv_0_r {m} x : @udiv m x zero = zero.
Proof. cbv [udiv]. apply to_Z_inj. rewrite to_Z_of_small_Z, to_Z_0, Zdiv_0_r; trivial. Qed.

Lemma umod_0_r {m} x : @umod m x zero = x.
Proof. cbv [umod]. apply to_Z_inj. rewrite to_Z_of_small_Z, to_Z_0, Zmod_0_r; trivial. Qed.

Lemma signed_sdiv {m} x y : @signed m (sdiv x y) = Z.smodulo (signed x / signed y) m.
Proof. apply signed_of_Z. Qed.

Lemma signed_smod {m} x y : @signed m (smod x y) = Z.smodulo (signed x mod signed y) m.
Proof. apply signed_of_Z. Qed.

Lemma sdiv_0_r {m} x : @sdiv m x zero = zero.
Proof. cbv [sdiv]. apply to_Z_inj; rewrite to_Z_of_Z, signed_0, Zdiv_0_r; trivial. Qed.

Lemma smod_0_r {m} x : @smod m x zero = x.
Proof. cbv [smod]. apply signed_inj. rewrite signed_of_Z, signed_0, Zmod_0_r, smod_signed; trivial. Qed.

Lemma signed_sdiv_small {m : positive} x y :
  ~ (signed x = -m/2 /\ signed y = -1 /\ m mod 2 = 0) ->
  @signed m (sdiv x y) = signed x / signed y.
Proof.
  intros H; rewrite signed_sdiv; apply Z.smod_small.
  pose proof signed_range x; pose proof signed_range y.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma sdiv_overflow {m : positive} x y
  (Hm : m mod 2 = 0) (Hx : signed x = -m/2) (Hy : signed y = -1) :
  @sdiv m x y = x.
Proof.
  apply signed_inj; rewrite signed_sdiv, Hx, Hy.
  rewrite (Z.smod_diveq 1); Z.to_euclidean_division_equations; nia.
Qed.


Lemma to_Z_inv {m} x : to_Z (@inv m x) = Znumtheory.invmod x m.
Proof. apply to_Z_of_small_Z. Qed.

Lemma inv_0 {m} : @inv m zero = zero. Proof. trivial. Qed.


Lemma to_Z_mdiv {m} x y : to_Z (@mdiv m x y) = x * Znumtheory.invmod y m mod m.
Proof. cbv [mdiv]. rewrite to_Z_mul, to_Z_inv; trivial. Qed.

Lemma mdiv_0_r {m} x : @mdiv m x zero = zero.
Proof. cbv [mdiv]. rewrite inv_0, mul_0_r; trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = mdiv x y.
Proof. apply to_Z_inj. cbv [mdiv inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r {m} x y : mul x (@inv m y) = mdiv x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

(** ** Bitwise operations *)
Import Nbitwise.

Lemma to_Z_and {m} x y : @to_Z m (and x y) = Z.land x y.
Proof.
  cbv [and]; rewrite to_Z_of_small_Z, N2Z.inj_land, 2Z2N.id;
  try apply to_Z_range; trivial.
Qed.

Lemma to_Z_ndn {m} x y : @to_Z m (ndn x y) = Z.ldiff x y.
Proof.
  cbv [ndn]; rewrite to_Z_of_small_Z, N2Z.inj_ldiff, 2Z2N.id;
  try apply to_Z_range; trivial.
Qed.

Lemma testbit_high_pow2 {w} (x : Zmod (2^w)) i (Hi : (w <= i)%Z) : Z.testbit x i = false.
Proof. rewrite <-mod_to_Z, ?Pos2Z.inj_pow, Z.mod_pow2_bits_high; lia. Qed.

Lemma to_Z_or_pow2 {w} x y : @to_Z (2^w) (or x y) = Z.lor x y.
Proof.
  cbv [or]; rewrite to_Z_of_Z; apply Z.bits_inj; intros i; destruct (Z.ltb_spec i w);
  repeat rewrite ?Pos2Z.inj_pow, ?Z.lor_spec, ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?testbit_high_pow2 by lia; trivial.
Qed.

Lemma to_Z_xor_pow2 {w} x y : @to_Z (2^w) (xor x y) = Z.lxor x y.
Proof.
  cbv [xor]; rewrite to_Z_of_Z; apply Z.bits_inj; intros i; destruct (Z.ltb_spec i w);
  repeat rewrite ?Pos2Z.inj_pow, ?Z.lxor_spec, ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?testbit_high_pow2 by lia; trivial.
Qed.

Lemma xor_zero_iff {w} (x y : Zmod (2^w)) : xor x y = zero <-> x = y.
Proof.
  rewrite <-2to_Z_inj_iff, to_Z_0, to_Z_xor_pow2, Z.lxor_eq_0_iff; reflexivity.
Qed.

Lemma eqb_xor_zero {w} (x y : Zmod (2^w)) : eqb (xor x y) zero = eqb x y.
Proof.
  pose proof xor_zero_iff x y.
  destruct (eqb_spec (xor x y) zero), (eqb_spec x y); intuition congruence.
Qed.

Lemma to_Z_not {w} x : @to_Z (2^w) (not x) = Z.lxor x (Z.ones w).
Proof.
  cbv [not]; rewrite to_Z_of_Z, ?Pos2Z.inj_pow; apply Z.bits_inj'; intros i Hi.
  case (Z.ltb_spec i w) as []; repeat rewrite
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lxor_spec,
    ?Z.ones_spec_high, ?Z.ones_spec_low, ?testbit_high_pow2
    by lia; trivial.
Qed.

(** ** Shifts *)
Lemma to_Z_sru {m} x n : @to_Z m (sru x n) = Z.shiftr x n.
Proof.
  cbv [sru]. pose proof (to_Z_range x).
  rewrite to_Z_of_small_Z, N2Z.inj_shiftr, Z2N.id; lia.
Qed.

Lemma signed_srs {m} x n : @signed m (srs x n) = Z.shiftr (signed x) n.
Proof.
  cbv [srs]; rewrite signed_of_Z; apply Z.smod_small.
  rewrite Z.shiftr_div_pow2 by lia; pose proof signed_range x.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma to_Z_srs {m} x n : @to_Z m (srs x n) = Z.shiftr (signed x) n mod m.
Proof. rewrite <-mod_to_Z, <-Z.mod_smod, <-signed_srs, <-signed_of_Z, of_Z_to_Z; trivial. Qed.

Lemma to_Z_slu {m} x n : @to_Z m (slu x n) = Z.shiftl x n mod m.
Proof. cbv [slu]; rewrite to_Z_of_Z; trivial. Qed.


(** ** Lemmas for equalities with different moduli *)

Lemma to_Z_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_Z a = to_Z b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_Z_inj. Qed.

Lemma to_Z_inj_dep_iff {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n /\ to_Z a = to_Z b <-> existT _ _ a = existT _ _ b.
Proof.
  split. { intros []; auto using to_Z_inj_dep. }
  intros H; inversion_sigma; subst; auto.
Qed.

Lemma to_Z_eq_rect {m} (a : Zmod m) n p : to_Z (eq_rect _ _ a n p) = to_Z a.
Proof. case p; trivial. Qed.

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


(** ** Bitvector operations that vary the modulus *)

Lemma to_Z_range_bitvec {n} (x : bitvec n) : 0 <= to_Z x < Z.pow 2 n.
Proof.
  pose proof to_Z_range x; rewrite ?Pos2Z.inj_shiftl, Z.shiftl_1_l in *; lia.
Qed.

Lemma to_Z_app {n m} a b : to_Z (@app n m a b) = Z.lor a (Z.shiftl b n).
Proof.
  cbv [app]. rewrite to_Z_of_Z, Z.mod_small; trivial.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Pos2Z.inj_shiftl, Z.shiftl_1_l, N2Z.inj_add, Z.pow_add_r by lia.
  (* lor <= add *)
  pose proof to_Z_range_bitvec a; pose proof to_Z_range_bitvec b.
  pose proof Z.lor_nonneg a (b * 2^n). pose proof Z.land_nonneg a (b * 2^n).
  pose proof Z.add_lor_land a (b * 2^n). nia.
Qed.

Lemma to_Z_firstn {n w} a : to_Z (@firstn n w a) = a mod 2^n.
Proof.
  cbv [firstn]. rewrite to_Z_of_Z, Pos2Z.inj_shiftl, Z.shiftl_1_l; lia.
Qed.

Lemma to_Z_skipn {n w} a : to_Z (@skipn n w a) = a/2^n.
Proof.
  cbv [skipn]. rewrite to_Z_of_Z, Z.mod_small; rewrite ?Z.shiftr_div_pow2; try lia.
  rewrite Pos2Z.inj_shiftl, Z.shiftl_1_l.
  pose proof to_Z_range_bitvec a.
  case (N.ltb_spec n w) as [].
  { replace (Z.of_N w) with (N.sub w n+n) in H by lia; rewrite Z.pow_add_r in H by lia.
    Z.div_mod_to_equations; nia. }
  { pose proof Z.pow_le_mono_r 2 w n; rewrite Z.div_small; lia. }
Qed.

Lemma to_Z_extract start pastend {w} (a : bitvec w) (H : N.le start pastend) :
  to_Z (extract start pastend a) = a/2^start mod 2^(pastend-start).
Proof. cbv [extract]; rewrite to_Z_firstn, to_Z_skipn, N2Z.inj_sub; trivial. Qed.

Lemma firstn_app {n m} a b : firstn n (@app n m a b) = a.
Proof.
  apply to_Z_inj; rewrite to_Z_firstn, to_Z_app.
  symmetry. rewrite <-mod_to_Z at 1; symmetry.
  rewrite Pos2Z.inj_shiftl, Z.shiftl_1_l, <-!Z.land_ones by lia.
  apply Z.bits_inj'; intros i Hi.
  repeat rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.shiftl_spec, ?Z.testbit_ones,
    ?Z.mod_pow2_bits_high, ?testbit_high_pow2, ?(Z.testbit_neg_r(*workaround*)b),
    ?Zle_imp_le_bool, ?Bool.andb_true_l by lia; trivial.
  destruct (Z.ltb_spec i n); try Btauto.btauto.
  rewrite (Z.testbit_neg_r b) by lia; Btauto.btauto.
Qed.

Lemma skipn_app {n m} a b : existT _ _ (skipn n (@app n m a b)) = existT _ _ b.
Proof.
  pose proof to_Z_range_bitvec a. eapply to_Z_inj_dep. { f_equal. lia. }
  rewrite to_Z_skipn, <-Z.shiftr_div_pow2, to_Z_app, Z.shiftr_lor, Z.shiftr_shiftl_l by lia.
  erewrite Z.shiftr_div_pow2, Z.sub_diag, Z.shiftl_0_r, Z.div_small, Z.lor_0_l; lia.
Qed.

Lemma skipn_app' {n m} a b : exists pf, skipn n (@app n m a b) = eq_rect _ Zmod b _ pf.
Proof.
  pose proof skipn_app a b as E; symmetry in E; inversion_sigma. exists E1.
  apply to_Z_inj. rewrite to_Z_eq_rect, <-E2, to_Z_eq_rect; trivial.
Qed.

Lemma skipn_app'' {n m} a b pf : skipn n (@app n m a b) = eq_rect _ Zmod b _ pf.
Proof.
  ecase (skipn_app' a b) as [?->]; apply to_Z_inj; rewrite !to_Z_eq_rect; trivial.
Qed.

Lemma skipn_app''' {n m} a b :
  skipn n (@app n m a b) = of_Z _ (to_Z (skipn n (@app n m a b))).
Proof.
  ecase (skipn_app' a b) as [?->]; apply to_Z_inj; rewrite to_Z_eq_rect, to_Z_of_Z.
  assert (n + m - n = m)%N as -> by lia. rewrite mod_to_Z; trivial.
Qed.

Lemma app_assoc {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l) :
  existT _ _ (app a (app b c)) = existT _ _ (app (app a b) c).
Proof.
  pose proof to_Z_range_bitvec a. eapply to_Z_inj_dep. { f_equal. lia. }
  rewrite ?to_Z_app.
  apply Z.bits_inj'; intros i Hi; case (Z.leb_spec 0 (i - n)) as [];
  repeat rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.shiftl_spec, ?Z.testbit_ones,
    ?Z.sub_add_distr, ?N2Z.inj_add, ?Bool.orb_assoc,
    (*workaround:*) ?(Z.testbit_neg_r (Z.shiftl c m)), ?(Z.testbit_neg_r c)
    by lia; trivial.
Qed.

Lemma app_assoc' {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l) : exists pf,
     app a (app b c) = eq_rect _ _ (app (app a b) c) _ pf.
Proof.
  pose proof app_assoc a b c as E; symmetry in E; inversion_sigma.
  exists E1. apply to_Z_inj; rewrite <-E2, !to_Z_eq_rect; trivial.
Qed.

Lemma app_assoc'' {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l) pf :
     app a (app b c) = eq_rect _ _ (app (app a b) c) _ pf.
Proof.
  ecase (app_assoc' a b c) as [?->]; apply to_Z_inj; rewrite !to_Z_eq_rect; trivial.
Qed.

Lemma app_assoc''' {n m l} (a : bitvec n) (b : bitvec m) (c : bitvec l) :
  app a (app b c) = of_Z _ (to_Z (app (app a b) c)).
Proof.
  ecase (app_assoc' a b c) as [?->]; apply to_Z_inj;
    rewrite !to_Z_eq_rect, !to_Z_of_Z, ?N.add_assoc, mod_to_Z; trivial.
Qed.

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

Lemma Private_to_Z_pow_N {m} x n : @to_Z m (pow_N x n) = to_Z x ^ n mod m.
Proof.
  revert x; induction n using N.peano_ind; intros; try apply to_Z_of_small_Z.
  rewrite  ?Private_pow_N_succ_r, ?to_Z_mul,
    ?N2Z.inj_succ, ?Z.pow_succ_r, ?IHn, ?Z.mul_mod_idemp_r; trivial; lia.
Qed.

Lemma to_Z_pow_nonneg_r {m} x z (Hz : 0 <= z) : @to_Z m (pow x z) = x^z mod m.
Proof. rewrite Private_pow_nonneg, Private_to_Z_pow_N; f_equal; f_equal; lia. Qed.
Notation to_Z_pow_nonneg := to_Z_pow_nonneg_r.

Lemma to_Z_pow_neg_r {m} x z (Hz : z < 0) : @to_Z m (pow x z) = Znumtheory.invmod (to_Z x^(-z)) m.
Proof.
  rewrite pow_neg, to_Z_inv, to_Z_pow_nonneg_r by lia.
  rewrite Znumtheory.invmod_mod_l; f_equal; f_equal; lia.
Qed.

Lemma of_Z_pow {m} x n (H : 0 <= n) : of_Z m (x ^ n) = pow (of_Z m x) n.
Proof.
  apply to_Z_inj. rewrite to_Z_pow_nonneg_r, !to_Z_of_Z, Z.mod_pow_l; trivial.
Qed.

Lemma Private_pow_N_0_l {m} n (Hn : n <> 0%N) : @pow_N m zero n = zero.
Proof. apply to_Z_inj; rewrite Private_to_Z_pow_N, to_Z_0, ?Z.pow_0_l; trivial; lia. Qed.

Lemma pow_0_l {m} n (Hn : n <> 0) : @pow m zero n = zero.
Proof. cbv [pow]; case Z.ltb eqn:?; rewrite Private_pow_N_0_l, ?inv_0 by lia; auto. Qed.


(** ** Misc *)

Lemma of_Z_nz {m} x (H : (x mod Z.pos m <> 0)%Z) : of_Z m x <> zero.
Proof.
  intro Hx. apply (f_equal to_Z) in Hx. rewrite to_Z_of_Z, to_Z_0 in Hx; contradiction.
Qed.

Lemma hprop_Zmod_1 (a b : Zmod 1) : a = b.
Proof.
  pose proof to_Z_range a; pose proof to_Z_range b; apply to_Z_inj; lia.
Qed.

Lemma wlog_eq_Zmod_2 {m} (a b : Zmod m) (k : 2 <= m -> a = b) : a = b.
Proof.
  destruct (Pos.eq_dec 1 m) as [e|ne].
  { destruct e; auto using hprop_Zmod_1. }
  { apply k; lia. }
Qed.

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

Lemma opp_1_neq_1 {m : positive} (Hm : 3 <= m) : @opp m one <> one.
Proof.
  intros H%(f_equal signed); rewrite signed_opp_small in H;
    rewrite signed_1 in *; Z.to_euclidean_division_equations; lia.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  apply wlog_eq_Zmod_2; intros.
  apply to_Z_inj; rewrite to_Z_inv, to_Z_1, Z.invmod_1_l; trivial.
Qed.

(** ** Absolute value *)

Lemma abs_0 m : @abs m zero = zero.
Proof. cbv [abs]. rewrite signed_0; trivial. Qed.

Lemma abs_1 m : @abs m one = one.
Proof.
  apply wlog_eq_Zmod_2; intros.
  case (Pos.eq_dec m 2) as [->|]; trivial.
  cbv [abs]. rewrite signed_1 by lia; trivial.
Qed.

Lemma abs_pos {m} x : 0 < @signed m x -> abs x = x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_neg {m} x : @signed m x < 0 -> abs x = opp x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_opp {m} x : @abs m (opp x) = abs x.
Proof.
  cbv [abs]; pose proof signed_range x; rewrite ?opp_opp.
  case (Z.eqb_spec (signed x) (- Z.pos m / 2)) as [], (Z.eqb_spec (m mod 2) 0) as [];
  try solve [rewrite opp_overflow; trivial].
  all : pose proof signed_opp_small x ltac:(Z.div_mod_to_equations; nia) as G; rewrite ?G.
  all :destruct (Z.ltb_spec (-signed x) 0), (Z.ltb_spec (signed x) 0); trivial; apply signed_inj; lia.
Qed.

Lemma abs_abs {m} (x : Zmod m) : abs (abs x) = abs x.
Proof. unfold abs at 2; case Z.ltb; rewrite ?abs_opp; trivial. Qed.

Lemma signed_abs_small {m} x (H : signed x <> - Z.pos m / 2) :
  @signed m (abs x) = Z.abs (signed x).
Proof.
  cbv [abs]; destruct (Z.ltb_spec (signed x) 0); [rewrite signed_opp_small|]; lia.
Qed.

Lemma signed_abs_odd {m : positive} (Hm : m mod 2 = 1) x :
  @signed m (abs x) = Z.abs (signed x).
Proof.
  cbv [abs]; destruct (Z.ltb_spec (signed x) 0); [rewrite signed_opp_small|];
    (pose proof signed_range x; Z.div_mod_to_equations; nia).
Qed.

Lemma signed_abs_nonneg_small {m} (x : Zmod m) (H : signed x <> - m / 2):
  0 <= signed (abs x).
Proof. rewrite signed_abs_small; lia. Qed.

Lemma signed_abs_nonneg_odd {m : positive} (Hm : m mod 2 = 1) (x : Zmod m) :
  0 <= signed (abs x).
Proof. rewrite signed_abs_odd; lia. Qed.

Lemma gcd_opp_m {m} x : Z.gcd (@opp m x) m = Z.gcd x m.
Proof. rewrite to_Z_opp, Z.gcd_mod, Z.gcd_opp_r, Z.gcd_comm; lia. Qed.

Lemma gcd_abs_m_odd {m : positive} (Hm : m mod 2 = 1) x :
  Z.gcd (@abs m x) m = Z.gcd x m.
Proof. rewrite <-2mod_signed, 2Z.gcd_mod, signed_abs_odd, Z.gcd_abs_r; lia. Qed.

Lemma pow_opp_2 {m} (x : Zmod m) : pow (opp x) 2 = pow x 2.
Proof. rewrite !pow_2_r. rewrite ?mul_opp_opp; trivial. Qed.

Lemma pow_abs_2 {m} (x : Zmod m) : pow (abs x) 2 = pow x 2.
Proof. rewrite !pow_2_r. cbv [abs]; case Z.ltb; rewrite ?mul_opp_opp; trivial. Qed.

(** Elements *)

Lemma length_elements m : length (elements m) = Pos.to_nat m.
Proof. cbv [elements]. rewrite List.length_map, List.length_seq; trivial. Qed.

Lemma nth_error_elements {m} n : List.nth_error (elements m) n =
  if (Nat.ltb n (Pos.to_nat m)) then Some (of_Z _ (Z.of_nat n)) else None.
Proof.
  cbv [elements].
  rewrite List.nth_error_map, List.nth_error_seq.
  case Nat.ltb; trivial.
Qed.

Lemma in_elements {m} a : List.In a (elements m).
Proof.
  apply List.nth_error_In with (n:=Z.to_nat a); rewrite nth_error_elements.
  pose proof to_Z_range a.
  destruct (Nat.ltb_spec (Z.to_nat a) (Pos.to_nat m)); [|lia].
  rewrite Z2Nat.id, of_Z_to_Z; trivial; lia.
Qed.

Lemma NoDup_elements m : List.NoDup (elements m).
Proof.
  cbv [elements].
  eapply List.NoDup_map_inv with (f := fun x : Zmod m => Z.to_nat x).
  erewrite List.map_map, List.map_ext_in, List.map_id; trivial using List.seq_NoDup.
  intros a Ha. apply List.in_seq in Ha; cbn [Nat.add] in Ha.
  rewrite to_Z_of_Z, Z.mod_small, Nat2Z.id; lia.
Qed.

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

Lemma NoDup_positives {m} : NoDup (positives m).
Proof.
  pose proof NoDup_elements m as H; rewrite elements_by_sign in H.
  eauto using NoDup_app_remove_l, NoDup_app_remove_r.
Qed.

Lemma NoDup_negatives {m} : NoDup (negatives m).
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

Lemma invertibles_prime (p : positive) (H : Znumtheory.prime p) :
  invertibles p = List.tl (elements p).
Proof.
  cbv [invertibles elements].
  replace (Pos.to_nat p) with (S (Pos.to_nat p-1)) by lia;
    progress cbn [List.seq List.tl List.map List.filter].
  rewrite Z.gcd_0_l; destruct (Z.eqb_spec (Z.abs p) 1).
  { pose proof Znumtheory.prime_ge_2 p H; lia. }
  erewrite filter_map_swap, filter_ext_in, filter_true; trivial; cbv beta.
  intros i ?%List.in_seq; apply Z.eqb_eq.
  eapply Znumtheory.Zgcd_1_rel_prime, Znumtheory.rel_prime_le_prime; trivial.
  rewrite Zmod.to_Z_of_Z, Z.mod_small; lia.
Qed.

Lemma length_invertibles_prime (p : positive) (H : Znumtheory.prime p) :
  length (invertibles p) = N.to_nat (Pos.pred_N p).
Proof.
  rewrite invertibles_prime, List.tl_length, Zmod.length_elements; trivial; lia.
Qed.

End Zmod.

Module Zstar.
Import Znumtheory Zmod Zstar.

(** ** Conversions to [Zmod] *)

Lemma coprime_to_Zmod {m} (a : Zstar m) : Z.gcd (to_Zmod a) m = 1.
Proof.
  cbv [Zmod.to_Z Zmod.Private_to_N to_Zmod Private_to_N Zmod.of_small_Z].
  case a as [a H]; apply Is_true_eq_true in H; rewrite N2Z.id; lia.
Qed.
Notation to_Zmod_range := coprime_to_Zmod.

Lemma to_Zmod_inj {m} (x y : Zstar m) : to_Zmod x = to_Zmod y -> x = y.
Proof.
  cbv [to_Zmod Private_to_N]; destruct x, y.
  intros H%(f_equal Zmod.to_Z); rewrite !Zmod.to_Z_of_small_Z in H.
  apply N2Z.inj in H; destruct H.
  apply f_equal, Is_true_hprop.
Qed.

Lemma to_Zmod_inj_iff {m} (x y : Zstar m) : to_Zmod x = to_Zmod y <-> x = y.
Proof. split; auto using to_Zmod_inj; congruence. Qed.

Lemma to_Zmod_of_coprime_Zmod {m} (x : Zmod m) pf : to_Zmod (of_coprime_Zmod x pf) = x.
Proof.
  apply to_Z_inj; pose proof Zmod.to_Z_range x.
  cbv [to_Zmod of_coprime_Zmod Private_to_N]; rewrite to_Z_of_small_Z; lia.
Qed.

Lemma to_Zmod_of_Zmod' {m} (x : Zmod m) :
  to_Zmod (of_Zmod x) = if Z.eqb (Z.gcd x m) 1 then x else Zmod.one.
Proof. apply to_Zmod_of_coprime_Zmod. Qed.

Lemma to_Zmod_of_Zmod {m} (x : Zmod m) (H : Z.gcd x m = 1) : to_Zmod (of_Zmod x) = x.
Proof. rewrite to_Zmod_of_Zmod'; case (Z.eqb_spec (Z.gcd x m) 1); congruence. Qed.

Lemma of_Zmod_to_Zmod {m} x : @of_Zmod m (to_Zmod x) = x.
Proof. pose (to_Zmod_range x). apply to_Zmod_inj. rewrite to_Zmod_of_Zmod; auto. Qed.

Lemma to_Zmod_1 {m} : @to_Zmod m one = Zmod.one.
Proof.
  intros; apply to_Zmod_of_Zmod.
  case (Pos.eqb_spec m 1) as [->|];
  rewrite ?Zmod.to_Z_1, ?Z.gcd_1_l, ?Z.gcd_1_r by lia; lia.
Qed.

Lemma of_Zmod_inj {m} (x y : Zmod m) :
  Z.gcd x m = 1 -> Z.gcd y m = 1 -> of_Zmod x = of_Zmod y -> x = y.
Proof. intros ? ? H%(f_equal to_Zmod); rewrite 2 to_Zmod_of_Zmod in H; trivial. Qed.

Lemma to_Zmod_0_iff {m} (a : Zstar m) : to_Zmod a = zero <-> m = xH.
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

Lemma wlog_eq_Zstar_3 {m} (a b : Zstar m) (k : 3 <= m -> a = b) : a = b.
Proof.
  destruct (Pos.eq_dec 1 m) as [e|].
  { destruct e; auto using hprop_Zstar_1. }
  destruct (Pos.eq_dec 2 m) as [e'|].
  { destruct e'; auto using hprop_Zstar_2. }
  { apply k; lia. }
Qed.

Lemma of_Zmod_1 {m} : @of_Zmod m Zmod.one = one.
Proof.
  apply wlog_eq_Zstar_3; intros.
  apply to_Zmod_inj. rewrite to_Zmod_1, to_Zmod_of_Zmod; trivial.
  rewrite to_Z_1, Z.gcd_1_l; lia.
Qed.

Lemma to_Z_0_iff {m} (a : Zstar m) : to_Z a = 0 <-> m = 1%positive.
Proof.
  split; intros H;
  specialize (to_Z_range a); specialize (to_Zmod_range a); rewrite ?H;
  rewrite ?Z.gcd_0_l; lia.
Qed.

Lemma to_Z_nz_iff {m} (a : Zstar m) : to_Z a <> 0 <-> m <> 1%positive.
Proof. rewrite to_Z_0_iff; reflexivity. Qed.

Lemma to_Z_nz {m} (a : Zstar m) : m <> 1%positive -> to_Z a <> 0.
Proof. apply to_Z_nz_iff. Qed.

(** ** [opp] *)

Lemma to_Zmod_opp {m} (a : Zstar m) : to_Zmod (opp a) = Zmod.opp a.
Proof.
  apply to_Zmod_of_Zmod.
  rewrite to_Z_opp, Z.gcd_mod, Z.gcd_opp_r, Z.gcd_comm by lia.
  apply coprime_to_Zmod.
Qed.

Lemma opp_opp {m} (a : Zstar m) : opp (opp a) = a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_opp. apply Zmod.opp_opp. Qed.

Lemma opp_inj {m} (a b : Zstar m) : opp a = opp b -> a = b.
Proof. rewrite <-2to_Zmod_inj_iff, 2to_Zmod_opp. apply opp_inj. Qed.

Lemma opp_distinct_odd {m : positive} (Hm : m mod 2 = 1) (Hm' : 3 <= m) a :
  a <> opp a :> Zstar m.
Proof.
  intro X; pose proof to_Z_range a; pose proof to_Z_nz a ltac:(lia).
  apply to_Zmod_inj_iff, Zmod.to_Z_inj_iff in X.
  rewrite ?to_Zmod_opp, Zmod.to_Z_opp, Z_mod_nz_opp_full in *;
    rewrite ?mod_to_Z in *; Z.div_mod_to_equations; nia.
Qed.

Lemma opp_1_neq_1 {m : positive} (Hm : 3 <= m) : opp one <> one :> Zstar m.
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

(** ** [mul] *)

Lemma to_Zmod_mul {m} (a b : Zstar m) : @to_Zmod m (mul a b) = Zmod.mul a b.
Proof. cbv [mul]. rewrite to_Zmod_of_coprime_Zmod; trivial. Qed.

Lemma mul_assoc {m} a b c : @mul m a (mul b c) = mul (mul a b) c.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul. apply Zmod.mul_assoc. Qed.
Lemma mul_comm {m} a b : @mul m a b = mul b a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul; apply Zmod.mul_comm. Qed.
Lemma mul_1_l {m} a : @mul m one a = a. Proof.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, to_Zmod_1. apply Zmod.mul_1_l. Qed.
Lemma mul_1_r {m} a : @mul m a one = a. Proof. rewrite <-mul_comm; apply mul_1_l. Qed.

Lemma mul_opp_l {m} (a b : Zstar m) : mul (opp a) b = opp (mul a b).
Proof. apply to_Zmod_inj; repeat rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_l. Qed.
Lemma mul_opp_r {m} (a b : Zstar m) : mul a (opp b) = opp (mul a b).
Proof. apply to_Zmod_inj; repeat rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_r. Qed.
Lemma mul_opp_opp {m} a b : @mul m (opp a) (opp b) = mul a b.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_opp. Qed.

Local Notation "∏ xs" := (List.fold_right mul one xs) (at level 40).

(** ** [inv] and [div] *)

Lemma to_Zmod_inv {m} x : to_Zmod (@inv m x) = Zmod.inv x.
Proof.
  cbv [inv]. rewrite to_Zmod_of_Zmod; trivial.
  rewrite to_Z_inv; auto using coprime_invmod, to_Zmod_range.
Qed.

Lemma not_of_Zmod_inv (m := 6%positive) (x := Zmod.of_Z _ 4) : of_Zmod (@Zmod.inv m x) <> inv (of_Zmod x).
Proof. inversion 1. Qed.

Lemma to_Zmod_div {m} x y : to_Zmod (@div m x y) = Zmod.mdiv x y.
Proof. cbv [div]. rewrite to_Zmod_mul, to_Zmod_inv, mul_inv_r; trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = div x y.
Proof. apply to_Zmod_inj. cbv [div inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r {m} x y : mul x (@inv m y) = div x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

Lemma div_same {m} (a : Zstar m) : div a a = one.
Proof.
  apply wlog_eq_Zstar_3; intros; apply to_Zmod_inj, to_Z_inj.
  rewrite to_Zmod_div, to_Z_mdiv, Z.mul_comm, invmod_coprime, to_Zmod_1, to_Z_1; try lia. apply to_Zmod_range.
Qed.

Lemma div_mul_l {m} (a b c : Zstar m) : div (mul a b) c = mul a (div b c).
Proof. rewrite <-mul_inv_l, mul_comm, <-mul_assoc, mul_inv_r; trivial. Qed.

Lemma mul_inv_same_l {m} x : mul (@inv m x) x = one.
Proof. apply wlog_eq_Zstar_3; rewrite mul_inv_l, div_same; trivial; apply to_Z_range. Qed.

Lemma mul_inv_same_r {m} x : mul x (@inv m x) = one.
Proof. rewrite mul_comm; apply mul_inv_same_l. Qed.

Lemma inv_inv {m} x : inv (@inv m x) = x.
Proof.
  rewrite <-mul_1_r, <-(mul_inv_same_l (inv x)), (mul_comm _ (inv x)); auto.
  rewrite mul_assoc, (mul_comm x), (mul_inv_same_l x), mul_1_l; auto.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  apply wlog_eq_Zstar_3; intros.
  symmetry; rewrite <-mul_1_l, mul_inv_r, div_same; trivial.
Qed.

Lemma mul_cancel_l {m} (a b c : Zstar m) (H : mul a b = mul a c) : b = c.
Proof.
  apply wlog_eq_Zstar_3; intros. apply (f_equal (fun x => mul (inv a) x)) in H.
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
  apply (f_equal (mul (inv b))), (f_equal (mul (inv a))) in H.
  rewrite mul_1_r in H; rewrite <-H; clear H; set (inv (mul _ _)) as x.
  rewrite !mul_assoc, (mul_comm (inv _)), <-(mul_assoc (inv _)).
  repeat rewrite ?mul_inv_same_l, ?mul_1_r, ?mul_1_l; trivial.
Qed.

Lemma div_div_r_same {m} (a b : Zstar m) : div a (div a b) = b.
Proof. rewrite <-!mul_inv_r, inv_mul, mul_assoc, inv_inv, mul_inv_same_r, mul_1_l. trivial. Qed.

Lemma inv_div {m} (x y : Zstar m) : inv (div x y) = div y x.
Proof. rewrite <-!mul_inv_l, inv_mul, inv_inv, mul_comm; trivial. Qed.

(** ** [prod] *)

Lemma prod_Permutation {m} one (xs ys : list (Zstar m)) (H : Permutation xs ys) :
  List.fold_right mul one xs = List.fold_right mul one ys.
Proof. induction H; cbn; repeat rewrite ?mul_assoc, ?(mul_comm x); try congruence.
Qed.

Lemma prod_app {m} xs ys : ∏ (xs ++ ys) = mul (∏ xs) (∏ ys) :> Zstar m.
Proof.
  induction xs; cbn; cbn [List.fold_right List.app];
    rewrite ?mul_1_l, ?IHxs, ?mul_assoc; trivial.
Qed.

Lemma prod_flat_map {m} f (xs : list (Zstar m)) :
  ∏ flat_map f xs = ∏ (map (fun x => ∏ f x) xs) :> Zstar m.
Proof. induction xs; cbn; rewrite ?prod_app, ?IHxs; eauto. Qed.

(** ** [pow] *)

Lemma to_Zmod_pow {m} (a : Zstar m) z : @to_Zmod m (pow a z) = Zmod.pow a z.
Proof.
  apply wlog_eq_Zmod_2; intros.
  pose proof coprime_to_Zmod a.
  apply to_Zmod_of_Zmod.
  case (ltac:(lia):z = 0 \/ z < 0 \/ 0 < z) as [->|[]].
  { rewrite pow_0_r, to_Z_1, Z.gcd_1_l; trivial. }
  all : rewrite ?to_Z_pow_nonneg_r, ?to_Z_pow_neg_r by lia.
  { apply coprime_invmod, Z.coprime_pow_l; lia. }
  { rewrite Z.gcd_mod, Z.gcd_comm, Z.coprime_pow_l; try lia. }
Qed.

Lemma pow_1_l {m} z : @pow m one z = one.
Proof.
  apply wlog_eq_Zstar_3; intros.
  apply to_Zmod_inj, to_Z_inj. rewrite to_Zmod_pow, to_Zmod_1.
  case (Z.leb_spec 0 z) as [].
  { rewrite to_Z_pow_nonneg_r, to_Z_1, Z.pow_1_l, Z.mod_small; lia. }
  { rewrite to_Z_pow_neg_r, to_Z_1, Z.pow_1_l, Z.invmod_1_l; lia. }
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

Lemma Private_coprime_Zmodpow {m} (a : Zstar m) z (H : 0 <= z ) : Z.gcd (Zmod.pow a z) m = 1.
Proof.
  pose proof coprime_to_Zmod a.
  rewrite Zmod.to_Z_pow_nonneg_r, Z.gcd_mod_l, Z.coprime_pow_l; lia.
Qed.

Lemma pow_opp_r {m} a (z : Z) : @pow m a (-z) = inv (pow a z).
Proof.
  apply wlog_eq_Zstar_3; intros. pose proof Private_coprime_Zmodpow a as G.
  case (Z.ltb_spec (-z) 0) as [].
  { cbv [pow inv]; f_equal.
    rewrite pow_neg, Z.opp_involutive, to_Zmod_of_Zmod; trivial. apply G; lia. }
  case (Z.eqb_spec z 0) as [->|].
  { cbv [pow inv]; f_equal.
    rewrite !Zmod.pow_0_r, to_Zmod_of_Zmod, Zmod.inv_1; trivial.
    rewrite to_Z_1, Z.gcd_1_l; lia. }
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
  { cbv [pow]; cbn. fold (@inv m x). rewrite of_Zmod_1, mul_inv_r, div_same; trivial. }
  remember (Z.pred (- z)) as n.
  assert (Z.succ z = -n) as -> by lia; assert (z = -Z.succ n)  as -> by lia.
  rewrite !pow_opp_r, Private_pow_succ_r_nonneg by lia.
  rewrite inv_mul, !mul_assoc, mul_inv_same_r, mul_1_l; trivial.
Qed.

Lemma pow_pred_r {m} (x : Zstar m) z : pow x (Z.pred z) = div (pow x z) x.
Proof.
  remember (Z.pred z) as n. assert (z = Z.succ n) as -> by lia.
  rewrite pow_succ_r, div_mul_l, mul_div_r_same_r; trivial.
Qed.

Lemma pow_add_r {m} (x : Zstar m) a b : pow x (a+b) = mul (pow x a) (pow x b).
Proof.
  induction a using Z.peano_ind;
    rewrite ?Z.add_0_l, ?Z.add_succ_l, ?Z.add_pred_l;
    rewrite ?pow_0_r, ?mul_1_l, ?pow_succ_r, ?pow_pred_r, ?IHa,
      <-?mul_inv_r, ?mul_assoc; trivial.
  rewrite <-(mul_assoc _ (inv _)), (mul_comm (inv _)), mul_assoc; trivial.
Qed.

Lemma pow_sub_r {m} (x : Zstar m) a b : pow x (a-b) = div (pow x a) (pow x b).
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

Lemma prod_repeat {m} (a : Zstar m) n : ∏ repeat a n = pow a (Z.of_nat n).
Proof.
  induction n as [|n]; cbn [List.fold_right List.repeat];
    rewrite ?pow_0_r, ?mul_1_r, ?Nat2Z.inj_succ, ?pow_succ_r, ?IHn; trivial.
Qed.

Lemma prod_map_mul {m} (a : Zstar m) xs :
  ∏ List.map (mul a) xs = mul (pow a (Z.of_nat (length xs))) (∏ xs).
Proof.
  induction xs as [|x xs]; cbn [List.fold_right List.map length];
    rewrite ?pow_0_r, ?mul_1_r, ?Nat2Z.inj_succ, ?pow_succ_r, ?IHxs; trivial.
  repeat rewrite ?mul_assoc, ?(mul_comm _ x); trivial.
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
Proof. cbv [elements]. rewrite in_of_Zmod_filter. apply in_elements. Qed.

Lemma in_positives {m} (x : Zstar m) : In x (positives m) <-> 0 < signed x.
Proof. cbv [positives]; rewrite in_of_Zmod_filter, <-in_positives; reflexivity. Qed.

Lemma in_negatives {m} (x : Zstar m) : In x (negatives m) <-> signed x < 0.
Proof. cbv [negatives]; rewrite in_of_Zmod_filter, <-in_negatives; reflexivity. Qed.

Lemma NoDup_elements {m} : NoDup (elements m).
Proof.
  eapply FinFun.Injective_map_NoDup_in, List.NoDup_filter, NoDup_elements.
  intros ?????%of_Zmod_inj; rewrite filter_In in *; trivial; lia.
Qed.

Lemma NoDup_positives {m} : NoDup (positives m).
Proof.
  eapply FinFun.Injective_map_NoDup_in, List.NoDup_filter, NoDup_positives.
  intros ?????%of_Zmod_inj; rewrite filter_In in *; trivial; lia.
Qed.

Lemma NoDup_negatives {m} : NoDup (negatives m).
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

Lemma to_Zmod_elements m : List.map to_Zmod (elements m) = Zmod.invertibles m.
Proof.
  cbv [elements Zmod.invertibles].
  erewrite map_map, map_ext_in, map_id; trivial.
  intros x [_ Hx]%List.filter_In; rewrite to_Zmod_of_Zmod; trivial; lia.
Qed.

Lemma to_Zmod_elements_prime (m : positive) (H : prime m) :
  List.map to_Zmod (elements m) = List.tl (Zmod.elements m).
Proof. rewrite to_Zmod_elements, Zmod.invertibles_prime; trivial. Qed.

Lemma length_elements_prime (m : positive) (H : prime m) : length (elements m) = N.to_nat (Pos.pred_N m).
Proof.
  erewrite <-List.length_map, to_Zmod_elements, Zmod.length_invertibles_prime; trivial.
Qed.

Lemma length_positives_length_negatives_odd (m : positive) (Hm : m mod 2 = 1) :
  length (positives m) = length (negatives m).
Proof.
  cbv [positives negatives].
  rewrite negatives_as_positives_odd by trivial.
  rewrite filter_map_swap, ?length_map, ?filter_rev, ?length_rev.
  symmetry; erewrite filter_ext; [reflexivity|]; intros.
  rewrite to_Z_opp, Z.gcd_mod, Z.gcd_comm, Z.gcd_opp_l; reflexivity || lia.
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

End Zstar.
End Base.

Module Export Inv.
Module Zmod.
Import Znumtheory Zmod.

Lemma mdiv_same {m} (a : Zmod m) : mdiv a a = of_Z m (Z.gcd a m).
Proof.
  rewrite <-mul_inv_l. apply to_Z_inj. rewrite to_Z_mul, to_Z_inv,
    to_Z_of_Z, invmod_ok by inversion 1; trivial.
Qed.

Lemma in_invertibles m (x : Zmod m) : List.In x (invertibles m) <-> Z.gcd x m = 1.
Proof.
  pose @in_elements; cbv [invertibles]; rewrite filter_In; intuition trivial; lia.
Qed.

Lemma NoDup_invertibles {m} : List.NoDup (invertibles m).
Proof. apply NoDup_filter, NoDup_elements. Qed.

Lemma mdiv_same_coprime {m} (a : Zmod m) (H : Z.gcd a m = 1) : mdiv a a = one.
Proof. rewrite mdiv_same, H; trivial. Qed.

Lemma mdiv_same_prime {m} (x : Zmod m) (Hm : prime m) (H : x <> zero) : mdiv x x = one.
Proof.
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

Lemma field_theory (m : positive) (Hm : prime m) :
  @Field_theory.field_theory (Zmod m) zero one add mul sub opp mdiv inv eq.
Proof.
  split; auto using ring_theory, one_neq_zero, prime_ge_2, mul_inv_r, mul_inv_same_l_prime.
Qed.

Lemma inv_nz_prime {m} (x : Zmod m) (Hm : prime m) (Hx : x <> zero) : inv x <> zero.
Proof.
  intro HX; exfalso; apply (@one_neq_zero m); auto using prime_ge_2.
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
  apply inv_inv, Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  case (Pos.eq_dec m 1); intros; subst; trivial.
  symmetry; rewrite <-mul_1_l, mul_inv_r, mdiv_same_coprime; trivial.
  rewrite to_Z_1, Z.gcd_1_l; lia.
Qed.

Lemma mul_cancel_l_coprime {m} (a b c : Zmod m)
  (Ha : Z.gcd a m = 1) (H : mul a b = mul a c) : b = c.
Proof.
  apply wlog_eq_Zmod_2; intros. apply (f_equal (fun x => mul (inv a) x)) in H.
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

Lemma mul_0_iff_prime {p : positive} (Hp : prime p) (a b : Zmod p) :
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

Lemma square_roots_opp_prime {p : positive} (Hp : prime p) (x y : Zmod p) :
  pow x 2 = pow y 2 <-> (x = y \/ x = opp y).
Proof.
  rewrite 2pow_2_r.
  intuition subst; rewrite ?mul_opp_opp; trivial; revert H.
  rewrite <-sub_eq_0_iff, Base.Zmod.square_roots_opp_prime_subproof.
  rewrite mul_0_iff_prime, 2sub_eq_0_iff ; intuition idtac.
Qed.

Lemma square_roots_1_prime {p : positive} (Hp : prime p) (x : Zmod p) :
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

End Inv.
