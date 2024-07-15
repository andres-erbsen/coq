Require Import NArith ZArith ZModOffset Lia ZmodDef ZmodSqrtDef Zmod.
Require Import Bool.Bool Lists.List Sorting.Permutation.
Require Import ZArith.Pfactor.
Import ListNotations.


(* TODO: move *)
Lemma Permutation_partition [A] f (l : list A) : Permutation l (fst (partition f l) ++ snd (partition f l)).
Proof.
  induction l; cbn [partition]; trivial.
  case partition eqn:?, f; cbn [fst snd app]; eauto using Permutation_cons_app.
Qed.
Lemma filter_filter [A] f g (l : list A) : filter f (filter g l) = filter (fun x => f x && g x) l.
Proof.
  induction l; cbn [filter]; trivial.
  case g; cbn [filter]; case f; cbn [andb]; congruence.
Qed.
Lemma andb_implied_r a b : (a = true -> b = true) -> a && b = a.
Proof. case a, b; trivial. intros H. case H; trivial. Qed.
Lemma negb_existsb [A] f (l : list A) : negb (existsb f l) = forallb (fun x => negb (f x)) l.
Proof.
  induction l; cbn [negb orb existsb forallb]; trivial.
  case f; rewrite ?IHl; trivial.
Qed.
Lemma existsb_as_filter [A] f (l : list A) : existsb f l = negb (length (filter f l) =? 0)%nat.
Proof.
  induction l; trivial.
  cbn [existsb filter]; case f; rewrite ?IHl; trivial.
Qed.

(* TODO: move *)
Lemma NoDup_app [A] (l l' : list A) : NoDup l -> NoDup l' -> (forall x, not (In x l /\ In x l')) -> NoDup (l++l').
Proof.
  intros H G; induction H; intros U; trivial.
  cbn [app]; constructor; [|firstorder idtac].
  rewrite in_app_iff; intros [X|X]; try tauto.
  case (U x); cbn [In]; eauto.
Qed.
Lemma NoDup_list_prod [A B] l l' : NoDup l -> NoDup l' -> NoDup (@list_prod A B l l').
Proof.
  intros H G; induction H; intros; cbn [list_prod]; [constructor|].
  apply NoDup_app; trivial.
  { eapply FinFun.Injective_map_NoDup, G. inversion 1; trivial. }
  intros [] [(?&[-> ->]%pair_equal_spec&?)%in_map_iff []%in_prod_iff]; tauto.
Qed.
Lemma list_prod_nil_l [A B] l : @list_prod A B nil l = nil.
Proof. trivial. Qed.
Lemma list_prod_cons_l [A B] (x : A) l (l' : list B) :
  list_prod (x::l) l' = map (pair x) l' ++ list_prod l l'.
Proof. trivial. Qed.
Lemma list_prod_map_l [A A' B] (f : A -> A') l (l' : list B) :
  list_prod (map f l) l' = map (fun '(a, b) => (f a, b)) (list_prod l l').
Proof.
  induction l; rewrite ?list_prod_cons, ?map_cons, ?list_prod_cons_l,
    ?map_app, ?map_map, ?IHl; trivial.
Qed.
Lemma list_prod_map_r [A B B'] (f : B -> B') (l : list A) l' :
  list_prod l (map f l') = map (fun '(a, b) => (a, f b)) (list_prod l l').
Proof.
  induction l; rewrite ?list_prod_cons, ?map_cons, ?list_prod_cons_l,
    ?map_app, ?map_map, ?IHl; trivial.
Qed.
Lemma list_prod_map_map [A A' B B'] (f : A -> A') (g : B -> B') l l' :
  list_prod (map f l) (map g l') = map (fun '(x, y) => (f x, g y)) (list_prod l l').
Proof.
  rewrite list_prod_map_l, list_prod_map_r, ?map_map; apply map_ext.
  intros []; trivial.
Qed.
Lemma list_prod_filter_l [A B] (f : A -> _) l (l' : list B) :
  list_prod (filter f l) l' = filter (fun p => f (fst p)) (list_prod l l').
Proof.
  induction l; cbn [filter list_prod]; trivial.
  rewrite filter_app, filter_map_swap; cbn [fst].
  case f; rewrite ?filter_true, ?filter_false; cbn [list_prod map];
  rewrite ?IHl; auto.
Qed.
Lemma list_prod_filter_r [A B] (f : B -> _) (l : list A) l' :
  list_prod l (filter f l') = filter (fun p => f (snd p)) (list_prod l l').
Proof.
  induction l; cbn [filter list_prod]; trivial.
  rewrite filter_app, filter_map_swap; cbn [snd].
  rewrite ?IHl; f_equal.
Qed.
Lemma list_prod_filter_filter [A B] f g (l : list A) (l' : list B) :
  list_prod (filter f l) (filter g l') = filter (fun '(x, y) => f x && g y) (list_prod l l').
Proof.
  rewrite list_prod_filter_l, list_prod_filter_r, ?filter_filter.
  apply filter_ext; intros []; trivial.
Qed.
Lemma Permutation_filter [A] f (l l' : list A) :
  Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  induction 1; cbn [filter]; repeat (case f; [|]);
    eauto using perm_trans, perm_swap.
Qed.
Module Z.
  Local Open Scope Z_scope.
  Lemma mod2_square a : a^2 mod 2 = a mod 2.
  Proof. Z.div_mod_to_equations. nia. Qed.
  Lemma divide_pow_same_r a b : 0 < b -> (a | a^b).
  Proof.
    exists (a^(b-1)).
    rewrite <-(Z.pow_1_r a) at 3; rewrite <-Z.pow_add_r; f_equal; lia.
  Qed.
  Lemma divide_pow_pow_same a b c : 0 <= b <= c -> (a^b | a^c).
  Proof. exists (a^(c-b)). rewrite <-Z.pow_add_r by lia. f_equal; lia. Qed.
  Import Znumtheory.
  Lemma mod_prod_mod_factor_l x a b : x mod (a*b) mod a = x mod a.
  Proof. apply mod_mod_divide; exists b; ring. Qed.
  Lemma mod_prod_mod_factor_r x a b : x mod (a*b) mod b = x mod b.
  Proof. apply mod_mod_divide; exists a; ring. Qed.
  Lemma gcd_mod_l x m : Z.gcd (x mod m) m = Z.gcd x m.
  Proof.
    case (Z.eq_dec m 0) as [->|].
    { rewrite ?Z.gcd_0_r, ?Zmod_0_r; trivial. }
    rewrite Z.gcd_mod, Z.gcd_comm; trivial.
  Qed.
  Lemma gcd_mod_r x m : Z.gcd m (x mod m) = Z.gcd m x.
  Proof. rewrite Z.gcd_comm, Z.gcd_mod_l, Z.gcd_comm; trivial. Qed.

  Lemma odd_square_mod_pow2_1mod8 n a 
    (Hnn : 0 < n) (H : 0 <= a < 2 ^ n) (Hodd : a mod 2 = 1)
    (Hr :exists r, r ^ 2 mod 2 ^ n = a mod 2 ^ n) : a mod 8 = 1.
  Proof.
    case Hr as [r Hr].
    rewrite <-(Z.mod_small a (2^n)) by trivial.
    case (Z.eqb_spec n 1) as [->|].
    { rewrite Z.mod_small; zify; Z.to_euclidean_division_equations; lia. }
    case (Z.eqb_spec n 2) as [->|].
    { rewrite <-Z.mod_pow_l in Hr; set (r mod 2 ^ 2) as r' in *.
      assert (r' = 0 \/ r' = 1 \/ r' = 2 \/ r' = 3);
        zify; Z.to_euclidean_division_equations; lia. }
    rewrite mod_mod_divide by (apply (Z.divide_pow_pow_same 2 3); lia).
    apply (f_equal (fun x => x mod 8)) in Hr.
    rewrite 2mod_mod_divide, <-Z.mod_pow_l in Hr by (apply (Z.divide_pow_pow_same 2 3); lia).
    set (r mod 8) as r' in *.
    assert (r' = 0 \/ r' = 1 \/ r' = 2 \/ r' = 3 \/ r' = 4 \/ r' = 5 \/ r' = 6 \/ r' = 7)
      by (zify; Z.to_euclidean_division_equations; lia).
    clearbody r'; intuition subst r'; cbn in *; (zify; Z.to_euclidean_division_equations; lia).
  Qed.
End Z.

Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Local Coercion N.pos : positive >-> N.
Local Coercion Z.of_N : N >-> Z.
Local Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
Local Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Module Export CRT.
Import Znumtheory.

Module Zmod.
Import Znumtheory ZmodDef.Zmod Base.Zmod.
Lemma elements_mul_coprime (a b : positive) (H : Z.gcd a b = 1) :
  Permutation (elements (a * b))
    (map (fun xy : Zmod _ * Zmod _ => Zmod.of_Z (a*b) (combinecong a b (fst xy) (snd xy)))
      (list_prod (elements a) (elements b))).
Proof.
  eapply NoDup_Permutation_bis; try apply NoDup_elements; rewrite ?length_map, ?length_prod, ?length_elements; try lia.
  intros xy G; rewrite in_map_iff; exists (of_Z _ xy, of_Z _ xy); cbn [fst snd].
  split; auto using in_prod, in_elements; [].
  apply to_Z_inj; rewrite !to_Z_of_Z, combinecong_mod_l, combinecong_mod_r.
  symmetry; rewrite <-2mod_to_Z at 1; f_equal; rewrite Pos2Z.inj_mul.
  apply combinecong_complete_coprime_nonneg_nonneg; lia.
Qed.
End Zmod.

Module Zstar.
Import Znumtheory ZmodDef.Zstar Base.Zstar.

Lemma elements_mul_coprime (a b : positive) (H : Z.gcd a b = 1) :
  Permutation (elements (a * b))
    (map (fun xy : Zstar _ * Zstar _ => of_Zmod (Zmod.of_Z (a*b) (combinecong a b (fst xy) (snd xy))))
      (list_prod (elements a) (elements b))).
Proof.
  pose proof Zmod.elements_mul_coprime a b H as P.
  eapply (Permutation_filter (fun x : Zmod (a*b) => Z.gcd x (a*b) =? 1)) in P.
  eapply (Permutation_map (@of_Zmod (a*b))) in P.
  rewrite <-Pos2Z.inj_mul in P; rewrite P; clear P.
  symmetry; rewrite <-map_map with (g:=of_Zmod), filter_map_swap; Morphisms.f_equiv.
  erewrite <-map_ext, <-map_map with (f := fun xy : Zstar _ * Zstar _ => (fst xy : Zmod _, snd xy : Zmod _)); Morphisms.f_equiv; cbv beta.
  2: { intros []; trivial. }
  cbv [elements]; erewrite list_prod_map_map, map_map, list_prod_filter_filter;
  erewrite map_ext_in, map_id, filter_ext; trivial; intros [x y]; cbn [fst snd].
  { case (combinecong_sound_coprime a b x y ltac:(trivial)) as [Hx Hy].
    apply eq_true_iff_eq; rewrite andb_true_iff, !Z.eqb_eq.
    rewrite Zmod.to_Z_of_Z, Pos2Z.inj_mul, Z.coprime_mul_r.
    do 2 (symmetry; rewrite <-(Z.gcd_mod_l _ a), <-(Z.gcd_mod_l _ b)).
    rewrite Z.mod_prod_mod_factor_l, Z.mod_prod_mod_factor_r, Hx, Hy; lia. }
  { intros [?[?%Z.eqb_eq ?%Z.eqb_eq]%andb_true_iff]%filter_In.
    rewrite !to_Zmod_of_Zmod; trivial. }
Qed.

Lemma length_elements_mul_coprime (a b : positive) (H : Z.gcd a b = 1) :
  length (elements (a*b)) = (length (elements a) * length (elements b))%nat.
Proof. erewrite elements_mul_coprime, ?length_map, ?length_prod; lia. Qed.

Lemma length_elements_semiprime (p q : positive)
  (Hp : prime p) (Hq : prime q) (H : p <> q) :
  length (elements (p*q)) = Z.to_nat ((p-1)*(q-1)).
Proof.
  rewrite length_elements_mul_coprime, 2length_elements_prime;
    try apply Z.coprime_prime_prime; trivial; nia.
Qed.
End Zstar.
End CRT.

Module Zstar.
Import Znumtheory ZmodDef.Zstar Base.Zstar Zstar.

Lemma square_roots_opp_prime {p : positive} (Hp : prime p) (x y : Zstar p) :
  pow x 2 = pow y 2 <-> (x = y \/ x = opp y).
Proof.
  rewrite <-3to_Zmod_inj_iff, 2to_Zmod_pow, to_Zmod_opp.
  rewrite (Zmod.square_roots_opp_prime Hp); reflexivity.
Qed.

Lemma square_roots_1_prime (p : positive) (Hp : prime p) (x : Zstar p) :
  pow x 2 = one <-> (x = one \/ x = opp one).
Proof.
  rewrite <-3to_Zmod_inj_iff, to_Zmod_pow, to_Zmod_opp, to_Zmod_1.
  rewrite (Zmod.square_roots_1_prime Hp); reflexivity.
Qed.

Local Notation "∏ xs" := (List.fold_right mul one xs) (at level 40).

Local Infix "*" := mul.
Local Infix "/" := div.

(* TODO: move? Local? *)
Definition of_bool (m : positive) (b : bool) : Zstar m := if b then one else opp one.
Lemma of_bool_negb m b : of_bool m (negb b) = opp (of_bool m b).
Proof. case b; cbn [of_bool negb]; rewrite ?opp_opp; trivial. Qed.
Lemma of_bool_1_iff m b : of_bool m b = one <-> b = true \/ m <= 2.
Proof.
  pose proof @opp_1_neq_1 m.
  pose proof @wlog_eq_Zstar_3 m one (opp one).
  case (Z.leb_spec 3 m); case b; cbn [of_bool]; intuition (congruence || lia).
Qed.
Lemma of_bool_m1_iff m b : of_bool m b = (opp one) <-> b = false \/ m <= 2.
Proof.
  pose proof @opp_1_neq_1 m.
  pose proof @wlog_eq_Zstar_3 m one (opp one).
  case (Z.leb_spec 3 m); case b; cbn [of_bool]; intuition (congruence || lia).
Qed.
Lemma of_bool_1_iff_ge3 m b (Hm : Pos.le 3 m) : of_bool m b = one <-> b = true.
Proof. rewrite of_bool_1_iff; intuition (congruence || lia). Qed.
Lemma of_bool_m1_iff_ge3 m b (Hm : Pos.le 3 m) : of_bool m b = opp one <-> b = false.
Proof. rewrite of_bool_m1_iff; intuition (congruence || lia). Qed.

Lemma abs_of_bool m b : abs (of_bool m b) = one.
Proof. cbv [of_bool]; case b; rewrite ?abs_opp, ?abs_1; trivial. Qed.
Lemma inv_of_bool m b : inv (of_bool m b) = of_bool m b.
Proof. cbv [of_bool]; case b; rewrite ?inv_opp, ?inv_1; trivial. Qed.

Lemma to_Z_true {m : positive} (H : 2 <= m) : Zmod.to_Z (of_bool m true) = 1.
Proof. cbv [of_bool]. rewrite to_Zmod_1, Zmod.to_Z_1; trivial. Qed.

Lemma to_Z_false {m : positive} : Zmod.to_Z (of_bool m false) = m-1.
Proof.
  case (Pos.eq_dec m 1) as [->|]; trivial.
  case (Pos.eq_dec m 2) as [->|]; trivial.
  cbv [of_bool].
  rewrite to_Zmod_opp, Zmod.to_Z_opp, to_Zmod_1, Zmod.to_Z_1, (Z.mod_diveq (-1)); try lia.
Qed.

Lemma signed_true {m : positive} (H : 3 <= m) : Zmod.signed (of_bool m true) = 1.
Proof. cbv [of_bool]. rewrite to_Zmod_1, Zmod.signed_1; trivial. Qed.

Lemma signed_false {m : positive} (H : 2 <= m) : Zmod.signed (of_bool m false) = -1.
Proof.
  case (Pos.eq_dec m 2) as [->|]; trivial. cbv [of_bool].
  rewrite to_Zmod_opp, Zmod.signed_opp, to_Zmod_1, Zmod.signed_1 by lia.
  rewrite Z.smod_small; trivial. zify; Z.to_euclidean_division_equations; nia.
Qed.

Local Lemma euler_criterion_subproof  {p : positive} (Hp : prime p) (a : Zstar p) :
  ∏ elements p =
  of_bool _ (negb (existsb (fun x => eqb (pow x 2) a) (elements p))) * pow a ((p-1)/2).
Proof.
  apply wlog_eq_Zstar_3; intro Hp'.

  (* Tripartite categorization *)
  rewrite existsb_as_filter, negb_involutive.
  set (roots := filter (fun x : ZmodDef.Zstar p => eqb (pow x 2) a) (elements p)).
  set (smalls := filter (fun x : ZmodDef.Zstar p => x <? div a x) (elements p)).
  set (larges := filter (fun x : ZmodDef.Zstar p => div a x <? x) (elements p)).
  assert (HP : Permutation (elements p) (roots ++ (smalls ++ larges))). {
   erewrite (Permutation_partition (fun x : Zstar _ => pow x 2 =? a)).
   erewrite (Permutation_partition (fun x : Zstar _ => x <? div a x) (snd _)).
   rewrite !partition_as_filter; cbn [fst snd]; rewrite !filter_filter.
   assert (Hiff : forall x, x*x = a :> Z <-> a/x = x :> Z).
   { intros x; rewrite !Zmod.to_Z_inj_iff, !to_Zmod_inj_iff.
     erewrite <-(mul_cancel_l_iff x _ x), mul_div_r_same_r. split; congruence. }
   erewrite (filter_ext (fun _ => _ && _) (fun x : Zstar _ => x <? div a x)); cycle 1.
   { intros x; eapply andb_implied_r; rewrite pow_2_r, negb_true_iff, Z.eqb_neq, Hiff; lia. }
   erewrite (filter_ext (fun _ => _ && _) (fun x => div a x <? x)); cycle 1.
   { intros x; apply eq_true_iff_eq. rewrite pow_2_r, !andb_true_iff, !negb_true_iff, Z.eqb_neq, Hiff; lia. }
   trivial. }

  pose proof @NoDup_elements p. (* TODO @ *)
  assert (NoDup roots) as NDroots by eauto using NoDup_filter.
  assert (NoDup smalls) by eauto using NoDup_filter.
  assert (NoDup larges) by eauto using NoDup_filter.

  (* Pairing inverses *)
  assert (HPP : Permutation larges (map (fun x : Zstar p => div a x) smalls));
    [|rewrite HPP in HP; clear HPP].
  { apply Permutation.NoDup_Permutation; intros; trivial.
    { eapply FinFun.Injective_map_NoDup; trivial.
      (* TODO: div_inj, inv_inj *)
      intros ? ? E.
      rewrite <-2mul_inv_r in E.
      eapply mul_cancel_l, (f_equal inv) in E.
      rewrite 2 Zstar.inv_inv in E.
      trivial. }
    cbv [smalls larges].
    rewrite in_map_iff; repeat setoid_rewrite filter_In.
    repeat setoid_rewrite N.ltb_lt.
    assert (Hdiv : forall x y z : Zstar p, div z y = x <-> z = mul x y); [|setoid_rewrite Hdiv].
    { split; intros; subst.
      { rewrite <-mul_inv_r, <-!mul_assoc, mul_inv_same_l, mul_1_r; auto. }
      { rewrite div_mul_l, div_same, mul_1_r; trivial. } }
    split.
    { intros []. exists (div a x). rewrite mul_div_r_same_r, div_div_r_same. intuition apply in_elements. }
    { intros (y&A&?&?). rewrite A in *. rewrite mul_comm.
      rewrite div_mul_l, div_same, mul_1_r in *. intuition apply in_elements. } }
  erewrite prod_Permutation, prod_app by eapply HP.
  erewrite (prod_Permutation _ (smalls++_) (flat_map (fun x => [x;a/x]) smalls)); cycle 1.
  { generalize (div a) as f; generalize smalls as xs; generalize (Zstar p) as A; clear.
    induction xs; cbn [map flat_map app]; intros; econstructor.
    erewrite <-Permutation_middle; eauto. }
  erewrite prod_flat_map, map_ext, map_const, (prod_repeat a); cycle 1.
  { intros x. cbn [fold_right]. rewrite mul_1_r, mul_div_r_same_r; trivial. }

  (* Counting elements *)
  assert (length (elements p) = length roots + 2*length smalls)%nat as HL.
  { erewrite Permutation.Permutation_length, !length_app, !length_map by eauto; lia. }
  assert (Z.of_nat (length smalls) = (p-1-Z.of_nat (length roots))/2)%Z as ->.
  { pose proof Zstar.length_elements_prime p Hp.
    zify; Z.to_euclidean_division_equations; lia. }

  (* Casework on [length roots] using [NoDup roots] *)
  destruct roots as [|x roots'] eqn:A. (* no roots *)
  { cbn [fold_right length Nat.eqb of_bool]; rewrite ?mul_1_l, Z.sub_0_r; trivial. }
  assert (Hx: In x roots). { rewrite A. left. split. } apply filter_In, proj2 in Hx.
  destruct roots' as [|y roots''] eqn:B. (* 1 *)
  { unshelve ecase (opp_distinct_odd _ _ x); try lia; auto using odd_prime.
    assert (In (opp x) roots) as AA.
    { apply filter_In, conj; try apply in_elements. rewrite pow_opp_2; trivial. }
    rewrite A in AA; inversion AA as [|AAA]; trivial; inversion AAA. }
  (* 2 <= *)
  assert (Hy: In y roots). { rewrite A. right. left. split. } apply filter_In, proj2 in Hy.
  rewrite eqb_eq in *.
  assert (y = opp x) as ->.
  { case (proj1 (square_roots_opp_prime Hp y x)); trivial.
    { congruence. }
    { intros ->. inversion_clear NDroots as [|? ? X]; case X; left; trivial. } }
  destruct roots'' as [|z roots''']; cycle 1. (* 3 <= *)
  { assert (Hz: In z roots). { rewrite A. right. right. left. split. } apply filter_In, proj2 in Hz.
    rewrite ?eqb_eq in *.
    { case (proj1 (square_roots_opp_prime Hp z x)) as [->| ->].
      { congruence. }
      { inversion_clear NDroots as [|? ? X]; case X; right; left; split. }
      { inversion_clear NDroots as [|? ? ? X].
        inversion_clear X as [|? ? Y]; case Y; left; split. } } }
  (* 2 roots *)
  cbn [fold_right length Nat.eqb of_bool];
  repeat rewrite ?mul_1_r, ?mul_1_l, ?mul_opp_l, ?mul_opp_r.
  rewrite <-pow_2_r, Hx, <-pow_succ_r. f_equal. f_equal.
  zify; Z.to_euclidean_division_equations; lia.
Qed.

(** One direction of Wilson's theorem *)
Theorem prod_elements_prime {p : positive} (Hp : prime p) : ∏ elements p = opp one.
Proof.
  rewrite (euler_criterion_subproof Hp one).
  rewrite (proj2 (existsb_exists _ _)), pow_1_l, mul_1_r; cbn [of_bool negb]; trivial.
  exists one; rewrite ?pow_1_l, ?eqb_eq ; auto using in_elements.
Qed.

Lemma euler_criterion_existsb {p : positive} a (Hp : prime p) :
  pow a ((p-1)/2) = of_bool p (existsb (fun x => eqb (pow x 2) a) (elements p)).
Proof.
  pose proof euler_criterion_subproof Hp a as H.
  rewrite prod_elements_prime in H by trivial.
  apply (f_equal opp) in H; rewrite ?of_bool_negb, ?mul_opp_l, ?opp_opp in H.
  case existsb in *; cbn [of_bool] in *;
    rewrite H, ?mul_opp_l, ?opp_opp, ?mul_1_l; trivial.
Qed.

Theorem euler_criterion {p : positive} (a : Zstar p) (Hp : prime p):
  pow a ((p-1)/2) = one <-> exists x, pow x 2 = a.
Proof.
  split.
  { case (Pos.leb_spec 3 p) as []; cycle 1.
    { exists one. apply wlog_eq_Zstar_3. lia. }
    rewrite euler_criterion_existsb, of_bool_1_iff, existsb_exists by trivial.
    intros [[x [_ Hx%eqb_eq]]|]; try lia; eauto. }
  { intros [x Hx]; eapply euler_criterion_square; eauto. }
Qed.

Lemma euler_criterion_nonsquare {p : positive} (Hp : prime p)
  (a : Zstar p) (Ha : forall x, pow x 2 <> a) : pow a ((p-1)/2) = opp one.
Proof.
  rewrite euler_criterion_existsb by trivial.
  case existsb eqn:H; trivial; exfalso.
  apply existsb_exists in H; case H as [x [_ H%eqb_eq]].
  case (Ha x); trivial.
Qed.

Lemma euler_criterion_neq_one {p : positive} (Hp : prime p)
  (a : Zstar p) (H : pow a ((p-1)/2) <> one) : forall x, pow x 2 <> a.
Proof.
  rewrite euler_criterion in H by trivial; intros x Hx; case H; eauto.
Qed.

Lemma euler_criterion_m1 {p : positive} (Hp : prime p) (Hp' : 3 <= p)
  (a : Zstar p) (H : pow a ((p-1)/2) = opp one) : forall x, pow x 2 <> a.
Proof.
  apply euler_criterion_neq_one; trivial; rewrite H; apply opp_1_neq_1; trivial.
Qed.
End Zstar.

Module Zmod.
Import Znumtheory ZmodDef.Zmod Base.Zmod Zmod.
Local Infix "*" := mul.
Local Infix "^" := pow.

Theorem euler_criterion_square_nz {p : positive} (Hp : prime p)
  (a sqrt_a : Zmod p) (Ha : pow sqrt_a 2 = a) (Hnz : a <> zero) :
  pow a ((p-1)/2) = one.
Proof.
  assert (sqrt_a <> zero). { intros ->; rewrite pow_0_l in *; congruence. }
  rewrite <-to_Z_0_iff in *; pose proof to_Z_range a; pose proof to_Z_range sqrt_a.
  assert (Z.gcd a p = 1) by (apply Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia).
  assert (Z.gcd sqrt_a p = 1) by (apply Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia).
  unshelve epose proof
    (E := Zstar.euler_criterion_square Hp (Zstar.of_Zmod a) (Zstar.of_Zmod sqrt_a) _).
  { apply Zstar.to_Zmod_inj; rewrite Zstar.to_Zmod_pow, 2Zstar.to_Zmod_of_Zmod; trivial. }
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in E; trivial.
Qed.

Theorem euler_criterion_square {p : positive} (Hp : prime p)
  (a sqrt_a : Zmod p) (Ha : pow sqrt_a 2 = a) :
  a = zero \/ pow a ((p-1)/2) = one.
Proof.
  pose proof euler_criterion_square_nz Hp _ _ Ha.
  case (eqb_spec a zero); intuition idtac.
Qed.

Theorem euler_criterion {p : positive} a (Hp : prime p) :
  (a = zero \/ a ^ ((p - 1) / 2) = one) <-> exists x : Zmod p, pow x 2 = a.
Proof.
  split; cycle 1.
  { intros []; eauto using euler_criterion_square. }
  intros [].
  { subst. exists zero. trivial. }
  pose proof (prime_ge_2 _ Hp) as Hp'; pose proof one_neq_zero Hp'.
  case (Pos.eq_dec p 2) as [->|]. {
    (pose proof in_elements a as C; rewrite elements_2 in C;
      cbv [In] in *; intuition subst); [exists zero|exists one]; trivial. }
  assert (((p - 1) / 2) <> 0)%Z by (zify; Z.div_mod_to_equations; nia).
  assert (a <> zero). { intros ->; rewrite pow_0_l in *. congruence. lia. }
  rewrite <-to_Z_0_iff in H2; pose proof to_Z_range a.
  assert (Z.gcd a p = 1). { apply Zgcd_1_rel_prime, rel_prime_le_prime; trivial; lia. }
  case (proj1 (@Zstar.euler_criterion p (Zstar.of_Zmod a) Hp)) as [x Hx].
  { apply Zstar.to_Zmod_inj.
    rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1; trivial. }
  { exists x. apply (f_equal Zstar.to_Zmod) in Hx.
    rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod in Hx; trivial. }
Qed.

Import ZmodSqrtDef.Zmod.
Section WithAB.
Local Infix "^" := pow.
Context {m} (phi_m : positive) (a b : Zmod m).
Local Notation chase_sqrt := (@Zmod.chase_sqrt m phi_m a b).
Context (b_spec : b ^ N.div2 phi_m = opp one).
Context (sqrts_1 : forall x : Zmod m, x ^ 2 = one -> x = one \/ x = opp one).
Local Lemma Private_chase_sqrt_correct (apow : positive) (bpow : N) :
  mul (pow a apow) (pow b bpow) = one /\
  (forall k:N, (2^k | apow) -> (2*2^k | bpow)) /\
  (forall k:N, (2^k | apow) -> (2^k | N.div2 phi_m)) ->
  chase_sqrt apow bpow ^ 2 = a.
Proof.
  revert bpow; induction apow; cbn [chase_sqrt]; intros ?; cycle -1.
  { intros (A&B&P).
    rewrite pow_1_r in *.
    rewrite pow_mul_l_nonneg, <-Zmod.pow_mul_r_nonneg, pow_2_r, <-mul_assoc
      by (try apply N2Z.is_nonneg; lia).
    assert (Z.mul (N.div2 bpow) 2 = bpow) as ->. {
      case (B 0%N) as [].
      { exists (xH); cbn. lia. }
      zify; Z.div_mod_to_equations; nia. }
    rewrite A, mul_1_r; trivial. }
  { rewrite pow_mul_l_nonneg, <-2Zmod.pow_mul_r_nonneg
      by (try apply N2Z.is_nonneg; lia).
    assert (Z.mul (Pos.succ apow) 2 = N.succ (xI apow)) as -> by lia; intros (A&B&P).
    assert (Z.mul (N.div2 bpow) 2 = bpow) as ->. {
      case (B 0%N) as [].
      { exists (xI apow); cbn. lia. }
      zify; Z.div_mod_to_equations; nia. }
    rewrite N2Z.inj_succ, pow_succ_r_nonneg, <-mul_assoc, N2Z.inj_pos, A, mul_1_r; trivial; lia. }
  { case (eqb_spec (a^apow * b^N.div2 bpow) one) as [E|E];
      intros (A&B&P); apply IHapow; clear IHapow.
    { split; trivial. split.
      { intros k [d D].
        case (B (N.succ k)) as [x H].
        { exists d. rewrite N2Z.inj_succ, Z.pow_succ_r; lia. }
        exists x.
        rewrite N2Z.inj_succ, Z.pow_succ_r in * by lia.
        zify; Z.div_mod_to_equations; nia. }
      { intros k [x Hx]. apply P. exists (Z.double x). lia. } }
    { split.
      { rewrite N2Z.inj_add, Zmod.pow_add_r_nonneg, mul_assoc, b_spec by apply N2Z.is_nonneg.
        case (sqrts_1 (mul (a^apow) (b^N.div2 bpow))) as [| ->]; try contradiction.
        { rewrite Zmod.pow_mul_l_nonneg, <-2Zmod.pow_mul_r_nonneg, Z.mul_comm
            by (try apply N2Z.is_nonneg; lia).
          assert (Z.mul (N.div2 bpow) 2 = bpow) as ->. {
            case (B 0%N) as [].
            { exists (xO apow); cbn. lia. }
            zify; Z.div_mod_to_equations; nia. }
          apply A. }
        rewrite mul_opp_opp, mul_1_l; trivial. }
      split.
      { intros k [d D].
        case (B (N.succ k)) as [x Bx].
        { exists d. rewrite N2Z.inj_succ, Z.pow_succ_r; lia. }
        case (P (N.succ k)) as [y Py].
        { exists d. rewrite N2Z.inj_succ, Z.pow_succ_r; lia. }
        rewrite N2Z.inj_add; apply Z.divide_add_r.
        { exists x.
          rewrite N2Z.inj_succ, Z.pow_succ_r in * by lia.
          zify; Z.div_mod_to_equations; nia. }
        exists y.
        rewrite Py, N2Z.inj_succ, Z.pow_succ_r; lia. }
      { intros k [x Hx]. apply P. exists (Z.double x). lia. } } }
Qed.
End WithAB.

Local Lemma Private_chase_sqrt_0 : forall m phi_m b apow bpow,
  @Zmod.chase_sqrt m phi_m zero b apow bpow = zero.
Proof.
  induction apow; cbn [Zmod.chase_sqrt]; intros;
    rewrite ?pow_0_l, ?mul_0_l by lia; trivial.
  case eqb; trivial.
Qed.

Lemma sqrtp'_correct (p : positive) (Hp : prime p)
  b (Hb : b^N.div2 (Pos.pred p) = opp one) :
  forall a, (exists x, x ^ 2 = a) -> @sqrtp' p a b ^ 2 = a.
Proof.
  cbv [sqrtp']; intros a.
  intros [x H]. apply wlog_eq_Zmod_2; intros Hp'.
  case (Pos.eq_dec p 2) as [->|]. {
    pose proof in_elements x as C; rewrite elements_2 in C;
      cbv [In] in *; intuition subst; cbn; rewrite ?mul_0_l, ?mul_1_l; auto. }
  case (euler_criterion_square Hp _ _ H) as [->|E].
  { rewrite Private_chase_sqrt_0; trivial. }
  apply Private_chase_sqrt_correct; trivial.
  { intros. apply Zmod.square_roots_1_prime; trivial. }
  rewrite Zmod.pow_0_r, Zmod.mul_1_r. split; [|split].
  { rewrite <-E; f_equal.
    rewrite Pos2Z.inj_div2; zify; Z.to_euclidean_division_equations; nia. }
  { intros. apply Z.divide_0_r. }
  { case (Pos.eq_dec (Pos.pred p) 1) as [->|]; [intros; apply Z.divide_0_r|].
    rewrite N2Z.inj_div2, Pos2Z.inj_div2; trivial. }
Qed.

Lemma nonsquare_correct {p : positive} (Hp : prime p) (Hp' : 3 <= p) :
  nonsquare p ^ ((p-1)/2) = opp one.
Proof.
  cbv [nonsquare].
  case ZmodSqrtDef.Zmod.find eqn:H.
  { apply find_some in H; rewrite eqb_eq in H; intuition idtac. }
  exfalso.
  pose proof find_none _ _ H as H'; cbv beta in *; clear H; rename H' into H.
  specialize (fun x : Zstar p => (H x (in_elements x))).
  setoid_rewrite <-not_true_iff_false in H; setoid_rewrite eqb_eq in H.
  setoid_rewrite <-Zstar.to_Zmod_pow in H.
  setoid_rewrite <-Zstar.to_Zmod_1 in H.
  setoid_rewrite <-Zstar.to_Zmod_opp in H.
  setoid_rewrite Zstar.to_Zmod_inj_iff in H.
  unshelve epose proof @NoDup_incl_length _ _ (map (fun x : Zstar p => Zstar.pow x 2) (Zstar.positives p)) (Zstar.NoDup_elements _) _ as X; cbv [incl] in *.
  { intros a _; specialize (H a).
    rewrite Zstar.euler_criterion_existsb, Zstar.of_bool_m1_iff_ge3 in H by trivial.
    rewrite not_false_iff_true, existsb_exists in H; case H as [x [_ H%Zstar.eqb_eq]].
    apply in_map_iff; exists (Zstar.abs x); auto using Zstar.in_elements.
    rewrite Zstar.pow_abs_2; split; trivial.
    rewrite Zstar.in_positives, Zstar.to_Zmod_abs, signed_abs_odd by (apply odd_prime; trivial).
    rewrite Z.abs_pos, signed_0_iff. apply Zstar.to_Zmod_nz; lia. }
  rewrite length_map in X.
  rewrite Zstar.length_elements_prime in X by trivial.
  rewrite Zstar.length_positives_prime in X by trivial.
  zify; Z.div_mod_to_equations; nia.
Qed.

Lemma sqrtp_square (p : positive) (Hp : prime p) a :
  (exists x, x ^ 2 = a) -> @sqrtp p a ^ 2 = a.
Proof.
  intros.
  apply wlog_eq_Zmod_2; intros Hp'.
  case (Pos.eq_dec p 2) as [->|].
  { pose proof in_elements a as C; rewrite elements_2 in C.
    case C as [|[|[]]]; subst; trivial. }
  cbv [sqrtp].
  rewrite sqrtp'_correct, eqb_refl, pow_abs_2, sqrtp'_correct; trivial;
    rewrite <-nonsquare_correct by (trivial; lia); f_equal;
    zify; Z.to_euclidean_division_equations; nia.
Qed.

Lemma abs_sqrtp p (a : Zmod p) : abs (sqrtp a) = sqrtp a.
Proof. cbv [sqrtp]; case eqb; rewrite ?abs_abs, ?abs_0; trivial. Qed.

Lemma sqrtp_nonsq (p : positive) (Hp : prime p) a :
  (forall x, x ^ 2 <> a) -> @sqrtp p a = zero.
Proof.
  pose proof sqrtp_square p Hp a.
  cbv [sqrtp] in *; intros X; case eqb eqn:E; trivial.
  rewrite eqb_eq, pow_abs_2 in *.
  case (fun x => (X (sqrtp' a (nonsquare p))) (H x)); eauto.
Qed.

Import Znumtheory.
Lemma lift_sqrt (q : Z) a x y
  (Hq : 3 <= q)
  (Hp : q mod 2 = 1)
  (Hx : Z.gcd x q = 1)
  (Ha : x^2 mod q = a mod q)
  (Hy : y = x + (x^2 - a)/q*invmod (-2*x) q mod q*q) :
  y^2 mod (q^2) = a mod (q^2).
Proof.
  intros.
  case (Z.eq_dec q 1) as [->|]; rewrite ?Z.mod_1_r; trivial.
  eapply cong_iff_0, Z.div_exact, Z.sub_move_r in Ha; try lia.
  set (((x^2 - a) / q)) as c in *.
  subst y.
  rewrite cong_iff_0.
  rewrite <-Z.add_opp_l.
  eassert (-_+_^2=_) as ->. { ring_simplify; ring. }
  rewrite Z_mod_plus_full, Ha.
  eassert (_+_=(c + 2*x * ((c * invmod (-2*x) q) mod q)) * q) as -> by ring.
  rewrite Z.pow_2_r, Zmult_mod_distr_r.
  rewrite <-Z.add_mod_idemp_r, Z.mul_mod_idemp_r by lia.
  assert ((2 * x * (c * invmod (-2 * x) q)) = -c * (invmod (-2*x) q * (-2*x))) as -> by ring.
  rewrite <-Z.mul_mod_idemp_r by lia.
  rewrite invmod_coprime; [|lia|..]; cycle 1.
  { apply Z.coprime_mul_l; trivial. change (-2) with (Z.opp 2); rewrite Z.gcd_opp_l.
    rewrite <-Z.gcd_mod, Hp; intuition lia. }
  rewrite Z.add_mod_idemp_r, Z.mul_1_r, Z.add_opp_r, Z.sub_diag, Z.mul_0_l; lia.
Qed.

Import Znumtheory.
Lemma lift_sqrt_2 n (q := 2^n) a x
  (Hk : 3 <= n)
  (Hx : Z.odd x = true)
  (Ha : x^2 mod q = a mod q)
  (k := (x ^ 2 - a) / 2 ^ n)
  (y := x + 2^(n-1)*k) :
  y^2 mod 2^(n+1) = a mod 2^(n+1).
Proof.
  intros.
  subst q.
  eapply cong_iff_0, Z.div_exact, Z.sub_move_r in Ha; try lia.
  fold k in Ha.
  rewrite cong_iff_0.
  rewrite <-Z.add_opp_l.
  subst y.
  eapply Zmod_divides. lia. eexists.
  etransitivity. ring_simplify. trivial.
  rewrite Ha.
  etransitivity. ring_simplify. trivial.
  rewrite <-Z.pow_mul_r, (ltac:(lia):(n - 1) * 2=(n+1)+(n-3)), Z.pow_add_r by lia.
  transitivity ((2*2^(n-1)*x+2^n*1)* k + 2^(n+1)*(2^(n-3)*k^2)); [ring|].
  rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred by lia.
  transitivity (2^n*(x+1)*k + 2^(n+1)*(2^(n-3)*k^2)); [ring|].
  rewrite (Z.div2_odd x) at 1.
  rewrite Hx; cbn [Z.b2z].
  assert ((2 * Z.div2 x + 1 + 1) = 2^1*(1+Z.div2 x)) as -> by lia.
  rewrite (Z.mul_assoc _ (2^1)), <-Z.pow_add_r by lia.
  instantiate (1:=(1 + Z.div2 x) * k + (2 ^ (n - 3) * k ^ 2)). ring.
Qed.

Local Lemma Private_sqrtp2''_correct n :
  forall a, a mod 8 = 1 ->
  (ZmodSqrtDef.sqrtp2'' n a)^2 mod 2^Z.of_nat n = a mod 2^Z.of_nat n.
Proof.
  induction n as [n IH] using lt_wf_ind. intros a Ha.
  do 4 try case n in *; rewrite ?Z.mod_1_r; trivial.
  1,2,3: simpl Z.of_nat; simpl ZmodSqrtDef.sqrtp2'';
    symmetry; rewrite <-mod_mod_divide with (b:=8), Ha; trivial;
    solve [exists 1; trivial | exists 2; trivial | exists 4; trivial].
  set (S (S (S n))) as n'; specialize (IH n' ltac:(lia) a Ha).
  cbn [ZmodSqrtDef.sqrtp2'']. cbn [n'].
  rewrite Z.land_comm, Z.land_ones, ?Z.mod_pow_l by lia.
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?Nat2Z.inj_succ, ?Z.pred_succ, <-?Z.add_1_r by lia.
  rewrite Z.mul_comm. eapply lift_sqrt_2; eauto; try lia.
  change 8 with (2^3) in *; apply (f_equal Z.odd) in Ha, IH;
    rewrite ?Zodd_mod, ?mod_mod_divide, ?Z.mod2_square in *;
    try apply Z.divide_pow_same_r; try lia. rewrite IH, Ha; trivial.
Qed.

Lemma sqrtp2'_correct n (Hnn : 0 <= n) a (Hodd : a mod 2 = 1)
  (Ha : exists x, x^2 mod 2^n = a mod 2^n) :
  (ZmodSqrtDef.sqrtp2' n a)^2 mod 2^n = a mod 2^n.
Proof.
  cbv [ZmodSqrtDef.sqrtp2'].
  rewrite !Z.land_ones by lia; change (2^3) with 8 in *; rename a into a'.
  case (Z.eqb_spec n 0) as [->|]. { rewrite ?Zmod_1_r; trivial. }
  pose proof Z.mod_pos_bound a' (2^n) ltac:(lia); set (a' mod 2^n) as a in *.
  rename Hodd into Hodd'; assert (Hodd : a mod 2 = 1).
  { subst a. rewrite Znumtheory.mod_mod_divide; trivial. apply Z.divide_pow_same_r; lia. }
  rename Ha into Ha'; assert (Ha : exists x, x^2 mod 2^n = a mod 2^n).
  { subst a. rewrite Z.mod_mod by lia; trivial. } clearbody a; clear Ha' Hodd' a'.
  case Z.eqb eqn:E; rewrite <-?not_true_iff_false, Z.eqb_eq in E; cycle 1.
  { case E; eapply Z.odd_square_mod_pow2_1mod8; eauto; lia. }
  unshelve epose proof Private_sqrtp2''_correct (Z.to_nat n) a E.
  rewrite Z2Nat.id, (Z.mod_small a) in * by lia; trivial.
Qed.

Section WithP.
  Context (p : positive).
  Local Notation sqrtpop' := (ZmodSqrtDef.sqrtpop' p).
  Local Notation sqrtpp' := (ZmodSqrtDef.sqrtpp' p).
  Local Notation sqrtpp := (sqrtpp p).

  Context (Hp : prime p).
  Local Lemma Private_sqrtpop'_correct (Hodd : 3 <= p) lgk :
    forall a (Ha : Z.gcd a p = 1) (Hsq : exists x : Zmod p, pow x 2 = a mod p :> Z)
    (q := Z.pow p (two_power_nat lgk)), sqrtpop' lgk a ^ 2 mod q = a mod q.
  Proof.
    pose proof odd_prime _ Hp Hodd as Hp'.
    induction lgk; cbn [sqrtpop']; intros.
    { rewrite ?two_power_nat_equiv, ?Z.pow_1_r.
      apply of_Z_inj. rewrite of_Z_pow by lia. rewrite of_Z_to_Z.
      rewrite sqrtp_square; trivial.
      case Hsq as [x Hsq]. exists x; apply to_Z_inj.
      rewrite Hsq, to_Z_of_Z; trivial. }
    rewrite ?two_power_nat_equiv, ?Nat2Z.inj_succ, ?Z.pow_succ_r, ?(Z.mul_comm 2), ?Z.pow_mul_r in * by lia.
    set (p ^ 2 ^ Z.of_nat lgk)%Z as q in *.
    rewrite <-mod_mod_divide with (b:=q) in Hsq.
    2: { subst q. rewrite <-(Z.succ_pred (2 ^ _)), Z.pow_succ_r by lia; apply Z.divide_factor_l. }
    unshelve epose proof (IHlgk (a mod q) _ Hsq) as IHlgk'.
    { rewrite <-Z.gcd_mod_l, mod_mod_divide, Z.gcd_mod_l; trivial. apply Z.divide_pow_same_r; lia. }
    eapply lift_sqrt; rewrite ?IHlgk', ?Zmod_mod; eauto.
    { subst q. transitivity (p^1); [|eapply Z.pow_le_mono_r]; try lia. }
    { subst q. rewrite <-Z.mod_pow_l, Hp', Z.pow_1_l; trivial; lia. }
    { rewrite <-Z.coprime_sqr_l, <-Z.gcd_mod_l, IHlgk', 2Z.gcd_mod_l; trivial.
      apply Z.coprime_pow_r; lia. }
  Qed.

  Local Lemma Private_sqrtpop'_0 lgk : sqrtpop' lgk 0 = 0.
  Proof.
    induction lgk; cbn [sqrtpop']; intros.
    { unshelve epose proof sqrtp_square p Hp zero _.
      { exists zero. rewrite pow_0_l; trivial; lia. }
      apply to_Z_0_iff; rewrite pow_2_r in H.
      apply Zmod.mul_0_iff_prime in H; intuition idtac. }
    rewrite ?two_power_nat_equiv, Z.mod_0_l, ?IHlgk,
      ?Z.add_0_l, ?Z.sub_0_r, ?Z.pow_0_l, ?Z.div_0_l, ?Z.mul_0_l; lia.
  Qed.

  Local Lemma Private_sqrtpp'_correct k (q := Pos.pow p k)
    a (Ha : Z.gcd a p = 1) (Hsq : exists x, x^2 mod q = a mod q :> Z) :
    sqrtpp' k a ^ 2 mod q = a mod q.
  Proof.
    cbv [q sqrtpp'] in *; rewrite ?Pos2Z.inj_pow in *.
    destruct (Pos.eqb_spec p 2) as [->|].
    { apply sqrtp2'_correct; trivial; try lia.
      (* gcd a 2 = 1 -> a mod 2 = 1 *)
      revert Ha. rewrite Z.gcd_comm, <-Z.gcd_mod by lia.
      assert (a mod 2 = 0 \/ a mod 2 = 1) as [-> | ->];
         cbn; (zify; Z.div_mod_to_equations; lia). }
    unshelve epose proof Private_sqrtpop'_correct _ (Z.to_nat (Z.log2_up k)) a _ _; trivial.
    { pose proof prime_ge_2 p Hp. lia. }
    { case Hsq as [r Hr]. exists (of_Z _ r).
      rewrite !to_Z_pow_nonneg, !to_Z_of_Z, Z.mod_pow_l by lia.
      apply (f_equal (fun x => x mod p)) in Hr.
      rewrite ?mod_mod_divide in Hr by (apply Z.divide_pow_same_r; lia); lia. }
    rewrite two_power_nat_equiv, Z2Nat.id in * by apply Z.log2_up_nonneg.
    remember (p ^ 2 ^ Z.log2_up k) as q'; cbv zeta in *.
    replace (2 ^ Z.log2_up k) with ((2^Z.log2_up k-k)+k) in * by lia;
      rewrite Z.pow_add_r in *; try lia; cycle 1.
    { enough (k <= 2^Z.log2_up k) by lia; eapply Z.log2_log2_up_spec; lia. }
    apply (f_equal (fun x => x mod p^k)) in H.
    rewrite !mod_mod_divide in H; trivial; try (eexists; eauto).
  Qed.

  Lemma sqrtpp_correct (k : positive) (q := Pos.pow p k) a
     (Hsq : exists x, x^2 mod q = a mod q) : sqrtpp k a ^ 2 mod q = a mod q.
  Proof.
    cbv [q sqrtpp] in *; rewrite ?Pos2Z.inj_pow in *.
    case Z.eqb eqn:E; rewrite <-?not_true_iff_false, Z.eqb_eq in E.
    { rewrite Z.pow_0_l, Z.mod_0_l; lia. }
    pose proof prime_ge_2 _ Hp.
    set (v := val _ _) in *.
    case (proj1 (val_iff v p _ ltac:(lia)) eq_refl) as [[x Hx] Hnx].
    pose proof Z.mod_pos_bound a (p^k) ltac:(lia).
    symmetry; rewrite <-(Zmod_mod a) at 1; symmetry.
    assert (a mod p ^ k = p^v * x) as -> by lia.
    rewrite <-N.negb_even. case N.even eqn:O;
      rewrite <-?not_true_iff_false, N.even_spec in O; cbv [negb]; cycle 1.
      { case (N.Even_or_Odd v) as [|[n Hn]]; [solve [intuition idtac]|clear O].
        case Hnx; clear Hnx.
        assert (N.succ v = 2*(n+1))%N as -> by nia.
        case Hsq as [r Hr].

        assert_succeeds (rename Hx into Hx'; assert (a mod p ^ k = x * p ^ v :> Z) as Hx by lia; clear Hx').

        subst v; rewrite <-Hr in *.


      admit. (* no sqrt -- contradict Hsq *) }
    case O as [].
    rewrite Z.mod_pow_l, Z.pow_mul_l, <-Z.pow_mul_r; try apply N2Z.is_nonneg; try lia.
    assert (N.div2 v * 2 = v) as -> by (zify; Z.div_mod_to_equations; nia).
    rewrite <-Zmult_mod_idemp_r at 1.
    symmetry; rewrite <-Zmult_mod_idemp_r; symmetry.
    f_equal; f_equal.
    rewrite (Z.mul_comm _ x), Z.div_mul by lia.
    pose proof Private_sqrtpp'_correct k x as R; rewrite ?Pos2Z.inj_pow in R; apply R; clear R.
    { apply Zgcd_1_rel_prime, rel_prime_sym, prime_rel_prime; trivial; intros [y ?].
      eapply (ndivide_val_div p (Z.to_pos (a mod p^k))); fold v.
      { pose proof prime_ge_2 p Hp; lia. }
      exists (Z.abs_N y). zify; Z.to_euclidean_division_equations; nia. }
    { (* sqrt exists after dividing out powers of p *) admit. }
  Admitted.
End WithP.
End Zmod.

Module Reciprosity. Module Zstar.
Import ZmodDef Znumtheory.
Import ZmodDef.Zmod Base.Zmod CRT.Zmod ZmodSqrt.Zmod.
Import ZmodDef.Zstar Base.Zstar CRT.Zstar ZmodSqrt.Zstar.
Local Notation "∏ xs" := (List.fold_right mul one xs) (at level 40).

Module Z.
Lemma pow_m1_l : forall n, 0 <= n -> Z.pow (-1) n = if Z.odd n then -1 else 1.
Proof.
  eapply Wf_Z.natlike_ind; trivial; intros.
  rewrite Z.pow_succ_r, Z.odd_succ, <-Z.negb_odd by trivial.
  case Z.odd in *; cbv [negb]; lia.
Qed.
End Z.

Local Lemma mul_signed_subgroups_abs (p q : positive) (Hp : p mod 2 = 1) (Hq : q mod 2 = 1) x y :
  abs x = abs y :> Zstar (p*q) -> Z.smodulo x p * Z.smodulo x q = Z.smodulo y p * Z.smodulo y q.
Proof.
  intros []%eq_abs_iff; [congruence|subst y].
  rewrite to_Zmod_opp, to_Z_opp.
  symmetry.
  rewrite <-Z.smod_mod, mod_mod_divide, Z.smod_mod by (exists q; lia).
  rewrite <-(Z.smod_mod _ q), mod_mod_divide, Z.smod_mod by (exists p; lia).
  rewrite <-(Z.smod_idemp_opp _ p), <-(Z.smod_idemp_opp _ q).
  pose proof Z.smod_pos_bound x p ltac:(lia).
  pose proof Z.smod_pos_bound x q ltac:(lia).
  rewrite !(Z.smod_small (- _)); (zify; Z.to_euclidean_division_equations; nia).
Qed.

Lemma square_prod_positives {p : positive} (prime_p : prime p) (odd_p : 3 <= p) :
  pow (∏ positives p) 2 = opp (pow (opp one) ((p - 1) / 2)).
Proof.
  rewrite Zstar.pow_2_r.
  pose proof prod_elements_prime prime_p as H.
  rewrite elements_by_sign in H by lia.
  rewrite negatives_as_positives_odd in H by auto using odd_prime.
  apply (f_equal opp) in H; rewrite ?opp_opp in H.
  rewrite prod_app, prod_opp, prod_rev, (mul_comm (pow _ _)), mul_assoc, <-mul_opp_r in H.
  rewrite length_rev, length_positives_prime in H by trivial.
  replace (Z.of_nat (N.to_nat (Pos.pred_N p / 2))) with ((p - 1) / 2) in H by lia.
  apply (f_equal (fun x => mul x (inv (opp (pow (opp one) ((p - 1) / 2)))))) in H;
  rewrite <-?mul_assoc, mul_inv_same_r, mul_1_r in H.
  rewrite mul_1_l, inv_opp, inv_pow_m1 in H; exact H.
Qed.

Local Lemma prod_snd_abspairs
  {p q : positive} {prime_p : prime p} {prime_q : prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.gcd p q = 1} :
  ∏ map snd (list_prod (elements p) (positives q)) =
  (-1)^((p-1)/2) * (-1)^((q-1)/2*((p-1)/2)) mod q :> Z.
Proof.
  rewrite List.snd_list_prod, prod_concat, map_repeat, prod_repeat.
  rewrite length_elements_prime, N_nat_Z by trivial.
  assert (Z.of_N (Pos.pred_N p) = 2 * ((p-1)/2)) as ->.
  { pose proof odd_prime _ prime_p odd_p. (zify; Z.to_euclidean_division_equations; nia). }
  rewrite pow_mul_r, square_prod_positives, <-mul_m1_l, pow_mul_l, <-pow_mul_r by trivial.
  rewrite ?to_Zmod_mul, ?to_Zmod_pow, ?to_Zmod_opp, ?to_Zmod_1.
  rewrite ?to_Z_mul, ?to_Z_pow_nonneg_r, ?to_Z_opp, ?to_Z_1, ?Z.mod_pow_l, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r;
    trivial; Z.to_euclidean_division_equations; nia.
Qed.

Local Lemma prod_fst_abspairs
  {p q : positive} {prime_p : prime p} {prime_q : prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.gcd p q = 1} :
  ∏ map fst (list_prod (elements p) (positives q)) = (-1)^((q-1)/2) mod p :> Z.
Proof.
  erewrite List.fst_list_prod, prod_flat_map, map_ext, prod_pow, prod_elements_prime; trivial.
  2: { intros. instantiate (1:=((q-1)/2)).
    rewrite prod_repeat, length_positives_prime; trivial; f_equal.
    zify; Z.to_euclidean_division_equations; nia. }
  rewrite to_Zmod_pow, to_Zmod_opp, to_Zmod_1.
  rewrite to_Z_pow_nonneg_r, to_Z_opp, to_Z_1, Z.mod_pow_l; trivial;
    Z.to_euclidean_division_equations; nia.
Qed.

Local Notation combine p q := (fun xy : Zstar _ * Zstar _ => Zstar.of_Zmod (Zmod.of_Z (p*q)%positive (combinecong p%positive q%positive (fst xy) (snd xy)))).

Lemma prod_combinecong
  {p q : positive} {Hp : 3 <= p} {Hq : 3 <= q} {coprime_p_q : Z.gcd p q = 1} (ps : list (Zstar p * Zstar q)) :
  ∏ (map (combine p q)) ps =
  Zstar.of_Zmod (Zmod.of_Z (p*q) (combinecong p q (∏ map fst ps) (∏ map snd ps))).
Proof.
  induction ps as [|[x y]]; cbn [fst snd map fold_right]; [|rewrite IHps; clear IHps].
  { erewrite <-combinecong_complete_coprime_nonneg_nonneg with (a:=1);
    repeat (rewrite ?Z.mod_small, ?to_Zmod_1, ?to_Z_1;
      trivial; try (Z.to_euclidean_division_equations; nia)). }
  rewrite ?to_Zmod_mul, ?to_Z_mul.
  symmetry; erewrite <-combinecong_complete_coprime_nonneg_nonneg with
    (a:=(combinecong p q x y) * (combinecong p q (∏ map fst ps) (∏ map snd ps)))
  by (try lia; rewrite <-Zmult_mod_idemp_r, <-Zmult_mod_idemp_l,
      ?(proj1 (combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?(proj2 (combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?Zmult_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmod_mod; trivial).
  rewrite <-Pos2Z.inj_mul, of_Z_mod, of_Z_mul, of_Zmod_mul; trivial;
  rewrite to_Z_of_Z, Z.gcd_mod_l, ?Pos2Z.inj_mul; apply Z.coprime_mul_r, conj;
  rewrite <-Z.gcd_mod_l,
      ?(proj1 (combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?(proj2 (combinecong_sound_coprime _ _ _ _ coprime_p_q)), ?Z.gcd_mod_l;
  auto using to_Zmod_range.
Qed.

Lemma abs_prod_abs m xs : @abs m (∏ map abs xs) = abs (∏ xs).
Proof.
  induction xs; cbn [fold_right map]; trivial.
  rewrite <-abs_mul_abs_r, IHxs, abs_mul_abs_abs; trivial.
Qed.

Lemma abs_prod_positives_semiprime
  {p q : positive} {prime_p : prime p} {prime_q : prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.gcd p q = 1} :
  abs (∏ positives (p*q)) = abs (∏ map (combine p q) (list_prod (elements p) (positives q))).
Proof.
  intros.
  pose (absq (x : Zstar (p*q)) := if 0 <? Z.smodulo x q then x else opp x).
  assert (abs_absq : forall x, abs (absq x) = abs x). {
    intros. cbv [absq]. destruct Z.ltb; auto using abs_opp. }
  erewrite <-abs_prod_abs, map_ext, <-map_map, abs_prod_abs by (symmetry; apply abs_absq).
  f_equal.
  eapply prod_Permutation .
  eapply Permutation.NoDup_Permutation_bis; cbv [incl].
  { eapply NoDup_map_inv with (f:=abs).
    erewrite map_map, map_ext by (eapply abs_absq).
    pose proof @NoDup_positives (p*q).
    assert (map abs (positives (p * q)) = positives (p*q)).
    { erewrite map_ext_in, map_id; try intros x ?%in_positives; auto using abs_pos. }
    congruence. }
  { rewrite ?length_map, ?length_prod, ?length_elements_prime by trivial.
    pose proof odd_prime p prime_p odd_p as Hp'.
    pose proof odd_prime q prime_q odd_q as Hq'.
    assert (p <> q) by (intro; subst; rewrite Z.gcd_diag in *; lia).
    rewrite length_positives_prime, length_positives_odd, length_elements_semiprime by
      (trivial; Z.to_euclidean_division_equations; lia).
    zify. rewrite Nat2Z.inj_div in *. zify. Z.to_euclidean_division_equations. nia. }
  setoid_rewrite in_map_iff.
  intros ? (?&[]&?).
  exists (of_Zmod (of_Z p (absq x)), of_Zmod (of_Z q (absq x))); cbn [fst snd].
  rewrite in_prod_iff, in_positives.
  pose proof coprime_to_Zmod x as Hc;
    rewrite Pos2Z.inj_mul in Hc; apply Z.coprime_mul_r in Hc; case Hc as [].
  pose proof coprime_to_Zmod (absq x) as Hc;
    rewrite Pos2Z.inj_mul in Hc; apply Z.coprime_mul_r in Hc; case Hc as [].
  repeat rewrite ?to_Zmod_of_Zmod, ?to_Z_of_Z, ?signed_of_Z,
    ?combinecong_mod_l, ?combinecong_mod_r, ?Z.gcd_mod_l; trivial; [].
  (intuition auto using in_elements); [|]; cycle 1. 
  { cbv [absq]; case (Z.ltb_spec 0 (Z.smodulo x q)) as []; trivial. 
    rewrite to_Zmod_opp, to_Z_opp, Pos2Z.inj_mul, <-Z.smod_mod, mod_mod_divide, Z.smod_mod, <-Z.smod_idemp_opp by
      (exists p; lia).
    pose proof Z.smod_pos_bound x q ltac:(lia).
    case (Z.eqb_spec (Z.smodulo x q) 0) as [E|].
    { enough (Z.gcd x q <> 1) by lia.
      apply (f_equal (fun x => x mod q)) in E; rewrite Z.mod_smod, Zmod_0_l in E.
      rewrite <-Z.gcd_mod_l, E, Z.gcd_0_l; lia. }
    rewrite Z.smod_small; try lia.
    pose proof odd_prime q prime_q odd_q as Hq'; Z.to_euclidean_division_equations; nia. }
  erewrite <-combinecong_complete_coprime_nonneg_nonneg; trivial; try lia.
  rewrite <-Pos2Z.inj_mul, of_Z_mod, of_Z_to_Z, of_Zmod_to_Zmod; trivial.
Qed.

Lemma add_seq a b c : map (Nat.add a) (seq b c) = seq (a+b) c.
Proof.
  revert b; induction c; intros;
    cbn [seq map]; rewrite ?IHc, ?Nat.add_succ_r; trivial.
Qed.

Lemma add_seq_0_l a b : map (Nat.add a) (seq 0 b) = seq a b.
Proof. rewrite add_seq, Nat.add_0_r; trivial. Qed.

Local Open Scope nat_scope.
Lemma filter_0mod_seq_0_mul : (forall m, m <> 0 -> forall n,
  filter (fun i => i mod m =? 0) (seq 0 (n * m)) = map (Nat.mul m) (seq 0 n))%nat.
Proof.
  intros until n; induction n; intros; trivial; [].
  rewrite Nat.mul_succ_l, Nat.add_comm, seq_app, filter_app, Nat.add_0_l.
  case m as [|pred_m] eqn:pred_m_eq at 2; [contradiction|]; cbn [seq filter].
  rewrite Nat.Div0.mod_0_l, Nat.eqb_refl.
  erewrite filter_ext_in, filter_false; cycle 1.
  { intros ??%in_seq; apply Nat.eqb_neq; intros [[]X]%Nat.Div0.mod_divides; nia. }
  cbn [map "++"]; rewrite Nat.mul_0_r; f_equal.
  erewrite <-add_seq_0_l, filter_map_swap, filter_ext, IHn; cycle 1.
  { intros. rewrite <-Nat.Div0.add_mod_idemp_l, Nat.Div0.mod_same, Nat.add_0_l; trivial. }
  symmetry. rewrite <-add_seq_0_l, 2map_map; apply map_ext; lia.
Qed.

Lemma filter_cong_seq_mul_mul k m (Hm : m <> 0) : forall n s,
  filter (fun i => i mod m =? k mod m) (seq (s*m) (n*m)) = map (fun i => i*m + k mod m) (seq s n).
Proof.
  induction n; trivial; intros.
  rewrite Nat.mul_succ_l, Nat.add_comm, seq_app, filter_app, <-Nat.mul_succ_l, IHn.
  enough (filter _ _ = [_]) as -> by exact eq_refl.
  pose proof Nat.mod_bound_pos k m ltac:(lia) ltac:(lia).
  replace m with ((k mod m) + (1 + (m-(k mod m+1)))) at 2 by lia.
  rewrite ?seq_app, ?filter_app.
  erewrite filter_ext_in, filter_false, filter_ext_in, filter_true, filter_ext_in, filter_false;
    trivial; intros i ?%in_seq; try apply Nat.eqb_eq; try apply Nat.eqb_neq; assert (s = i / m);
      zify; rewrite ?Nat2Z.inj_div, ?Nat2Z.inj_mod in *; Z.to_euclidean_division_equations; nia.
Qed.

Lemma filter_cong_seq k m (Hm : m <> 0) n s :
  filter (fun i => i mod m =? k mod m) (seq s n) =
  filter (fun i : nat => i mod m =? k mod m) (seq s (n mod m)) ++
  map (Nat.add (s mod m + n mod m + (k mod m + m - s mod m + m - n mod m) mod m))
      (map (Nat.mul m) (seq (s / m) (n / m))).
Proof.
  match goal with |- _ = ?R => set R end.
  pose proof Nat.mod_bound_pos s m ltac:(lia) ltac:(lia).
  pose proof Nat.mod_bound_pos n m ltac:(lia) ltac:(lia).
  rewrite (Nat.div_mod n m), Nat.add_comm, seq_app, (Nat.mul_comm m) by lia.
  rewrite (Nat.div_mod s m) at 2 by lia.
  rewrite <-Nat.add_assoc, Nat.add_comm, <-add_seq by lia.
  rewrite filter_app, filter_map_swap.

  unshelve erewrite (Nat.mul_comm m), (filter_ext _ _ _ (seq (_*m) _)), (filter_cong_seq_mul_mul (k mod m+m-s mod m + m - n mod m)) by lia; shelve_unifiable.
  { intros i; apply eq_true_iff_eq; rewrite 2Nat.eqb_eq; split; intros R.
    { rewrite <-R; clear R.
      apply Nat2Z.inj_iff; repeat rewrite ?Nat2Z.inj_mod, ?Nat2Z.inj_mul, ?Nat2Z.inj_add, ?Nat2Z.inj_sub by lia.
      repeat match goal with
             |- context[Z.of_nat ?x] => is_var x; let x' := fresh x "'" in rename x into x';
             set (Z.of_nat x') as x
             end.
      rewrite <-Z.mod_add with (a:=Z.sub _ _) (b:=-2%Z) by lia.
      replace ((s mod m + n mod m + i) mod m + m - s mod m + m - n mod m + - (2) * m)%Z
         with ((s mod m + n mod m + i) mod m - (s mod m + n mod m))%Z by lia.
      rewrite Zminus_mod_idemp_l. f_equal. lia. }
    { rewrite <-Nat.Div0.add_mod_idemp_r, R by lia; clear R; rewrite !Nat.Div0.add_mod_idemp_r, ?Zmod_mod.
      apply Nat2Z.inj_iff; repeat rewrite ?Nat2Z.inj_mod, ?Nat2Z.inj_mul, ?Nat2Z.inj_add, ?Nat2Z.inj_sub by lia.
      repeat match goal with
             |- context[Z.of_nat ?x] => is_var x; let x' := fresh x "'" in rename x into x';
             set (Z.of_nat x') as x
             end.
      rewrite <-Z.mod_add with (a:=Z.add _ _) (b:=-2%Z) by lia.
      replace (s mod m + n mod m + (k mod m + m - s mod m + m - n mod m) + - (2) * m)%Z
         with (k mod m)%Z by lia.
      apply Z.mod_mod; lia.  } }

  erewrite map_map, map_ext, <-map_map with
    (f:=Nat.mul m)
    (g:=Nat.add(s mod m + n mod m + ((k mod m + m - s mod m + m - n mod m) mod m))).
  2:{ intros i; cbv beta. lia. }

  epose proof fun x => filter_In (fun i : nat => i mod m =? k mod m) x (seq s (n mod m)).
  setoid_rewrite in_seq in H1.

  exact eq_refl.
Qed.
Local Close Scope nat_scope.

Local Lemma coprime_prime_r a p (H : prime p) : Z.gcd a p = 1 <-> a mod p <> 0.
Proof.
  pose proof prime_ge_2 p H.
  rewrite Zgcd_1_rel_prime, Z.mod_divide by lia.
  split; [|intros; apply rel_prime_sym, prime_rel_prime; trivial].
  inversion_clear 1; intros X.
  match goal with H: _ |- _ => case (H _ X (Z.divide_refl _)) as [] end.
  case (Z.eqb_spec x 0); nia.
Qed. 
Local Lemma mul_eq_1_iff a b : a*b = 1 <-> a = 1 /\ b = 1 \/ a = -1 /\ b = -1.
Proof. pose proof Z.eq_mul_1 a b; nia. Qed.
Local Lemma filter_filter {A} f g l :
    @filter A f (filter g l) = filter (fun a => f a && g a) l.
Proof. induction l; cbn; auto. case g; cbn; case f; cbn; rewrite ?IHl; auto. Qed.
Lemma seq_mul_r s n c : seq s (n*c) = flat_map (fun i => seq (s + i*c) c) (seq O n).
Proof.
  revert s; induction n; intros; rewrite ?flat_map_nil_l, ?Nat.add_0_r; trivial.
  cbn [Nat.mul]; rewrite Nat.add_comm, seq_app.
  rewrite seq_S, flat_map_app, IHn; cbn [flat_map]; rewrite app_nil_r; trivial.
Qed.
Lemma seq_0_mur n c : seq O (n*c) = flat_map (fun i => seq (i*c) c) (seq O n).
Proof. apply seq_mul_r. Qed.
Lemma prod_map_filter {A} {m} (f : A -> Zstar m) g (xs : list A) :
  ∏ map f (filter g xs) = div (∏ map f xs) (∏ map f (filter (fun x => negb (g x)) xs)).
Proof.
  induction xs; cbn [map filter fold_right]; rewrite ?div_same; trivial.
  case g; cbn [negb map fold_right]; rewrite !IHxs, ?div_mul_l; trivial.
  rewrite <-!mul_inv_r, ?inv_mul, ?mul_assoc, ?(mul_comm (f a)), ?mul_assoc; f_equal.
  rewrite <-?mul_assoc, mul_inv_same_r, mul_1_r; trivial.
Qed.
Local Lemma to_Zmod_prod {m} xs : @to_Zmod m (∏ xs) = fold_right Zmod.mul Zmod.one (map to_Zmod xs).
Proof. induction xs; cbn; rewrite ?to_Zmod_1, ?to_Zmod_mul, ?IHxs; auto. Qed.
Local Lemma of_Zmod_prod {m} xs : Forall (fun x : Zmod m => Z.gcd x m = 1) xs -> @of_Zmod m (fold_right Zmod.mul Zmod.one xs) = ∏ (map of_Zmod xs).
Proof.
  intros H. apply wlog_eq_Zstar_3; intro Hm.
  induction H; cbn [fold_right map]; rewrite ?of_Zmod_1, ?of_Zmod_mul, ?IHForall; auto.
  clear H IHForall x; induction H0; cbn; rewrite ?to_Z_1, ?Z.gcd_1_l, ?to_Z_mul; try lia.
  rewrite Z.gcd_mod_l, Z.coprime_mul_l; auto.
Qed.
Lemma prod_positives_semiprime
  {p q : positive} {prime_p : prime p} {prime_q : prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.gcd p q = 1} :
  Z.smodulo (∏ positives (p*q)) p =  (-1)^((q-1)/2) * Z.smodulo (q^((p-1)/2)) p.
Proof.
  assert (tl_seq : forall start len, tl (seq start len) = seq (S start) (len-1)).
  { destruct len; rewrite ?Nat.sub_1_r; trivial. }
  assert (
    map_add_seq: forall len start shift : nat, map (Nat.add shift) (seq start len) = seq (shift + start) len
    ).
  { clear; induction len; cbn [seq map]; intros; rewrite ?IHlen, ?Nat.add_succ_r; trivial. }
  assert (
    seq_as_0_l : forall len start shift : nat, seq start len = map (Nat.add start) (seq O len)
    ).
  { clear -map_add_seq; intros. rewrite map_add_seq, Nat.add_0_r; trivial. }
  assert (
div_mul_same_r:
  forall {m : positive} (x y z : Zstar m), div (mul y x) (mul z x) = div y z
  ).
  { clear; intros.
    repeat rewrite <-?mul_inv_r, ?inv_mul, ?(mul_comm x), <-?mul_assoc.
    rewrite mul_inv_same_l, mul_1_r; trivial. }

  assert (div_abs1_r : forall m (x y : Zstar m), abs y = one -> div x y = mul x y).
  { clear; intros m x y H.
    rewrite <-abs_1 in H; eapply eq_sym, eq_abs_iff in H; case H as [->| ->];
        rewrite <-?mul_inv_r, ?inv_opp, ?inv_1; trivial. }


  pose proof odd_prime p prime_p odd_p as Hp'.
  pose proof odd_prime q prime_q odd_q as Hq'.
  rewrite Z.gcd_comm in coprime_p_q.

  assert ((p / 2) < p) by (Z.div_mod_to_equations; nia).

  rewrite <-(Z.smod_smod_divide _ (Pos.mul p q)), smod_unsigned by (exists q; lia).

  (* injecting product into [Zmod p] *)
  rewrite <-signed_of_Z, <-(to_Zmod_of_Zmod (of_Z _ _)); cycle 1.
  { rewrite to_Z_of_Z, <-smod_unsigned, <-Z.mod_smod, Z.smod_smod_divide, Z.mod_smod, Z.gcd_mod_l
      by (exists q; lia).
    pose proof coprime_to_Zmod (∏ positives (p * q)) as Hc;
      rewrite Pos2Z.inj_mul in Hc; apply Z.coprime_mul_r in Hc; case Hc as []; trivial. }

  cbv [positives].
  erewrite to_Zmod_prod, map_map, map_ext_in, map_id; cbv beta.
  2: { intros ? [_ ?]%filter_In. rewrite to_Zmod_of_Zmod by lia; exact eq_refl. }

  rewrite <-(@of_Z_mod p), <-(Z.mod_smod _ p).
  rewrite <-(@smod_unsigned (p*q)), Z.smod_smod_divide, Z.mod_smod by (exists q; lia).
  rewrite <-Zmod.mod_to_Z.
  assert (forall xs, fold_right Zmod.mul Zmod.one xs mod (p*q)%positive = fold_right Z.mul 1 (map to_Z xs) mod (p*q)%positive) as ->.
  { clear -odd_p odd_q. induction xs; cbn; rewrite ?to_Z_1, ?to_Z_mul, ?Zmod_mod by lia; trivial.
    rewrite <-Z.mul_mod_idemp_r, IHxs, Z.mul_mod_idemp_r by lia; trivial. }
  rewrite mod_mod_divide, of_Z_mod by (exists q; lia).
  eassert (forall xs, of_Z _ (fold_right Z.mul 1 xs) = fold_right Zmod.mul Zmod.one (map (of_Z _) xs)) as ->.
  { clear. induction xs; cbn; rewrite ?of_Z_mul, ?IHxs; trivial. }

  rewrite !map_map.
  rewrite of_Zmod_prod, ?map_map; cycle 1.
  { eapply Forall_map, Forall_forall; intros ? [? E%Z.eqb_eq]%filter_In.
    rewrite Pos2Z.inj_mul in E; apply Z.coprime_mul_r in E; case E as [].
    rewrite to_Z_of_Z, Z.gcd_mod_l by (exists q; lia); trivial. }

  (* inclusion-exclusion principle for [Zmod (p * q)] *)
  erewrite filter_ext, <-filter_filter; cbv beta; cycle 1.
  { instantiate (1:=fun x => Z.gcd x p =? 1). instantiate (1:=fun x => Z.gcd x q =? 1).
    intros x. apply eq_true_iff_eq.
    rewrite andb_true_iff, Pos2Z.inj_mul, Z.mul_comm, !Z.eqb_eq, Z.coprime_mul_r; lia. }

  cbv [Zmod.positives].
  rewrite 2 filter_map_swap, ?map_map.
  rewrite prod_map_filter, filter_filter.
  erewrite (filter_ext_in (fun k => andb _ _) (fun k => (Z.of_nat k mod q) =? 0)); cycle 1.
  { intros ? G; apply in_seq in G.
    eapply eq_true_iff_eq. rewrite andb_true_iff, <-eq_true_not_negb_iff, 3Z.eqb_eq.
    rewrite !to_Z_of_Z, !Pos2Z.inj_mul, <-!(Z.gcd_mod_l (Z.of_nat a mod (p * q))),
      !mod_mod_divide, !Z.gcd_mod_l by ((exists q + exists p); lia).
    rewrite !coprime_prime_r by trivial; intuition try lia.
    rewrite !Z.mod_divide in * by lia.
    case (Z.lcm_least p q (Z.of_nat a)) as [d ?]; trivial.
    rewrite Z.gcd_comm, Z.gcd_1_lcm_mul, Z.abs_eq in coprime_p_q by lia.
    assert (0 < d) by nia; zify; Z.div_mod_to_equations; nia. }

  eassert ( let f := _ in let n := _ in filter f (seq 1 n) = filter f (seq 0 (S n))) as ->.
  { cbn [seq filter]. rewrite to_Z_0, Z.gcd_0_l, (proj2 (Z.eqb_neq _ _)); trivial; lia. }
  eassert (S _ = (Pos.to_nat p * Z.to_nat (q / 2) + S (Z.to_nat (p/2)))%nat)
    as -> by (Z.div_mod_to_equations; nia); rewrite Nat.mul_comm.

  (* filtering numerator *)
  erewrite List.filter_ext; cycle 1.
  { intros k. 
    rewrite to_Z_of_Z, <-Z.gcd_mod_l, Pos2Z.inj_mul, mod_mod_divide by (exists q; lia).
    exact eq_refl. }

  rewrite seq_app, seq_mul_r, List.flat_map_concat_map.
  repeat rewrite <-?List.concat_filter_map, ?map_app, ?concat_map, ?map_map, ?filter_app.
  cbn [Nat.add].

  erewrite List.map_ext; cycle 1.
  { intros i.
    replace (Pos.to_nat p) with (S (Pos.to_nat p-1)) at 2 by lia.
    cbn [List.seq List.filter].
    rewrite Nat2Z.inj_mul, positive_nat_Z, Z_mod_mult, Z.gcd_0_l, (proj2 (Z.eqb_neq _ _)) by lia.
    erewrite filter_ext_in, filter_true; [exact eq_refl|]; intros j ?%in_seq; cbv beta.
    rewrite Z.gcd_mod_l, Z.gcd_comm.
    apply Z.eqb_eq, Zgcd_1_rel_prime, prime_rel_prime; trivial.
    rewrite <-Z.mod_divide, (Z.mod_diveq (Z.of_nat i)); lia. }

  cbn [List.seq List.filter].
  rewrite Nat2Z.inj_mul, positive_nat_Z, Z_mod_mult, Z.gcd_0_l, (proj2 (Z.eqb_neq _ _)) by lia.
  erewrite filter_ext_in, filter_true; cycle 1. 
  { intros j ?%in_seq; cbv beta.
  rewrite Z.gcd_mod_l, Z.gcd_comm.
  apply Z.eqb_eq, Zgcd_1_rel_prime, prime_rel_prime; trivial.
  rewrite <-Z.mod_divide, (Z.mod_diveq (Z.of_nat (Z.to_nat (q/2)))); lia. }

  (* multiplying numerator *)
  rewrite prod_app, prod_concat, map_map.
  erewrite map_ext_in, (map_const (opp one)), prod_repeat, length_seq, Z2Nat.id; revgoals.
  { intros i **.
    rewrite <-Nat.add_1_l, Nat.add_comm. rewrite <-map_add_seq, map_map.
    erewrite map_ext_in; cycle 1.
    { intros k Hk; apply in_seq in Hk.
      rewrite to_Z_of_Z, <-of_Z_mod, mod_mod_divide by (exists q; lia).
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul, positive_nat_Z, Z.add_comm.
      rewrite Z.mod_add, of_Z_mod by lia. exact eq_refl. }
    rewrite <-map_map. rewrite <-tl_seq.
    rewrite <-tl_map.
    eassert (map _ _ = Zmod.elements p) as -> by trivial.
      pose proof to_Zmod_elements_prime p ltac:(trivial).
    eassert (map of_Zmod _ = Zstar.elements p) as ->.
    { erewrite <-to_Zmod_elements_prime, map_map, map_ext_in, map_id; trivial; intros.
      rewrite of_Zmod_to_Zmod. trivial. }
    rewrite prod_elements_prime by trivial. exact eq_refl. }
  { clear -odd_q; Z.div_mod_to_equations; nia. }

  erewrite <-Nat.add_1_r, <-map_add_seq, map_map, map_ext_in; cycle 1.
  { intros k **; cbv beta. rapply f_equal.
      rewrite to_Z_of_Z, <-of_Z_mod, mod_mod_divide by (exists q; lia).
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, positive_nat_Z, Z.add_comm, Z2Nat.id by
      (clear -odd_p; Z.div_mod_to_equations; nia).
    rewrite Z.mod_add, of_Z_mod by lia; trivial. }

  (* filtering denominator *)
  eassert (filter _ (seq 1 _) = map (Nat.mul (Z.to_nat q)) (seq 1 (Z.to_nat (p/2)))) as ->.
  { erewrite filter_ext with (g:=fun x => (x mod Pos.to_nat q =? 0 mod Z.to_nat q)%nat); cycle 1.
    { intros i; eapply eq_true_iff_eq.
      rewrite Nat.Div0.mod_0_l.
      rewrite Z.eqb_eq, Nat.eqb_eq, <-Nat2Z.inj_iff, Nat2Z.inj_mod; lia. }
    rewrite filter_cong_seq by lia.
    rewrite Nat.Div0.mod_0_l, Nat.add_0_l, !(Nat.mod_small 1), !(Nat.div_small 1) by lia.
    assert (2 * (Z.to_nat (((p * q)%positive - 1) / 2) mod Z.to_nat q) <= Z.to_nat q)%nat.
    { repeat rewrite ?Nat2Z.inj_le, ?Nat2Z.inj_mod, ?Nat2Z.inj_mul by lia.
      rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia. }
    erewrite filter_ext_in, filter_false; cycle 1; cbn [List.app].
    { intros i ?%in_seq; apply Nat.eqb_neq; intros [d X]%Nat.Lcm0.mod_divide.
      subst i; destruct d; nia. }
    rewrite map_ext_in with (g:=Nat.add (Z.to_nat q)), map_map; cycle 1.
    { intros iq [i [? Hi%in_seq]]%in_map_iff; subst iq.
      repeat rewrite <-?Nat2Z.inj_iff, ?Z2Nat.id, ?Nat2Z.inj_mod, ?Nat2Z.inj_div, ?Nat2Z.inj_add, ?Nat2Z.inj_sub, ?Nat2Z.inj_mul; [|(zify; Z.to_euclidean_division_equations; nia)..].
      rewrite Zminus_mod_idemp_r.
      rewrite <-Z.mod_add with (a:=Z.sub _ _) (b:=-2%Z) by lia.
      eassert (_+-2*q = - (1 + ((p*q)%positive-1)/2)) as -> by lia.
      rewrite Z_mod_nz_opp_full by
        (rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia).
      enough ((1 + ((p * q)%positive - 1) / 2) mod q = 1 + (((p * q)%positive - 1) / 2) mod q) by lia.
      rewrite <-Z.add_mod_idemp_r by lia. rewrite Z.mod_small; trivial.
      rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia.
    }
    rewrite map_ext with (g:=fun i => Nat.mul (Z.to_nat q) (S i)), <-map_map, seq_shift by nia.
    f_equal. f_equal. repeat rewrite <-?Nat2Z.inj_iff, ?Z2Nat.id, ?Nat2Z.inj_div;
      zify; Z.to_euclidean_division_equations; nia. }

  (* multiplying denominator *)
  erewrite map_map, (map_ext_in (fun x : nat => of_Zmod (of_Z p (to_Z _)))); cycle 1.
  { intros ? L%in_seq.
    rewrite to_Z_of_Z, <-of_Z_mod, mod_mod_divide by (exists q; lia).
    rewrite Nat2Z.inj_mul, Z2Nat.id, of_Z_mod, of_Z_mul by lia.
    rewrite of_Zmod_mul; cycle 1.
    { rewrite to_Z_of_Z, Z.gcd_mod_l; trivial. }
    { rewrite to_Z_of_Z, Z.gcd_mod_l.
      apply Zgcd_1_rel_prime, rel_prime_le_prime; trivial.
      clear -L; Z.div_mod_to_equations; nia. }
    exact eq_refl. }
  rewrite <-map_map with (g := mul _), prod_map_mul, length_map, length_seq.

  (* cancellation *)
  rewrite div_mul_same_r, Z2Nat.id by (zify; Z.div_mod_to_equations; lia).
  eassert ((p / 2) = (p-1)/2) as -> by (zify; Z.div_mod_to_equations; lia).
  eassert ((q / 2) = (q-1)/2) as -> by (zify; Z.div_mod_to_equations; lia).
  rewrite div_abs1_r by (rewrite euler_criterion_existsb, abs_of_bool; trivial).

  pose proof (@euler_criterion_existsb p (of_Zmod (of_Z _ q)) ltac:(trivial)) as Heul.
  apply to_Zmod_inj_iff, signed_inj_iff in Heul; revert Heul.

  (* zification *)
  rewrite ?to_Zmod_mul, ?to_Zmod_pow, ?to_Zmod_opp, ?to_Zmod_1.
  rewrite signed_mul, ?signed_pow_nonneg_r, ?signed_opp_small, ?signed_1 by
    (rewrite ?signed_1; zify; Z.div_mod_to_equations; lia).
  rewrite to_Zmod_of_Zmod by (rewrite to_Z_of_Z, Z.gcd_mod_l; trivial).
  rewrite signed_of_Z, Z.smod_pow_l.
  intro Heul.
  rewrite 2Z.smod_small; trivial.

  all : clear -Heul odd_p odd_q Hp' Hq'; rewrite ?Z.pow_m1_l; repeat (case Z.odd; [|]);
     try solve [simpl Z.mul; rewrite ?(Z.gcd_opp_l 1), Z.gcd_1_l; trivial];
     try (zify; Z.to_euclidean_division_equations; nia).
  all : destruct existsb in *; rewrite ?signed_true, ?signed_false in * by lia.
  all : rewrite Heul; clear Heul.
  all : rewrite Z.smod_small; try (zify; Z.to_euclidean_division_equations; nia).
Qed.

Lemma quadratic_reciprocity'
  {p q : positive} {prime_p : prime p} {prime_q : prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.gcd p q = 1} :
  Z.smodulo (q ^ ((p - 1) / 2)) p * Z.smodulo (p ^ ((q - 1) / 2)) q =
  (-1) ^ ((q - 1) / 2 * ((p - 1) / 2)).
Proof.
  pose proof odd_prime p prime_p odd_p as Hp'.
  pose proof odd_prime q prime_q odd_q as Hq'.

  unshelve epose proof abs_prod_positives_semiprime(p:=p)(q:=q) _ as H; trivial.
  unshelve erewrite prod_combinecong, prod_snd_abspairs, prod_fst_abspairs in H; trivial.
  rewrite ?combinecong_mod_l, ?combinecong_mod_r in H.
  apply mul_signed_subgroups_abs, eq_sym in H; trivial.
  progress replace (Z.smodulo (∏ positives (p*q)) q) with (Z.smodulo (∏ positives (q*p)) q) in H
    by (rewrite Pos.mul_comm; trivial).
  erewrite 2@prod_positives_semiprime in H by (trivial || rewrite Z.gcd_comm; trivial).

  rewrite !to_Zmod_of_Zmod, !to_Z_of_Z, !Pos2Z.inj_mul in H.
  2: rewrite to_Z_of_Z, Z.gcd_mod_l, Pos2Z.inj_mul; apply Z.coprime_mul_r;
    split; rewrite <-Z.gcd_mod_l;
    rewrite (proj1 (combinecong_sound_coprime _ _ _ _ coprime_p_q))
    || rewrite (proj2 (combinecong_sound_coprime _ _ _ _ coprime_p_q)); rewrite Z.gcd_mod_l.
  rewrite <-(Z.smod_mod _ p), mod_mod_divide,
    (proj1 (combinecong_sound_coprime _ _ _ _ coprime_p_q)), Z.smod_mod in H by (exists q; lia).
  rewrite <-(Z.smod_mod _ q), mod_mod_divide,
    (proj2 (combinecong_sound_coprime _ _ _ _ coprime_p_q)), Z.smod_mod in H by (exists p; lia).

  rewrite ?(Z.smod_small ((-1)^_)), ?(Z.smod_small ((-1)^_*(-1)^_)) in H.
  enough ((-1) ^ ((p - 1) / 2) * (-1) ^ ((q - 1) / 2) <> 0) by nia.
  all : clear -odd_p odd_q Hp' Hq'; rewrite ?Z.pow_m1_l; repeat (case Z.odd; [|]);
     try solve [simpl Z.mul; rewrite ?(Z.gcd_opp_l 1), Z.gcd_1_l; trivial];
     try (zify; Z.to_euclidean_division_equations; nia).
Qed.

End Zstar.

End Reciprosity.
