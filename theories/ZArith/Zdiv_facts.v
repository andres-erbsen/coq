Require Import BinInt Zdiv Znumtheory PreOmega Lia.
Local Open Scope Z_scope.

Module Z.

Lemma diveq_iff c a b :
  (b = 0 /\ c = 0 \/ c*b <= a < c*b + b \/ c*b + b < a <= c*b) <-> a/b = c.
Proof.
  destruct (Z.eqb_spec b 0); [subst; rewrite Zdiv_0_r; intuition lia|].
  rewrite <-(Z.sub_move_0_r (_/_)),  <-(Z.add_opp_r (_/_)).
  rewrite <-Z.div_add, Z.div_small_iff; lia.
Qed.

Lemma mod_diveq_iff c a b :
  (b = 0 \/ c*b <= a < c*b + b \/ c*b + b < a <= c*b) <-> a mod b = a-b*c.
Proof.
  destruct (Z.eqb_spec b 0); [subst; rewrite Zmod_0_r; intuition lia|].
  rewrite Z.mod_eq by trivial; pose proof diveq_iff c a b; nia.
Qed.

(* Usage: rewrite (mod_diveq (-1)) by lia *)
Definition mod_diveq c a b := proj1 (mod_diveq_iff c a b).

Definition diveq c a b := proj1 (diveq_iff c a b).

Lemma eq_mod_opp m x y : x mod -m = y mod -m <-> x mod m = y mod m.
Proof.
  intros.
  case (Z.eq_dec (x mod m) 0), (Z.eq_dec (y mod m) 0) as [];
    repeat rewrite ?Z_mod_zero_opp_r, ?Z_mod_nz_opp_r in * by lia.
  all : (intuition try lia); Z.div_mod_to_equations; lia.
Qed.

Lemma eq_mod_abs m x y : x mod (Z.abs m) = y mod (Z.abs m) <-> x mod m = y mod m.
Proof.
  case (Z.abs_eq_or_opp m) as [->| ->].
  reflexivity.
  apply eq_mod_opp.
Qed.

Lemma mod_mod_opp a b : (a mod - b) mod b = a mod b.
Proof.
  replace a with (--a) at 1 by apply Z.opp_involutive.
  rewrite Zmod_opp_opp, Z.mod_opp_mod_opp; trivial.
Qed.

Lemma mod_mod_opp' a b : (a mod b) mod - b = a mod - b.
Proof. rewrite <-(mod_mod_opp a (-b)), Z.opp_involutive; trivial. Qed.

Lemma mod_mod_abs a b : (a mod Z.abs b) mod b = a mod b.
Proof.
  case b as []; cbn [Z.abs].
  { rewrite ?Zmod_0_r; trivial. }
  { apply Z.mod_mod; inversion 1. }
  { rewrite <-Pos2Z.opp_pos. apply mod_mod_opp'. }
Qed.

Lemma mod_mod_abs' a b : (a mod b) mod Z.abs b = a mod Z.abs b.
Proof.
  case b as []; cbn [Z.abs].
  { rewrite ?Zmod_0_r; trivial. }
  { apply Z.mod_mod; inversion 1. }
  { rewrite <-Pos2Z.opp_pos. apply mod_mod_opp. }
Qed.
End Z.
