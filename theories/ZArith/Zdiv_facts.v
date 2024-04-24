Require Import BinInt Zdiv Znumtheory PreOmega Lia.
Local Open Scope Z_scope.

Module Z.

Lemma cong_mul_cancel_r_coprime a b m (Hm : m <> 0) (Hb : Z.gcd b m = 1)
  (H : (a * b) mod m = 0) : a mod m = 0.
Proof.
  apply Zmod_divide in H; trivial; [].
  rewrite Z.mul_comm in H; apply Gauss, Zdivide_mod in H; trivial.
  apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
Qed.

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

Definition mod_diveq c a b := proj1 (mod_diveq_iff c a b).

Definition diveq c a b := proj1 (diveq_iff c a b).

Lemma mod_mod_pow a b n m : 0 <= n < m -> (a mod b^m) mod b^n = a mod b^n.
Proof.
  intro; apply mod_mod_divide. exists (b^(m-n)).
  rewrite <-Z.pow_add_r; f_equal; try lia.
Qed.

Lemma div_mod_l_mul_r a b c (Hb : 0 <> b) (Hc : 0 < c) :
  a mod (b * c) / b = (a / b) mod c.
Proof.
  rewrite 2Z.mod_eq by lia.
  rewrite <-Z.add_opp_r, <-Z.mul_opp_r, <-Z.mul_assoc, Z.mul_comm.
  rewrite Z.div_add, Z.div_div; lia.
Qed.

Lemma div_mod_l_pow2_r a b m n (Hb : 0 < b) (H : 0 <= n <= m) :
  a mod b ^ m / b ^ n = a / b ^ n mod b ^ (m - n).
Proof.
  replace m with (n+(m-n)) at 1 by lia; rewrite Z.pow_add_r by lia.
  rewrite div_mod_l_mul_r; lia.
Qed.

Lemma gcd_of_N a b : Z.gcd (Z.of_N a) (Z.of_N b) = Z.of_N (N.gcd a b).
Proof. case a, b; trivial. Qed.

Lemma gcd_mod_l a b : Z.gcd (a mod b) b = Z.gcd a b.
Proof.
  case (Z.eqb_spec b 0) as [->|];
    rewrite ?Zmod_0_r, ?Z.gcd_mod, Z.gcd_comm; trivial.
Qed.

Lemma gcd_mod_r a b : Z.gcd a (b mod a) = Z.gcd a b.
Proof. rewrite Z.gcd_comm, Z.gcd_mod_l, Z.gcd_comm; trivial. Qed.

Lemma mod_pow_l a b c : (a mod c)^b mod c = ((a ^ b) mod c).
Proof.
  destruct (Z.ltb_spec b 0) as [|Hb]. { rewrite !Z.pow_neg_r; trivial. }
  destruct (Z.eqb_spec c 0) as [|Hc]. { subst. rewrite !Zmod_0_r; trivial. }
  generalize dependent b; eapply natlike_ind; trivial; intros x Hx IH.
  rewrite !Z.pow_succ_r, <-Z.mul_mod_idemp_r, IH, Z.mul_mod_idemp_l, Z.mul_mod_idemp_r; trivial.
Qed.

Lemma bezout_1_iff a b : Z.Bezout a b 1 <-> Z.gcd a b = 1.
Proof.
  rewrite Zgcd_1_rel_prime.
  transitivity (Bezout a b 1);
    [|split; eauto using bezout_rel_prime, rel_prime_bezout].
  split; inversion_clear 1; firstorder eauto using Bezout_intro.
Qed.

Lemma coprime_l_factor_l a b c (H : Z.gcd (a*b) c = 1) : Z.gcd a c = 1.
Proof.
  rewrite <-bezout_1_iff in *; case H as (u&v&H).
  exists (u*b), v; lia.
Qed.

Local Lemma Private_coprime_mul a b m : Z.gcd a m = 1 -> Z.gcd b m = 1 -> Z.gcd (a * b) m = 1.
Proof.
  intros.
  apply Zgcd_1_rel_prime, rel_prime_sym, rel_prime_mult;
  apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
Qed.

Lemma coprime_l_factor_r a b c : Z.gcd (a*b) c = 1 -> Z.gcd b c = 1.
Proof. rewrite Z.mul_comm. apply coprime_l_factor_l. Qed.

Lemma coprime_mul_l a b c : Z.gcd (a*b) c = 1 <-> Z.gcd a c = 1 /\ Z.gcd b c = 1.
Proof. intuition eauto using Private_coprime_mul, coprime_l_factor_l, coprime_l_factor_r. Qed.

Lemma coprime_mul_r a b c : Z.gcd a (b*c) = 1 <-> Z.gcd a b = 1 /\ Z.gcd a c = 1.
Proof. rewrite 3(Z.gcd_comm a). apply coprime_mul_l. Qed.

Lemma coprime_r_factor_l a b c : Z.gcd a (b*c) = 1 -> Z.gcd a b = 1.
Proof. rewrite 2(Z.gcd_comm a); apply coprime_l_factor_l. Qed.

Lemma coprime_r_factor_r a b c : Z.gcd a (b*c) = 1 -> Z.gcd a c = 1.
Proof. rewrite 2(Z.gcd_comm a); apply coprime_l_factor_r. Qed.

Lemma coprime_sqr_l a b : Z.gcd (a^2) b = 1 <-> Z.gcd a b = 1.
Proof. rewrite Z.pow_2_r. rewrite coprime_mul_l; intuition auto. Qed.

Lemma coprime_sqr_r a b : Z.gcd a (b^2) = 1 <-> Z.gcd a b = 1.
Proof. rewrite Z.pow_2_r. rewrite coprime_mul_r; intuition auto. Qed.

Lemma coprime_pow_l_iff a n b : 0 < n -> Z.gcd (a^n) b = 1 <-> Z.gcd a b = 1.
Proof.
  pattern n; eapply Z.order_induction_0; try exact _; try lia.
  intros n' n'nn IH ?.
  rewrite Z.pow_succ_r, coprime_mul_l by lia; case (Z.eq_dec n' 0) as [->|];
    rewrite ?Z.pow_0_r, ?Z.gcd_1_l, ?IH by lia; intuition idtac.
Qed.

Lemma coprime_pow_r_iff a b n : 0 < n -> Z.gcd a (b^n) = 1 <-> Z.gcd a b = 1.
Proof. intros; rewrite Z.gcd_comm, coprime_pow_l_iff, Z.gcd_comm; trivial; reflexivity. Qed.

Lemma coprime_pow_l a n b : 0 <= n -> Z.gcd a b = 1 -> Z.gcd (a^n) b = 1.
Proof.
  case (Z.eqb_spec n 0) as [->|]. { rewrite Z.pow_0_r, Z.gcd_1_l; trivial. }
  intros; rewrite coprime_pow_l_iff; lia.
Qed.

Lemma coprime_pow_r a b n : 0 <= n -> Z.gcd a b = 1 -> Z.gcd a (b^n) = 1.
Proof. intros; rewrite Z.gcd_comm. apply coprime_pow_l; auto. rewrite Z.gcd_comm; auto. Qed.

Lemma coprime_prime_prime p q (Hp : prime p) (Hq : prime q) : Z.gcd p q = 1 <-> p <> q.
Proof.
  pose proof prime_ge_2 _ Hp; pose proof prime_ge_2 _ Hq.
  split. { intros ? ->. rewrite Z.gcd_diag in *; lia. }
  intros; apply Zgcd_1_rel_prime.
  case (Z.ltb_spec p q) as []; [|symmetry];
    apply rel_prime_le_prime; trivial; lia.
Qed.

Lemma invmod_1_l' m (H : m <> 0) : invmod 1 m = 1 mod m.
Proof.
  pose proof invmod_coprime' 1 m H ltac:(rewrite Z.gcd_1_l; trivial).
  rewrite Z.mul_1_r, mod_invmod in *; trivial.
Qed.

Lemma invmod_1_l m (H : 2 <= m) : invmod 1 m = 1.
Proof.
  pose proof invmod_coprime 1 m H ltac:(rewrite Z.gcd_1_l; trivial).
  rewrite Z.mul_1_r, mod_invmod in *; trivial.
Qed.
End Z.
