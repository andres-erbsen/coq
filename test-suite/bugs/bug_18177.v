From Coq Require Import PeanoNat.

Arguments Nat.succ_lt_mono {n m}.

Lemma bar (n m : nat) : n < m -> S n < S m.
Proof.
  intros H.
  now apply -> Nat.succ_lt_mono.
Qed.

Axiom foo : unit -> True <-> True.
Axiom foo' : True <-> True.
Goal True.
  Fail apply (foo _). (* Cannot infer this placeholder of type "unit". *)
  Fail apply <-(foo _). (* Tactic failure: <coq-core.plugins.ltac::has_evar@0> where $1 := foo ?u of type constr succeeds. *)
  apply foo'.
  apply foo; try exact tt.
  apply <- foo; try exact tt.
  apply -> foo; try exact tt.
  pose proof I as H.
  apply <- foo in H; try exact tt.
  apply -> foo in H; try exact tt.
  Fail apply (foo _) in H. (* Cannot infer this placeholder of type "unit". *)
  Fail apply <-(foo _) in H. (* Tactic failure: <coq-core.plugins.ltac::has_evar@0> where $1 := foo ?u of type constr succeeds. *)
  exact I.
Qed.
