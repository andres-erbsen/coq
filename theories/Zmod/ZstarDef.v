Require Import NArith ZArith Zdiv_facts2 ZModOffset Lia.
Require Import Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Require Import ZmodDef.

Module Zstar.
Import Zmod.
Local Coercion to_Z : Zmod >-> Z.

#[projections(primitive)]
Record Zstar (m : Z) := Private_of_Z_value {
  Private_to_Z : Z ;
  Private_range : Is_true (Private_small Private_to_Z m && 
                             (Z.gcd Private_to_Z m =? 1)) }.
Arguments Private_to_Z {m}.

Definition to_Zmod {m : Z} (a : Zstar m) : Zmod m.
  refine (Zmod.of_small_Z m (Private_to_Z a) (fun _ => _)).
  abstract (case a as [a H]; cbv [Private_to_Z];
    apply Private_small_iff; case Private_small in *; trivial).
Defined.

Local Coercion to_Zmod : Zstar >-> Zmod.

Definition of_coprime_Zmod {m} (a : Zmod m) (H : True -> Z.gcd a m = 1) : Zstar m.
  refine (Private_of_Z_value m (Zmod.to_Z a) (transparent_true _ (fun _ => _))).
  abstract (case a as [a Ha]; cbv [Zmod.to_Z Zmod.Private_to_Z] in *; rewrite ?N2Z.id;
    apply andb_prop_intro, conj, Is_true_eq_left, Z.eqb_eq, H, I; trivial).
Defined.

Definition of_Zmod {m} (x : Zmod m) : Zstar m.
  refine (of_coprime_Zmod (if Z.eqb (Z.gcd x m) 1 then x else Zmod.one) (fun _ => _)).
  abstract (destruct (Z.eqb_spec (Z.gcd x m) 1);
    cbv [Zmod.to_Z Zmod.Private_to_Z Zmod.of_Z Zmod.of_small_Z Zmod.one];
    try rewrite Z.gcd_mod_l, Z.gcd_1_l; trivial).
Defined.

Definition eqb {m} (x y : Zstar m) := Zmod.eqb x y.

Definition one {m} : Zstar m := of_Zmod Zmod.one.

Definition opp {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.opp x).

Definition abs {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.abs x).

Definition mul {m} (a b : Zstar m) : Zstar m.
  refine (of_coprime_Zmod (Zmod.mul a b) (fun _ => _)).
  abstract (case a as [a Ha], b as [b Hb] in *;
    cbv [Zmod.to_Z Zmod.mul Zmod.of_Z Zmod.of_small_Z Zmod.Private_to_Z];
    rewrite Z.gcd_mod_l, Z.coprime_mul_l;
    cbn; apply Is_true_eq_true in Ha, Hb; lia).
Defined.

(**  Inverses and division have a canonical definition  *)

Definition inv {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.inv x).

Definition div {m} (x y : Zstar m) : Zstar m := mul x (inv y).

(**  Powers  *)

Definition pow {m} (a : Zstar m) z := of_Zmod (Zmod.pow a z).

(** Enumerating elements *)

Definition elements m : list (Zstar m) :=
  if Z.eqb m 0 then [one; opp one] else
  map of_Zmod (filter (fun x : Zmod _ => Z.eqb (Z.gcd x m) 1) (Zmod.elements m)).

Definition positives m :=
  map of_Zmod (filter (fun x : Zmod m => Z.gcd x m =? 1) (Zmod.positives m)).

Definition negatives m :=
  map of_Zmod (filter (fun x : Zmod m => Z.gcd x m =? 1) (Zmod.negatives m)).

End Zstar.

Notation Zstar := Zstar.Zstar.
