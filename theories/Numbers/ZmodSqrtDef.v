Require Import ZmodDef.
Require Import NArith ZArith ZModOffset Lia.
Require Import Coq.Bool.Bool Coq.Lists.List.
Require Import Pfactor.
Import ListNotations.
Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Local Coercion N.pos : positive >-> N.
Local Coercion Z.of_N : N >-> Z.

Module Zmod.
Import ZmodDef.Zmod.

(* NOTE: this definition is intended to be replacable with one that does not compute [elements m] *)
(* TODO: move to Zmod *)
Local Definition find {m} f := find f (elements m).

Section WithAB.
Context {m} (phi_m : positive) (a b : Zmod m).
Local Infix "*" := mul.
Local Infix "^" := pow.
Fixpoint chase_sqrt (apow : positive) (bpow : N) :=
  match apow with
  | xO apow => if Zmod.eqb (a^apow * b^N.div2 bpow) one
               then chase_sqrt apow (N.div2 bpow)
               else chase_sqrt apow (N.div2 bpow + N.div2 phi_m)%N
  | xI apow => a^Pos.succ apow * b ^ N.div2 bpow
  | xH =>      a               * b ^ N.div2 bpow
  end.
End WithAB.

Definition sqrtp' {p : positive} (a b : Zmod p) :=
  @chase_sqrt p (Pos.pred p) a b (Pos.div2 (Pos.pred p)) 0.

Definition nonsquare (p : positive) : Zmod p :=
  match find (fun b => eqb (pow b ((p-1)/2)) (opp (@one p))) with
  | Some b => b
  | None => one
  end.

Definition sqrtp {p} (a : Zmod p) :=
  let x := sqrtp' a (nonsquare p) in
  if eqb (pow x 2) a then abs x else zero.

End Zmod.
Notation Zmod := Zmod.Zmod.
Local Coercion Zmod.to_Z : Zmod >-> Z.

Local Fixpoint sqrtp2'' (n : nat) (a : Z) : Z :=
  Z.land (Z.ones (Z.of_nat n))
  match n with
  |0%nat|1%nat|2%nat|3%nat => 1
  |S n => let x := sqrtp2'' n a in
          let k := Z.shiftr (x^2-a) (Z.of_nat n) in
          x + Z.shiftl k (Z.pred (Z.of_nat n))
  end.

Local Definition sqrtp2' (k : Z) (a : Z) : Z :=
  if Z.land a (Z.ones 3) =? 1 then sqrtp2'' (Z.to_nat k) a else 0.

Section WithP.
  Context (p : positive).
  Local Fixpoint sqrtpop' (lgk : nat) (a : Z) : Z :=
    match lgk with
    | O => Zmod.sqrtp (Zmod.of_Z p a)
    | S lgk' =>
        let q := Z.pow p (two_power_nat lgk') in
        let x := sqrtpop' lgk' (a mod q) in
        x + ((x^2 - a)/q * Znumtheory.invmod (-2*x) q) mod q * q
    end.
End WithP.

Local Definition sqrtpp' (p : positive) (k : Z) (a : Z) : Z :=
  if Pos.eqb p 2 then sqrtp2' k a else sqrtpop' p (Z.to_nat (Z.log2_up k)) a.

Definition sqrtpp (p : positive) (k : positive) (a : Z) : Z :=
  let a := Z.modulo a (p^k) in     if Z.eqb 0 a then 0 else
  let v := val p (Z.to_pos a) in   if N.odd v then 0 else
  p^N.div2 v * sqrtpp' p k (a / p^v) mod p^k.

Module Export Sqrtpp.
Module Zmod.
Import ZmodDef.Zmod.

Definition sqrtpp' p k (a : Zmod (p^k)) : Zmod (p^k) :=
  Zmod.of_Z (p^k) (sqrtpp p k a).

Definition sqrtpp {q} (a : Zmod q) : Zmod q :=
  match ppfactor q with
  | [(p, k)] => Zmod.of_Z q (ZmodSqrtDef.sqrtpp p k a)
  | _ => zero
  end.

End Zmod.
End Sqrtpp.

Module Zstar.
Import ZmodDef.Zstar.
Local Coercion to_Zmod : Zstar >-> Zmod.

Definition sqrtp {p} (a : Zstar p) : Zstar p := of_Zmod (Zmod.sqrtp a).

Definition sqrtpp' p k (a : Zstar (p^k)) : Zstar (p^k) :=
  of_Zmod (Zmod.of_Z (p^k) (sqrtpp' p k a)).

Definition sqrtpp {q} (a : Zstar q) : Zstar q :=
  match ppfactor q with
  | [(p, k)] => of_Zmod (Zmod.of_Z q (ZmodSqrtDef.sqrtpp' p k a))
  | _ => one
  end.

End Zstar.

Module Z.
  Definition sqrtmod' a m : Z :=
    let pps := ppfactor m in
    let epps := map (uncurry Pos.pow) pps in
    let rs := map (fun '(p, k) => sqrtpp p k a) pps in
    fst (fold_right (fun '(x1, m1) '(x2, m2) =>
          (Znumtheory.combinecong (Z.pos m1) (Z.pos m2) x1 x2, Pos.mul m1 m2)) (0, xH)
          (combine rs epps)).
  Definition sqrtmod a m :=
    let r := sqrtmod' a m in 
    if r * r mod m =? a then r else 0.
End Z.
