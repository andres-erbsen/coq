Require Import NArith ZArith ZModOffset Lia.
Require Import Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Module Zmod.

Definition Private_small z m :=
  (0 =? m) || negb (Z.sgn z =? -Z.sgn m) && (Z.abs z <? Z.abs m).

Lemma Private_small_iff z m :
  Bool.Is_true (Private_small z m) <-> z mod m = z.
Proof.
  rewrite Z.mod_id_iff.
  cbv [Private_small Is_true]. case m as [|m|m], z as [|z|z];
   cbn; try case Z.ltb eqn:?; lia.
Qed.

#[projections(primitive)]
Record Zmod (m : Z) := Private_of_Z_value {
  Private_to_Z : Z ; Private_range : Bool.Is_true (Private_small Private_to_Z m) }.
Arguments Private_to_Z {m}.

Definition unsigned {m} (x : Zmod m) := Private_to_Z x.
Notation to_Z := unsigned (only parsing).
Local Coercion to_Z : Zmod >-> Z.

Local Lemma mod_to_Z {m} (x : Zmod m) : x mod m = x.
Proof. case x as [x H]; apply Private_small_iff, H. Qed.

Local Lemma unsigned_range {m} (x : Zmod m) : 0 <= x < m \/ m = 0 \/ m < x <= 0.
Proof. apply Z.mod_id_iff, mod_to_Z. Qed.

Definition of_small_Z (m : Z) (z : Z) (H : True -> z mod m = z) : Zmod m.
  refine (Private_of_Z_value m z (transparent_true _ (fun _ => _))).
  abstract apply Private_small_iff, H, I.
Defined.

Definition of_Z (m : Z) (z : Z) : Zmod m.
  refine (of_small_Z m (z mod m) (fun _ => _)).
  abstract apply Zmod_mod.
Defined.

Definition signed {m} (x : Zmod m) : Z :=
  if Z.ltb (Z.double (Z.abs x)) (Z.abs m) then x else x-m.

Definition zero {m} := of_Z m 0.

Definition one {m} := of_Z m 1.

(** ** Ring operations *)

Definition eqb {m} (x y : Zmod m) := Z.eqb (to_Z x) (to_Z y).

Definition add {m} (x y : Zmod m) : Zmod m.
  refine (let n := x + y in of_small_Z m (if Z.ltb (Z.abs n) (Z.abs m) then n else n-m) (fun _ => _)).
  abstract (pose proof unsigned_range x; pose proof unsigned_range y;
    case Z.ltb eqn:?; rewrite Z.mod_id_iff; lia).
Defined.

Definition sub {m} (x y : Zmod m) : Zmod m.
  refine (let z := x - y in of_small_Z m (if Z.sgn z =? -Z.sgn m then z+m else z) (fun _ => _)).
  abstract (pose proof unsigned_range x; pose proof unsigned_range y;
    case (Z.eqb_spec (Z.sgn z) (-Z.sgn m)); rewrite Z.mod_id_iff; lia).
Defined.

Definition opp {m} (x : Zmod m) : Zmod m := sub zero x.

Definition mul {m} (x y : Zmod m) : Zmod m := of_Z m (x * y).

(** ** Three notions of division *)

Definition udiv {m} (x y : Zmod m) : Zmod m. refine (
    if Z.eq_dec 0 y then opp one else of_small_Z m (
    let z := Z.div x y in
    if Z.sgn z =? -Z.sgn m then z+m else z
  ) (fun _ => _)).
  abstract (
    pose proof unsigned_range x; pose proof unsigned_range y; apply Z.mod_id_iff;
    cbn [Z.sgn]; destruct Z.eqb eqn:?;
    Z.to_euclidean_division_equations; nia).
Defined.

Definition umod {m} (x y : Zmod m) : Zmod m.
  refine (of_small_Z m (Z.modulo (unsigned x) (unsigned y)) (fun _ => _)).
  abstract (pose proof unsigned_range x; pose proof unsigned_range y; apply Z.mod_id_iff;
    zify; Z.to_euclidean_division_equations; nia).
Defined.

Definition squot {m} (x y : Zmod m) :=
  of_Z m (if signed y =? 0 then -1 else Z.quot (signed x) (signed y)).

Definition srem {m} (x y : Zmod m) := of_Z m (Z.rem (signed x) (signed y)).

Definition inv {m} (x : Zmod m) : Zmod m.
  refine (of_small_Z m (Znumtheory.invmod (to_Z x) m) (fun _ => _)).
  apply Znumtheory.mod_invmod.
Defined.

Definition mdiv {m} (x y : Zmod m) : Zmod m := mul x (inv y).

(** ** Powers  *)

Local Definition Private_pow_N {m} (a : Zmod m) n := N.iter_op mul one a n.
Definition pow {m} (a : Zmod m) z :=
  if Z.ltb z 0 then inv (Private_pow_N a (Z.to_N (Z.opp z))) else Private_pow_N a (Z.to_N z).

(** ** Bitwise operations *)
Definition and {m} (x y : Zmod m) := of_Z m (Z.land x y).

Definition ndn {m} (x y : Zmod m) := of_Z m (Z.ldiff x y).

Definition or {m} (x y : Zmod m) := of_Z m (Z.lor x y).

Definition xor {m} (x y : Zmod m) := of_Z m (Z.lxor x y).

Definition not {m} (x : Zmod m) := of_Z m (Z.lnot (to_Z x)).

Definition abs {m} (x : Zmod m) := if signed x <? 0 then opp x else x.

(** ** Shifts *)

Definition slu {m} (x : Zmod m) n := of_Z m (Z.shiftl x n).

Definition sru {m} (x : Zmod m) n := of_Z m (Z.shiftr x n).

Definition srs {m} x n := of_Z m (Z.shiftr (@signed m x) n).

(** ** Bitvector operations that vary the modulus *)

(** Effective use of the operations defined here with moduli that are not
   converitble to values requires substantial understanding of dependent types,
   in particular the equality type, the sigma type, and their eliminators. Even
   so, many applications are better served by [Z] or by adopting one
   common-denominator modulus. See the four variants of [skipn_app] and
   [app_assoc], for a taste of the challenges. *)

Local Notation bits n := (Zmod (2^n)). (* n : N *)

Definition app {n m} (a : bits n) (b : bits m) : bits (n+m) :=
  of_Z _ (Z.lor a (Z.shiftl b n)).

Definition firstn n {w} (a : bits w) : bits n := of_Z _ a.

Definition skipn n {w} (a : bits w) : bits (w-n) := of_Z _ (Z.shiftr a n).

Definition extract start pastend {w} (a : bits w) : bits (pastend-start) :=
  firstn (pastend-start) (skipn start a).

(** ** Enumerating elements *)

Definition elements m : list (Zmod m) :=
  map (fun i => of_Z m (Z.of_nat i)) (seq 0 (Z.abs_nat m)).

Definition positives m :=
  let p := (Z.abs m - Z.b2z ((0 <? m)))/2 in
  map (fun i => of_Z m (Z.of_nat i)) (seq 1 (Z.to_nat p)).

Definition negatives m :=
  let p := (Z.abs m - Z.b2z ((0 <? m)))/2 in
  let r := Z.abs m - 1 - p in
  map (fun i => of_Z m (Z.of_nat i)) (seq (S (Z.to_nat p)) (Z.to_nat r)).

Definition invertibles m : list (Zmod m) :=
  if Z.eqb m 0 then [one; opp one] else
  filter (fun x : Zmod _ => Z.eqb (Z.gcd x m) 1) (elements m).

End Zmod.

Notation Zmod := Zmod.Zmod.

Notation bits n := (Zmod (2^n)).

Module bits.
  Notation of_Z n z := (Zmod.of_Z (2^n) z).
End bits.

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
