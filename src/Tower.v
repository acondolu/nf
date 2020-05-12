Require Import Coq.Bool.Bool.

Fixpoint tower n: Set := match n with
  | O => unit
  | S m => tower m -> bool
end.

(* Fixpoint ext {n} : (tower n -> bool) -> bool := match n with
| O => fun P => P tt
| S m => fun P => alt (fun z => andb (x z) (y z))
end. *)
Axiom ext: forall {n}, (tower n -> bool) -> bool.
Axiom alt: forall {n}, (tower n -> bool) -> bool.

Definition cS {X Y Z} a (b c: X -> Y) (d: X) : Z := a (b d) (c d).

Fixpoint eqt {n} : tower n -> tower n -> bool := match n with
  | O => fun _ _ => true
  | S m => fun x y => alt (cS andb x y)
end.



Fixpoint liftn {n} : tower n -> tower (S n) := match n with
  | O => fun _ _ => false
  | S m => fun x z => ext (fun z' => andb (eqt (liftn z') z) (x z'))
end.

(* TODO: fix liftn' *)
Fixpoint liftn' {n} : tower n -> tower (S n) := match n with
  | O => fun _ _ => false
  | S m => fun x z => ext (fun z' => andb (eqt (liftn' z') z) (x z'))
end.

Eval cbv in (@liftn 1 (@liftn O tt)).

Definition orbF {X} (f g: X -> bool) x := andb (f x) (g x).

Definition set X := prodT (X -> bool) ((X -> bool) -> bool).

Definition lift n : set (tower n) -> set (tower (S n)) := fun x => match x with
  (a, b) => (orbF (@ liftn (S n) a) b, @liftn' (S (S n)) b)
end.





Definition V := { n: nat & set (tower n)}.

Definition U : V := existT _ O (fun _ => true, fun _ => true).
Definition E : V := existT _ O (fun _ => false, fun _ => false).