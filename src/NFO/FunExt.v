(* Extensionally equal functions *)
Definition ext {X Y} f g :=
  forall x: X, f x = (g x : Y).

(* Extensionally equivalent predicates *)
Definition extP {X} P Q :=
  forall x: X, P x <-> Q x.

(* Extensionally equivalent binary predicates *)
Definition extP2 {X Y} P Q :=
  forall x: X, forall y: Y, P x y <-> Q x y.
