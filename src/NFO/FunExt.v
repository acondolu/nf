(* ext f g holds iff f and g are extensionally equal *)
Definition ext {X Y} f g :=
  forall x: X, f x = (g x : Y).

(* A weaker version of function extensionality on predicates,
   using equivalence instead of equality *)
Definition extP {X} P Q :=
  forall x: X, P x <-> Q x.

(* Extensional binary predicates *)
Definition extP2 {X Y} P Q :=
  forall x: X, forall y: Y, P x y <-> Q x y.
