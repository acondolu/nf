Definition ext {X Y} f g :=
  forall x: X, f x = (g x : Y).

Definition extP {X} f g :=
  forall x: X, f x <-> g x.

Definition extP2 {X Y} f g :=
  forall x: X, forall y: Y, f x y <-> g x y.