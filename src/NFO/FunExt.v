Definition ext {X Y} f g :=
  forall x: X, f x = (g x : Y).

Definition extP {X} f g :=
  forall x: X, f x <-> g x.