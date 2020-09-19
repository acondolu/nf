

(** Aczel's equality *)
Definition eq_aczel {X Y Z} (R: Z -> Z -> Prop) f g :=
  (forall x: X, exists y, R (f x) (g y))
  /\ forall y: Y, exists x, R (f x) (g y).