Add LoadPath "src/NFO/".
Require Eeq.
Require Model.
Require Iin.
Require Ext.
Require Union.


Module NFO.

(* The type of NFO sets *)
Definition set := Model.set.

(* Equality *)
Definition eeq := Eeq.eeq.
Definition eeq_refl : forall x, eeq x x := @Eeq.eeq_refl.
Definition eeq_sym : forall x y, eeq x y -> eeq y x := @Eeq.eeq_sym.
Definition eeq_trans : forall x y z, eeq x y -> eeq y z -> eeq x z := @Eeq.eeq_trans.

(* Set membership *)
Definition iin : set -> set -> Prop := Iin.iin.

(* Extensionality *)
Definition ext : forall x y, eeq x y <-> forall z, iin z x <-> iin z y := @Ext.ext.

(* TODO: put here set operators *)
Definition union := @Union.cup.
Definition union_ok
  : forall x y z, iin z (union x y) <-> iin z x \/ iin z y
  := Union.cup_ok.

End NFO.
