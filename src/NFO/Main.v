Add LoadPath "src/NFO/".
Require Eeq Model Iin Ext Union.

Module NFO.

(* The type of NFO sets *)
Definition set := Model.set.

(* Equality *)
Definition eeq := Eeq.eeq.
Definition eeq_refl : forall x, eeq x x
  := @Eeq.eeq_refl.
Definition eeq_sym : forall x y, eeq x y -> eeq y x
  := @Eeq.eeq_sym.
Definition eeq_trans : forall x y z, eeq x y -> eeq y z -> eeq x z
  := @Eeq.eeq_trans.

(* Set membership *)
Definition iin : set -> set -> Prop := Iin.iin.

(* Extensionality *)
Definition ext : forall x y, eeq x y <-> forall z, iin z x <-> iin z y
  := @Ext.ext.

(* Set operators *)

(* Empty set *)
Definition emptyset := Sets.emptyset.
Definition emptyset_ok: forall x, ~ iin x emptyset
  := Sets.emptyset_ok.

(* Complement *)
Definition compl := Sets.compl.
Definition compl_ok: forall x y, iin x (compl y) <-> (iin x y -> False)
  := @Sets.compl_ok.

(* Co-singleton *)
Definition cosin := Sets.cosin.
Definition cosin_ok: forall x y, iin x (cosin y) <-> iin y x
  := @Sets.cosin_ok.

(* Singleton *)
Definition sin := Sets.sin.
Definition sin_ok: forall x y, iin x (sin y) <-> eeq y x
  := @Sets.sin_ok.

(* Union *)
Definition union := @Union.cup.
Definition union_ok: forall x y z, iin z (union x y) <-> iin z x \/ iin z y
  := @Union.cup_ok.

End NFO.
