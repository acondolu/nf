(** * NFO.Main : NFO Interface *)
(* begin hide *)
Add LoadPath "src".
From NFO Require Eeq Model Iin Ext Union.
(* end hide *)

(** The type of NFO sets *)
Definition set
  := Model.set.
Notation 𝓥 := set.

(** Equality *)
Definition eeq : 𝓥 -> 𝓥 -> Prop
  := Eeq.eeq.
Infix "≡" := eeq (at level 50).

Definition eeq_refl : forall x: 𝓥, x ≡ x
  := @Eeq.eeq_refl.
Definition eeq_sym : forall x y: 𝓥, x ≡ y -> y ≡ x
  := @Eeq.eeq_sym.
Definition eeq_trans : forall x y z: 𝓥, x ≡ y -> y ≡ z -> x ≡ z
  := @Eeq.eeq_trans.

(** Set membership *)
Definition iin : 𝓥 -> 𝓥 -> Prop
  := Iin.iin.
Infix "∈" := iin (at level 85).

(** Extensionality *)
Definition ext : forall x y: 𝓥, x ≡ y <-> forall z: 𝓥, z ∈ x <-> z ∈ y
  := @Ext.ext.

(** * Set operators *)

(** Empty set *)
Definition Ø : 𝓥
  := Sets.emptyset.
Definition emptyset_ok : forall x: 𝓥, ~ (x ∈ Ø)
  := Sets.emptyset_ok.

(** Complement *)
Definition compl : 𝓥 -> 𝓥
  := Sets.compl.
Definition compl_ok : forall x y: 𝓥, x ∈ (compl y) <-> ~ (x ∈ y)
  := @Sets.compl_ok.

(** Singleton *)
Definition sin : 𝓥 -> 𝓥 := Sets.sin.
Definition sin_ok : forall x y: 𝓥, x ∈ (sin y) <-> y ≡ x
  := @Sets.sin_ok.

(** Co-singleton *)
Definition cosin : 𝓥 -> 𝓥
  := Sets.cosin.
Definition cosin_ok : forall x y: 𝓥, x ∈ (cosin y) <-> y ∈ x
  := @Sets.cosin_ok.

(** Union *)
Definition union : 𝓥 -> 𝓥 -> 𝓥
  := @Union.cup.
Definition union_ok : forall x y z: 𝓥, z ∈ (union x y) <-> z ∈ x \/ z ∈ y
  := @Union.cup_ok.
