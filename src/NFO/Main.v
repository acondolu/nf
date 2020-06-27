(** * NFO.Main : NFO Interface *)
(* begin hide *)
Require Import Setoid Morphisms.
Add LoadPath "src".
From NFO Require Eeq Model Iin Ext Union.
(* end hide *)

(** The type of NFO sets *)
Definition set : Type.
  exact Model.set.
Defined.
Notation 𝓥 := set.

(** Equality *)
Definition eeq : 𝓥 -> 𝓥 -> Prop.
  exact Eeq.eeq.
Defined.
Infix "≡" := eeq (at level 50).

Definition eeq_refl : forall x: 𝓥, x ≡ x.
  exact @Eeq.eeq_refl.
Qed.
Definition eeq_sym : forall x y: 𝓥, x ≡ y -> y ≡ x.
  exact @Eeq.eeq_sym.
Qed.
Definition eeq_trans : forall x y z: 𝓥, x ≡ y -> y ≡ z -> x ≡ z.
  exact @Eeq.eeq_trans.
Qed.

Instance nfo_setoid : Equivalence eeq.
  exact Eeq.nfo_setoid.
Qed.

(** Set membership *)
Definition iin : 𝓥 -> 𝓥 -> Prop.
  exact Iin.iin.
Defined.
Infix "∈" := iin (at level 85).

Add Morphism iin with signature eeq ==> eeq ==> iff as iin_morphism.
  exact Morphs.iin_mor.
Qed.

(** Extensionality *)
Definition ext : forall x y: 𝓥, x ≡ y <-> forall z: 𝓥, z ∈ x <-> z ∈ y.
  exact @Ext.ext.
Qed.

(** * Set operators *)

(** Empty set *)
Definition Ø : 𝓥.
  exact Sets.emptyset.
Defined.
Definition emptyset_ok : forall x: 𝓥, ~ (x ∈ Ø).
  exact Sets.emptyset_ok.
Qed.

(** Complement *)
Definition compl : 𝓥 -> 𝓥.
  exact Sets.compl.
Defined.
Definition compl_ok : forall x y: 𝓥, x ∈ (compl y) <-> ~ (x ∈ y).
  exact @Sets.compl_ok.
Qed.

(** Singleton *)
Definition sin : 𝓥 -> 𝓥.
 exact Sets.sin.
Defined.
Definition sin_ok : forall x y: 𝓥, x ∈ (sin y) <-> y ≡ x.
  exact @Sets.sin_ok.
Qed.

(** Co-singleton *)
Definition cosin : 𝓥 -> 𝓥.
  exact Sets.cosin.
Defined.
Definition cosin_ok : forall x y: 𝓥, x ∈ (cosin y) <-> y ∈ x.
  exact @Sets.cosin_ok.
Qed.

(** Union *)
Definition union : 𝓥 -> 𝓥 -> 𝓥.
  exact @Union.cup.
Defined.
Definition union_ok : forall x y z: 𝓥, z ∈ (union x y) <-> z ∈ x \/ z ∈ y.
  exact @Union.cup_ok.
Qed.
