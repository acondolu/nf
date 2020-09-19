(** * NFO.Main : NFO Interface *)
(** This module gathers the important definitions
    and theorems about NFO.
*)

(* begin hide *)
Add LoadPath "src".
(* end hide *)

Require Import Setoid Morphisms.

From NF2 Require Model Ext Sets.
Module NF2.

(** The type of NF2 sets *)
Definition SET : Type.
  exact Model.SET.
Defined.
Notation 𝓥 := SET.

(** Equality *)
Definition EQ : 𝓥 -> 𝓥 -> Prop.
  exact Model.EQ.
Defined.
Infix "≡" := EQ (at level 50).

Instance nf2_setoid : Equivalence EQ.
  exact Model.nf2_setoid.
Qed.

(** Set membership *)
Definition IN : 𝓥 -> 𝓥 -> Prop.
  exact Model.IN.
Defined.
Infix "∈" := IN (at level 85).

Add Morphism IN with signature EQ ==> EQ ==> iff as IN_morphism.
  exact Model.IN_mor.
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
 exact Sets.sing.
Defined.
Definition sin_ok : forall x y: 𝓥, x ∈ (sin y) <-> y ≡ x.
  exact @Sets.sing_ok.
Qed.

(** Union *)
Definition union : 𝓥 -> 𝓥 -> 𝓥.
  exact @Sets.cup.
Defined.
Definition union_ok : forall x y z: 𝓥, z ∈ (union x y) <-> z ∈ x \/ z ∈ y.
  exact @Sets.cup_ok.
Qed.

End NF2.

From NFO Require Model Eq In Ext Union.
Section NFO.

(** The type of NFO sets *)
Definition SET : Type.
  exact Model.SET.
Defined.
Notation 𝓥 := SET.

(** Equality *)
Definition EQ : 𝓥 -> 𝓥 -> Prop.
  exact Eq.EQ.
Defined.
Infix "≡" := EQ (at level 50).

Instance nfo_setoid : Equivalence EQ.
  exact Eq.nfo_setoid.
Qed.

(** Set membership *)
Definition IN : 𝓥 -> 𝓥 -> Prop.
  exact In.IN.
Defined.
Infix "∈" := IN (at level 85).

Add Morphism IN with signature EQ ==> EQ ==> iff as IN_morphism.
  exact Morphism.IN_mor.
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

End NFO.
