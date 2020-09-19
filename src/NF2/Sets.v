From Coq.Logic Require Import Classical_Prop Classical_Pred_Type.

Add LoadPath "src".
Require Import NF2.Model.
From Internal Require Import Misc.

(* The universal set *)
Definition 𝒰 := High False (fun x => match x with end).

Lemma univ_ok : forall x, x ∈ 𝒰.
Proof. intros x H. destruct H. Qed.

(* The empty set *)
Definition Ø := Low False (fun x => match x with end).

Lemma empty_ok : forall x, ~ (x ∈ Ø).
Proof. intros x H. apply H. Qed.

(* Complement *)
Definition neg : set -> set :=
  fun x => match x with
  | Low _ f => High _ f
  | High _ f => Low _ f
  end
.

Lemma neg_ok : forall x y, x ∈ neg y <-> (x ∈ y -> False).
Proof.
  intros x y. destruct y; simpl neg; simpl IN; split; firstorder.
  apply not_all_not_ex. assumption.
Qed.

(* Singleton *)
Definition sing : set -> set :=
  fun x => Low unit (fun _ => x).

Definition sing_ok : forall x y, x ∈ sing y <-> x ≡ y.
Proof.
  intros. simpl. split; intros. destruct H; firstorder. apply ex_unit. symmetry. auto.
Qed.

(* Some auxiliary definitions: *)

Definition minus {X Y} f g : { x : X & forall y : Y, ~ (g y ≡ f x) } -> set :=
  select f (fun x => forall y, ~ (g y ≡ f x)).

Definition meet {X Y} f g : { x : X & exists y : Y, g y ≡ f x } -> set :=
  select f (fun x => exists y, g y ≡ f x).

Definition join {X Y} f g : X + Y -> set := f ⨁ g.

(* Intersection *)
Definition cap x y := match x, y with
  | Low _ f, High _ g => Low _ (minus f g)
  | High _ f, Low _ g => Low _ (minus g f)
  | Low _ f, Low _ g => Low _ (meet f g)
  | High _ f, High _ g => High _ (join f g)
end.
Notation "A ⋂ B" := (cap A B) (at level 85).

Lemma cap1: forall x y z, z ∈ cap x y -> (z ∈ x) /\ (z ∈ y).
Proof.
  destruct x; destruct y; simpl; intro z.
  - rewrite (ex_T (fun x => exists y, _) (fun x => s x ≡ z)).
    firstorder. rewrite<- H in H0. firstorder.
  - rewrite (ex_T (fun x => forall y, ~ _) (fun x => s x ≡ z)).
    firstorder. rewrite<- H0. apply H.
  - rewrite (ex_T (fun x => forall y, ~ _) (fun x => s0 x ≡ z)).
    firstorder. setoid_rewrite H0 in H. firstorder.
  - unfold join. firstorder. apply (H (inl x)). apply (H (inr x)). 
Qed.

Lemma cap2: forall x y z, (z ∈ x) /\ (z ∈ y) -> z ∈ cap x y.
Proof.
  destruct x; destruct y; simpl; unfold meet, minus, join, select; intros; destruct H.
  - rewrite (ex_T (fun x => exists y, _) (fun x => s x ≡ z)).
    destruct H, H0. exists x. firstorder. exists x0. transitivity z. auto. symmetry. auto.
  - rewrite (ex_T (fun x => forall y, ~ _) (fun x => s x ≡ z)).
    destruct H. exists x. firstorder. simpl in H0. setoid_rewrite<- H in H0. apply (H0 y).
  - rewrite (ex_T (fun x => forall y, ~ _) (fun x => s0 x ≡ z)).
    destruct H0. exists x. firstorder. setoid_rewrite H0.
    apply (H y).
  - destruct x. apply (H x). apply (H0 x).
Qed.

Lemma cap_ok : forall x y z, z ∈ (x ⋂ y) <-> (z ∈ x) /\ (z ∈ y).
Proof. intros. split. apply cap1. apply cap2. Qed.

(* Union *)
Definition cup x y := neg (cap (neg x) (neg y)).
Notation "A ∪ B" := (cup A B) (at level 85).

Lemma cup_ok : forall x y z, z ∈ (x ∪ y) <-> (z ∈ x) \/ (z ∈ y).
Proof.
  intros. unfold cup. rewrite neg_ok. rewrite cap_ok. repeat rewrite neg_ok. tauto.
Qed. 
