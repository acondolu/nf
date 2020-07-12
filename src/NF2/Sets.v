From Coq.Logic Require Import Classical_Prop Classical_Pred_Type.

Add LoadPath "src".
Require Import NF2.Model.
From Internal Require Import Misc.

(* The universal set *)
Definition 𝒰 : 𝓥 := Neg (fun x: False => match x with end).

Lemma univ_ok : forall x, x ∈ 𝒰.
Proof. intros x H. destruct H. Qed.

(* The empty set *)
Definition Ø : 𝓥 := Pos (fun x: False => match x with end).

Lemma empty_ok : forall x, ~ (x ∈ Ø).
Proof. intros x H. apply H. Qed.

(* Complement *)
Definition neg : 𝓥 -> 𝓥 :=
  fun x => match x with
  | Pos f => Neg f
  | Neg f => Pos f
  end
.

Lemma neg_ok : forall x y, x ∈ neg y <-> (x ∈ y -> False).
Proof.
  intros x y. destruct y; simpl neg; simpl iin; split.
  - intros. destruct H0. apply (H x0 H0).
  - intros H x0 H'. apply H. exists x0. assumption.
  - intros. destruct H. apply (H0 x0). assumption.
  - apply not_all_not_ex.
Qed.

(* Singleton *)
Definition sing : 𝓥 -> 𝓥 :=
  fun x => @Pos unit (fun _ => x).

Definition sing_ok : forall x y, x ∈ sing y <-> x ≡ y.
Proof.
  intros. simpl. split; intros. destruct H. apply eeq_sym.
  assumption. exists tt. apply eeq_sym. assumption.
Qed.

(* Some auxiliary definitions: *)

Definition minus {X Y} f g : { x : X & forall y : Y, ~ (g y ≡ f x) } -> 𝓥 :=
  select f (fun x => forall y, ~ (g y ≡ f x)).

Definition meet {X Y} f g : { x : X & exists y : Y, g y ≡ f x } -> 𝓥 :=
  select f (fun x => exists y, g y ≡ f x).

Definition join {X Y} f g : X + Y -> 𝓥 := f ⨁ g.

(* Intersection *)
Definition cap x y := match x, y with
  | Pos f, Neg g => Pos (minus f g)
  | Neg f, Pos g => Pos (minus g f)
  | Pos f, Pos g => Pos (meet f g)
  | Neg f, Neg g => Neg (join f g)
end.
Notation "A ⋂ B" := (cap A B) (at level 85).

Lemma cap1: forall x y z, z ∈ cap x y -> (z ∈ x) /\ (z ∈ y).
Proof.
  destruct x; destruct y; simpl; intro z.
  - rewrite (ex_T (fun x => exists y, _) (fun x => s x ≡ z)). intros. destruct H, H, H. split. firstorder. rewrite<- H in H0. firstorder.
  - rewrite (ex_T (fun x => forall y, ~ _) (fun x => s x ≡ z)).
    intros. destruct H, H. firstorder. rewrite<- H0. apply H.
  - rewrite (ex_T (fun x => forall y, ~ _) (fun x => s0 x ≡ z)).
    intros. destruct H, H. setoid_rewrite H0 in H. firstorder.
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
