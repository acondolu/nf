Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Add LoadPath "src/".
Require Import Simplest.

(* The universal set *)
Definition 𝒰 : 𝓥 := @Neg False (fun x => match x with end).

Lemma univ_okay : forall x, x ∈ 𝒰.
Proof. intros x H. destruct H. Qed.

(* The empty set *)
Definition Ø : 𝓥 := @Pos False (fun x => match x with end).

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
  - apply all_not_not_ex.
  - apply not_ex_all_not.
  - intros. revert H. apply all_not_not_ex. assumption. 
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

Definition minus {X Y} f g : { x : X & forall y : Y, ~ (f x ≡ g y) } -> 𝓥 :=
    (fun ex => match ex with existT _ x _ => f x end)
.
Definition meet {X Y} f g : { x : X & exists y : Y, f x ≡ g y } -> 𝓥 :=
    (fun ex => match ex with existT _ x _ => f x end)
.
Definition join {X Y} f g : X + Y -> 𝓥 :=
  fun z => match z with
  | inl x => f x
  | inr y => g y
  end.

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
  destruct x; destruct y.
  - simpl cap. unfold meet. simpl iin. intros. destruct H. destruct x. destruct e. split. exists x. exact H. exists x0. apply (fun X => eeq_trans X H). apply eeq_sym. assumption.
  - simpl cap. unfold minus. simpl iin. intros. destruct H. destruct x.
    split. exists x. assumption. intros. apply (n x0). apply (eeq_trans H). apply eeq_sym. assumption.
  - simpl cap. unfold minus. simpl iin. intros. destruct H. destruct x. 
    split. intros. apply (n x0). apply (eeq_trans H). apply eeq_sym. assumption.
    exists x. assumption.
  - simpl cap. unfold join. simpl iin. intros. split; intros.
    apply (H (inl x)). assumption. apply (H (inr x)). assumption.
Qed.

Lemma cap2: forall x y z, (z ∈ x) /\ (z ∈ y) -> z ∈ cap x y.
Proof.
  destruct x; destruct y; intros; destruct H; simpl cap; simpl iin.
  - unfold meet. simpl iin in *. destruct H. destruct H0.
    pose proof (eeq_trans H (eeq_sym H0)).
    exists (existT _ x (ex_intro _ x0 H1)). assumption.
  - unfold minus. simpl iin in *. destruct H.
    cut (forall x0 : X0, ~ (s x ≡ s0 x0)).
    intro. exists (existT _ x H1). assumption.
    intros x0 H1. apply (H0 x0). apply (fun X => eeq_trans X H).
    apply eeq_sym. assumption.
  - unfold minus. simpl iin in *. destruct H0 as [x0 H0].
    cut (forall x : X, ~ (s0 x0 ≡ s x)).
    intro. exists (existT _ x0 H1). assumption.
    intros x H1. apply (H x). apply (fun X => eeq_trans X H0).
    apply eeq_sym. assumption.
  - unfold join. simpl iin in *. intros. destruct x.
    -- apply (H x). assumption.
    -- apply (H0 x). assumption.
Qed.

Lemma cap_ok : forall x y z, z ∈ (x ⋂ y) <-> (z ∈ x) /\ (z ∈ y).
Proof. intros. split. apply cap1. apply cap2. Qed.

(* Union *)
Definition cup x y := neg (cap (neg x) (neg y)).
Notation "A ∪ B" := (cup A B) (at level 85).

Lemma cup_ok : forall x y z, z ∈ (x ∪ y) <-> (z ∈ x) \/ (z ∈ y).
Proof.
  intros. unfold cup. split; intros.
  - rewrite neg_ok in H. rewrite cap_ok in H. rewrite neg_ok in H. rewrite neg_ok in H.
    apply NNPP. intro. apply H. split; intro; apply H0. left. assumption. right. assumption.
  - apply neg_ok. intro. rewrite cap_ok in H0. rewrite neg_ok in H0. rewrite neg_ok in H0. destruct H0.
    destruct H. apply H0. assumption. apply H1. assumption.
Qed. 
