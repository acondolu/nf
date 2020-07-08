(** * Internal.List : Quantification on lists *)

Require Import Coq.Lists.List.

Inductive PROP X : Prop :=
  PP : X -> PROP X.
Notation "☐ A" := (PROP A) (at level 85).

Lemma PROP_prod {X Y}: ☐ X -> ☐ Y -> ☐ prod X Y.
Proof.
  intros. destruct H, H0.
  refine (PP _ _). auto.
Qed.

Ltac psplit := apply PROP_prod.
Ltac pleft := refine (PP _ _); left.
Ltac pright := refine (PP _ _); right.
Ltac passumption := apply PP; assumption.
Ltac pauto := refine (PP _ _); auto.

Section List.

Variable A: Type.

(** all/some *)


(** Check whether a predicate is satisfied by all the elements of a list: *)
Fixpoint all P (l: list A): Prop := match l with
| nil => True
| cons b bs => P b /\ all P bs
end.

Fixpoint allT P (l: list A): Type := match l with
| nil => True : Type
| cons b bs => prod (P b) (allT P bs)
end.

Lemma all_PROP: forall {P l},
  all (fun x => ☐ P x) l
  -> ☐ allT (fun x => P x) l.
Proof.
  intros. induction l. simpl. pauto.
  destruct H. psplit. assumption.
  apply IHl. assumption.
Qed.

Lemma allT_all: forall (P: A -> Prop) l, allT P l -> all P l.
Proof.
  induction l. auto. simpl. intros. destruct X. tauto.
Qed.

Fixpoint some P (l: list A) := match l with
| nil => False
| cons b bs => P b \/ some P bs
end.

Fixpoint someT P (l: list A) : Type := match l with
| nil => False : Type
| cons b bs => sum (P b) (someT P bs)
end.

Lemma someT_some: forall (P: A -> Prop) l, someT P l -> some P l.
Proof.
  induction l. auto. simpl. intros. destruct X; tauto.
Qed.
Lemma some_someT: forall (P: A -> Prop) l, some P l -> ☐ (someT P l).
Proof.
  induction l; intro. pauto.
  destruct H. pleft. auto.
  destruct (IHl H). pright. auto.
Qed.

Lemma allT_mono: forall (P: A -> Type) (Q: A -> Type),
  (forall x, P x -> Q x) ->
  forall l, allT P l -> allT Q l.
Proof.
  induction l; simpl; auto.
  intro. destruct X0. firstorder.
Qed.

Lemma all_mono: forall (P Q: A -> Prop),
  (forall x, P x -> Q x)
    -> forall l, all P l -> all Q l.
Proof.
  induction l; simpl; auto.
  intro. destruct H0. firstorder.
Qed.

Lemma all_ext: forall (P Q: A -> Prop),
  (forall x, P x <-> Q x)
    -> forall l, all P l <-> all Q l.
Proof. intros. split; apply all_mono; firstorder. Qed.

Lemma all_In: forall (P: A -> Prop) l,
  all P l <-> forall x, In x l -> P x.
Proof.
  induction l; simpl.
  - split; tauto.
  - split; intros. destruct H0, H. rewrite<- H0. auto. rewrite IHl in H1. auto. split. apply H. left. auto. apply IHl. intros.
  apply H. auto.
Qed.

Lemma some_In: forall (P: A -> Prop) l,
  some P l <-> exists x, In x l /\ P x.
Proof.
  induction l; simpl.
  - split; firstorder.
  - split; intros; destruct H. exists a. auto.
  rewrite IHl in H. destruct H. exists x. firstorder. destruct H, H.
  left. rewrite H. auto. right. apply IHl. exists x. auto.
Qed.

Lemma cons_not_nil: forall x l, @cons A x l <> nil <-> True.
Proof. intros. split; eauto. intro H. intro H0. apply (@nil_cons _ x l). eauto. Qed.

End List.

Arguments all : default implicits.
Arguments allT : default implicits.
Arguments allT_all : default implicits.
Arguments all_mono : default implicits.
Arguments allT_mono : default implicits.
Arguments some : default implicits.
Arguments someT : default implicits.
Arguments someT_some : default implicits.
Arguments some_someT : default implicits.
Arguments some_In : default implicits.
Arguments all_In : default implicits.
Arguments all_ext : default implicits.
