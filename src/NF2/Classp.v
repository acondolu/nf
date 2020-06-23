Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Add LoadPath "src".
From NF2 Require Import Model Sets.

Fixpoint bool a := match a with
  | Pos f => exists x, ~ bool (f x)
  | Neg f => forall x,   bool (f x)
end.

Lemma bool_bot : ~ bool Ø.
Proof.
  unfold bool. unfold Ø. cbv. intro. destruct H. destruct x.
Qed.

Lemma bool_neg : forall a, bool (sing a) <-> ~ bool a.
Proof.
  intros. unfold sing. simpl bool. split; intro.
  destruct H. auto. exists tt. auto.
Qed.

Lemma bool_and : forall a b, bool (sing (sing a ∪ sing b)) <-> bool a /\ bool b.
Proof.
  intros. unfold sing, cup. simpl bool. split; split.
  - destruct H. apply NNPP. intro. apply H. exists (inl tt).
   unfold join. auto. 
   - destruct H. apply NNPP. intro. apply H. exists (inr tt).
   unfold join. auto.
  - exact tt.
  - destruct H. intro. destruct H1. destruct x; apply H1; assumption.
Qed.

Lemma bool_or : forall a b, bool (sing (sing a) ∪ sing (sing b)) <-> bool a \/ bool b.
Proof.
  intros. unfold sing, cup. simpl bool. split; intros.
  - destruct H. destruct x. left. unfold join in *. pose proof (bool_neg a). unfold sing in *. tauto. right. unfold join in *. pose proof (bool_neg b). unfold sing in *. tauto.
  - destruct H. exists (inl tt). unfold join. pose proof (bool_neg a). tauto. exists (inr tt). unfold join. pose proof (bool_neg b). tauto.
Qed.