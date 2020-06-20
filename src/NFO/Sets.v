Add LoadPath "src/NFO/".
Require Import Xor.
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Iin.

(* Empty set *)
Definition emptyset :=
  S False (Bot _) (False_rect _) False (False_rect _).

Lemma emptyset_ok: forall x, ~ iin x emptyset.
Proof.
  red. unfold emptyset. intro x. rewrite iin_unfold. unfold Ain. unfold Xor. simpl. destruct 1; repeat destruct H. destruct x0.
  destruct H0.
Qed.

(* Set complement *)
Definition compl x := match x with
  S A p h X f => S A (Not _ p) h X f
end.

Lemma compl_ok: forall x y,
  iin x y <-> (iin x (compl y) -> False).
Proof.
  intro x. destruct y. unfold compl. repeat rewrite iin_unfold. simpl boolean_map. simpl eval. split; intros.
  - unfold Xor in *. tauto.
  - apply negb_xor_r. auto.
Qed.

(* Co-singleton *)
Definition cosin x := S unit (Atom _ tt) (fun _ => x) False (False_rect _).

Lemma cosin_ok: forall x y, iin x (cosin y) <-> iin y x.
Proof.
  intros x y. unfold cosin. rewrite iin_unfold.
  unfold Xor, Ain. simpl. split; intros.
  - destruct H, H. destruct H, x0. unfold iin. assumption.
  - right; auto. split. intro. destruct H0. destruct x0.
    unfold iin' in H. assumption.
Qed.

(* Singleton *)
Definition sin x := S False (Bot _) (False_rect _) unit (fun _ => x).

Lemma sin_ok: forall x y, iin x (sin y) <-> eeq x y.
Proof.
  intros x y. unfold sin. rewrite iin_unfold.
  unfold Xor, Ain. simpl. split; intros.
  - destruct H, H. destruct H. apply eeq_sym. auto. destruct H0.
  - left. split. exists tt. apply eeq_sym. auto. tauto.
Qed.

(* Exclusive or of sets *)

Local Definition boolean_xor {A} (p p': boolean A) :=
  Or _ (Not _ (Or _ p (Not _ p'))) (Not _ (Or _ (Not _ p) p')).

Definition QXor B C := 
  match B, C with S A p h X f, S A' p' h' X' f' =>
  let A'' := sum A A' in
  let h'' := mk_sum h h' in
  let X'' := sum {x: X & ~ exists x', eeq (f' x') (f x)} {x': X' & ~ exists x, eeq (f x) (f' x')} in 
  let f'' := fun xx: X'' => match xx with inl xx' => f (projT1 xx') | inr xx'' => f' (projT1 xx'') end in
  let p'' := boolean_xor (boolean_map inl p) (boolean_map inr p') in
  S A'' p'' h'' X'' f''
end.

Lemma xor_ok: forall x y, forall z, iin z (QXor x y) <-> Xor (iin z x) (iin z y).
Proof.
  intros. destruct x, y. rewrite (Xor_eq iin_unfold' iin_unfold').
  rewrite xor_pairs. unfold QXor. rewrite iin_unfold'. apply Xor_eq.
  - unfold Ain. split; intros. destruct H, x, s; simpl in H.
  -- pose proof (ex_intro (fun x0 => f x0 == z) x H).
      cut (~ exists x0 : X0, f0 x0 == z). intro.
      apply (Xor_1 H0 H1). intro. apply n. destruct H1.
      exists x0. apply (eeq_trans H1 (eeq_sym H)).
  -- pose proof (ex_intro (fun x => f0 x == z) x H).
      cut (~ exists x0, f x0 == z). intro.
      apply (Xor_2 H1 H0). intro. destruct H0, H1.
      apply n. exists x1. apply (eeq_trans H1 (eeq_sym H)).
  -- destruct H, H.
  --- destruct H.
      cut (~ exists x0 : X0, f0 x0 == f x). intro.
      exists (inl (existT _ x H1)). exact H.
      intro O. destruct O. apply H0. exists x0.
      apply (eeq_trans H1 H).
  --- destruct H0.
      cut (~ exists x0, f x0 == f0 x). intro.
      exists (inr (existT _ x H1)). exact H0.
      intro O. destruct O. apply H. exists x0.
      apply (eeq_trans H1 H0).
  - unfold boolean_xor. simpl Qin.
    repeat rewrite<- Qin_aux. simpl. repeat rewrite boolean_map_compose. unfold Basics.compose. simpl mk_sum.
    repeat rewrite Qin_aux. unfold Xor. tauto.
Qed.


(* TODO: Union *)
