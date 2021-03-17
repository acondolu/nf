Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Add LoadPath "src/Internal" as Internal.
Add LoadPath "src/NF2" as NF2.
Require Import NF2.Model.
From Internal Require Import Misc.

(*
  The axiom of regularity does not hold in this set theory.
  The weaker form of regularity holds, and its necessary to 
  prove extensionality: a positive set does cannot belong to itself.
*)
Theorem weak_regularity: forall {x}, low x -> IN x x -> False.
Proof.
  induction x; simpl low; auto; intros.
  assert (H1' := H1). destruct H1. apply (H x).
  - destruct (s x); simpl; auto.
  - setoid_rewrite H1. assumption.
Qed.

(* 
  The lemma [pos_neg_ext_neq] below is fundamental to
  prove extensionality. It proves that a positive set cannot
  be extensionally equal to a negative set.

  In order to prove [pos_neg_ext_neq], we first prove the
  auxiliary [pos_univ]. It says that if a positive set is
  extensionally equal to a negative set, then one can
  express the universal set (defined as negative) as a
  positive set.
  This, together with weak regularity, yields the required
  contradiction.
*)


Lemma pos_univ: forall X f Y g,
  (forall z, IN z (Low X f) <-> IN z (High Y g))
  -> forall z, IN z (Low (X + Y) (f ⨁ g)).
Proof.
  intros. simpl IN in *.
  pose proof (H z).
  destruct (classic (exists x : X, EQ (f x) z)).
  - destruct H1. exists (inl x). tauto.
  - cut (exists y : Y, EQ (g y) z). intro. destruct H2.
    exists (inr x). auto.
  destruct H0. pose proof (fun T => H1 (H2 T)).
  apply NNPP. intro. apply H3. intros x HH. apply H4. exists x. auto.
Qed.

Lemma pos_neg_ext_neq: forall X f Y g,
  (forall z, IN z (Low X f) <-> IN z (High Y g)) -> False.
Proof.
  intros.
  pose proof (pos_univ _ _ _ _ H).
  apply (@weak_regularity (Low (X + Y) (f ⨁ g)) I). apply H0.
Qed.

Lemma ext_pos: forall X f Y g,
  (forall z, IN z (Low X f) <-> IN z (Low Y g))
  -> EQ (Low X f) (Low Y g).
Proof.
  intros. simpl; split; intro.
  - destruct (H (f x)). simpl IN in H0.
    cut (exists x0 : X, EQ (f x0) (f x)). intro. destruct (H0 H2). exists x0. apply EQ_sym. assumption. exists x. apply EQ_refl.
  - destruct (H (g y)). simpl IN in H1.
  cut (exists x : Y, EQ (g x) (g y)). intro. destruct (H1 H2). exists x. assumption. exists y. apply EQ_refl.
Qed.

Lemma not_ex_all_not_iff: forall {U} (P: U -> Prop),
  ~ (exists n : U, P n) <-> forall n:U, ~ P n.
Proof.
  split. apply not_ex_all_not. firstorder.
Qed.

Lemma ext_neg: forall X f Y g,
  (forall z, IN z (High X f) <-> IN z (High Y g))
  -> EQ (High X f) (High Y g).
Proof.
  simpl. intros. apply (ext_pos X f Y g). simpl. intro z. specialize H with z.
  setoid_rewrite<- not_ex_all_not_iff in H. tauto.
Qed.

Theorem ext: forall x y, x ≡ y <-> forall z, z ∈ x <-> z ∈ y.
Proof.
  intros. split.
  - intros. split; apply in_sound_right; auto. symmetry. assumption.
  - destruct x; destruct y.
  -- apply ext_pos.
  -- intros. destruct (pos_neg_ext_neq _ _ _ _ H).
  -- intros. symmetry. apply (pos_neg_ext_neq X0 s0 X s). firstorder.
  -- apply ext_neg.
Qed.
