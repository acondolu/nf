Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Wff.
Require Import Eeq.
Require Import Iin.

Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.

Require Import Xor.
Lemma Xor_eq {a a' b b'}: (a <-> a') -> (b <-> b') -> Xor a b <-> Xor a' b'.
Proof. unfold Xor. tauto. Qed.

Lemma eeq_iin_low_1: forall {x y X} {f: X -> _},
  x == y -> iin_low x f <-> iin_low y f.
Proof.
  intros. unfold iin_low. split; intro; destruct H0; exists x0.
  apply (eeq_trans H0 H). apply (eeq_trans H0 (eeq_sym H)).
Qed.
Lemma eeq_iin_low_2: forall {x X Y} {f: X -> _} {g: Y -> _},
  eeq_low f g -> iin_low x f <-> iin_low x g.
Proof.
  intros. unfold iin_low. destruct H. split; intro; destruct H1.
  - destruct (H x0). exists x1. apply (eeq_trans (eeq_sym H2) H1).
  - destruct (H0 x0). exists x1. apply (eeq_trans H2 H1).
Qed.



(* TODO: Prove extensionality *)

Lemma ext_easy: forall z x y, eeq x y ->
  (iin z x <-> iin z y)
  /\ (iin x z <-> iin y z).
Proof.
  induction z. destruct x, y. repeat rewrite iin_unfold. split; apply Xor_eq; rewrite eeq_unfold in H1; destruct H1.
  - apply eeq_iin_low_2. assumption.
  - unfold eeq_boolean in H1.
    pose (fun s : set =>
      (exists a0, s == h0 a0 /\ iin (h0 a0) (S A p h X f))
      \/ (exists a1, s == h1 a1 /\ iin (h1 a1) (S A p h X f))
    ) as g.
    pose proof (H1 g).
    repeat rewrite boolean_map_compose in H3.
    cut (eval (boolean_map (Basics.compose g h0) p0) <-> (let w := fun a : A0 => iin (h0 a) (S A p h X f) in eval (boolean_map w p0))). intro.
    cut (eval (boolean_map (Basics.compose g h1) p1) <-> (let w := fun a : A1 => iin (h1 a) (S A p h X f) in eval (boolean_map w p1))). intro.
    cut (respects g eeq). tauto.
    -- unfold g. unfold respects. intros. admit.
    -- apply boolean_map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold g. split; intro. repeat destruct H5; auto.
       (* GOSH! Serve il symprod a tre! Uffa! *)
       (* right. exists a1. auto.
    -- apply boolean_map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold g. split; intro. repeat destruct H4; auto.
       left. exists a1. auto. 
  - apply eeq_iin_low_1. rewrite eeq_unfold. auto.
  - apply boolean_map_extP. unfold FunExt.extP. intro a.
    apply (H a (S A0 p0 h0 X0 f0) (S A1 p1 h1 X1 f1)). rewrite eeq_unfold. auto.
Qed.


  split; destruct z. rewrite iin_unfold.
  * intro z. destruct x1, x2.
  repeat rewrite iin_unfold in *.
  rewrite eeq_unfold in H0.
  repeat destruct H0.
  unfold Xor.Xor. 
  split; split; destruct H2; destruct H2.
  - left. destruct H3. destruct (H0 x). exists x0.
    apply (eeq_trans (eeq_sym H5) H3).
  - right. unfold eeq_boolean in H1.
    pose proof (H1 (fun x => match x with inl a => iin (h a) z | inr b => iin (h0 b) z end)).
    repeat rewrite boolean_map_compose in H5.
    cut (respects
    (fun x : A + A0 =>
     match x with
     | inl a => iin (h a) z
     | inr b => iin (h0 b) z
     end) (sum_i eeq h h0)).
     --- admit.
     --- unfold respects. destruct x, x'; unfold sum_i.
          intro. apply H. apply AA; apply lt_h. assumption.
          intro. apply H. apply AB; apply lt_h. assumption.
          intro. apply H. apply BA; apply lt_h. assumption.
          intro. apply H. apply BB; apply lt_h. assumption.
Admitted.
(* TODO *)

Lemma eeq_iin: forall x z y, eeq x y -> iin x z <-> iin y z.
Proof.
  apply (@uncurry _ _ (fun x z => forall y, eeq x y -> iin x z <-> iin y z)).
  apply (@well_founded_ind _ _ (wf_swapprod _ lt wf_lt) (fun (a : set * set) => forall (y : set), fst a == y -> iin (fst a) (snd a) <-> iin y (snd a))).
  destruct x. destruct s, s0. intro H. destruct y. simpl.
  repeat rewrite iin_unfold.
  intros. apply Xor_eq.
  - apply eeq_iin_low_1. assumption.
  - apply boolean_map_extP. unfold FunExt.extP. intro a.
    pose proof (H (h0 a, S A p h X f)).  
  split; intro.
  unfold eeq_low in H0. *)
Admitted.
