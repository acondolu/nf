Add LoadPath "src/NFO/".
Require Import Xor Aux.
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Iin.

(* Empty set *)
Definition emptyset :=
  S False (Bot _) (False_rect _) False (False_rect _).

Lemma emptyset_ok: forall x, ~ iin x emptyset.
Proof.
  red. unfold emptyset. intro x. rewrite iin_unfold. unfold Ain, Xor.
  simpl. destruct 1; repeat destruct H. destruct x0. destruct H0.
Qed.

(* Set complement *)
Definition compl x := match x with
  S A p h X f => S A (Not _ p) h X f
end.

Lemma compl_ok: forall x y,
  iin x (compl y) <-> (iin x y -> False).
Proof.
  intros. destruct y. unfold compl. repeat rewrite iin_unfold.
  simpl boolean_map. simpl eval. apply xor_neg_commute.
Qed.

(* Co-singleton *)
Definition cosin x := S unit (Atom _ tt) (fun _ => x) False (False_rect _).

Lemma cosin_ok: forall x y, iin x (cosin y) <-> iin y x.
Proof.
  intros. unfold cosin. rewrite iin_unfold.
  unfold Xor, Ain. simpl. setoid_rewrite ex_false. tauto.
Qed.

(* Singleton *)
Definition sin x := S False (Bot _) (False_rect _) unit (fun _ => x).

Lemma sin_ok: forall x y, iin x (sin y) <-> eeq y x.
Proof.
  intros x y. unfold sin. rewrite iin_unfold.
  unfold Xor, Ain. simpl. rewrite ex_unit. tauto.
Qed.

(* Exclusive or of sets *)

Local Definition boolean_xor {A} (p p': boolean A) :=
  Or _ (Not _ (Or _ p (Not _ p'))) (Not _ (Or _ (Not _ p) p')).

(* Lemma  *)

Definition AXor {X Y} (f: X -> set) (g: Y -> set)
  : sum {x & ~ exists y, eeq (g y) (f x)} {y & ~ exists x, eeq (f x) (g y)} -> set
  := fun s => match s with
      | inl x => f (projT1 x)
      | inr y => g (projT1 y) 
    end.

Definition QXor B C := 
  match B, C with S A p h X f, S A' p' h' X' f' =>
  let A'' := sum A A' in
  let h'' := sum_funs h h' in
  let p'' := boolean_xor (boolean_map inl p) (boolean_map inr p') in
  S A'' p'' h'' _ (AXor f f')
end.

Lemma AXor_ok {X X'} {f: X -> set} {f': X' -> set} {x}:
  Ain x (AXor f f') <-> Xor (Ain x f) (Ain x f').
Proof.
  unfold Ain. split; intros. destruct H, x0, s; simpl in H.
  - pose proof (ex_intro (fun x0 => f x0 == x) x0 H).
      cut (~ exists x0, f' x0 == x). intro.
      apply (Xor_1 H0 H1). intro. apply n. destruct H1.
      exists x1. apply (eeq_trans H1 (eeq_sym H)).
  - pose proof (ex_intro (fun x' => f' x' == x) x0 H).
      cut (~ exists x0, f x0 == x). intro.
      apply (Xor_2 H1 H0). intro. destruct H0, H1.
      apply n. exists x2. apply (eeq_trans H1 (eeq_sym H)).
  - destruct H, H.
  -- destruct H.
      cut (~ exists x', f' x' == f x0). intro.
      exists (inl (existT _ x0 H1)). exact H.
      intro O. destruct O. apply H0. exists x1.
      apply (eeq_trans H1 H).
  -- destruct H0.
      cut (~ exists x', f x' == f' x0). intro.
      exists (inr (existT _ x0 H1)). exact H0.
      intro O. destruct O. apply H. exists x1.
      apply (eeq_trans H1 H0).
Qed.

Lemma QXor_ok {X Y} {h: X -> set} {h0: Y -> set} {z p p0}:
Qin z (sum_funs h h0) (boolean_xor (boolean_map inl p) (boolean_map inr p0)) <-> Xor (Qin z h p) (Qin z h0 p0).
Proof.
  unfold boolean_xor. simpl Qin.
  repeat rewrite<- Qin_aux. simpl. repeat rewrite boolean_map_compose. unfold Basics.compose. simpl sum_funs.
  repeat rewrite Qin_aux. unfold Xor. tauto.
Qed.

Lemma xor_ok: forall x y, forall z, iin z (QXor x y) <-> Xor (iin z x) (iin z y).
Proof.
  intros. destruct x, y. rewrite (xor_iff iin_unfold' iin_unfold').
  rewrite xor_pairs. unfold QXor. rewrite iin_unfold'. apply xor_iff.
  - apply AXor_ok.
  - apply QXor_ok.
Qed.


(* TODO: Union *)


Definition cup B C := 
  match B, C with S A p h X f, S A' p' h' X' f' =>
  let A'' := sum A A' in
  let h'' := sum_funs h h' in
  let p'' := Or _ (boolean_map inl p) (boolean_map inr p') in
  S A'' p'' h'' _ (sum_funs f f') (* FIXME: incorrect! *)
end.


(* Axuliary *)
Definition enum {X} f := S False (Bot _) (False_rect _) X f.
