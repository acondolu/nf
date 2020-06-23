Add LoadPath "src/NFO/".
Require Import Xor Aux FunExt.
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Iin.

(* Axuliary *)
Definition enum {X} f := S False (Bot _) (False_rect _) X f.

Lemma Qin_sum_inl: forall X Y z (f: X -> set) (g: Y -> set) p,
  Qin z (sum_funs f g) (boolean_map inl p) <-> Qin z f p.
Proof.
  induction p; simpl.
  - tauto.
  - tauto.
  - setoid_rewrite IHp. tauto.
  - setoid_rewrite IHp1. setoid_rewrite IHp2. tauto.
Qed.

Lemma Qin_sum_inr: forall X Y z (f: X -> set) (g: Y -> set) p,
  Qin z (sum_funs f g) (boolean_map inr p) <-> Qin z g p.
Proof.
  induction p; simpl.
  - tauto.
  - tauto.
  - setoid_rewrite IHp. tauto.
  - setoid_rewrite IHp1. setoid_rewrite IHp2. tauto.
Qed.

Lemma Ain_sum {X X'} {f: X -> set} {f': X' -> set} {x}:
  Ain x (sum_funs f f') <-> (Ain x f) \/ (Ain x f').
Proof.
  unfold Ain, sum_funs. split; intro.
  - destruct H, x0. left; eauto. right; eauto.
  - destruct H, H. exists (inl x0). auto. exists (inr x0). auto.
Qed.


(* Empty set *)
Definition emptyset := enum (False_rect _).

Lemma emptyset_ok: forall x, ~ iin x emptyset.
Proof.
  red. unfold emptyset, enum. intro x. rewrite iin_unfold. unfold Ain, Xor.
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
Definition sin x := enum (fun _: unit => x).

Lemma sin_ok: forall x y, iin x (sin y) <-> eeq y x.
Proof.
  intros x y. unfold sin, enum. rewrite iin_unfold.
  unfold Xor, Ain. simpl. rewrite ex_unit. tauto.
Qed.

(* Exclusive or of sets *)

Local Definition boolean_xor {A} (p p': boolean A) :=
  Or _ (Not _ (Or _ p (Not _ p'))) (Not _ (Or _ (Not _ p) p')).

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
  Qin z (sum_funs h h0)
    (boolean_xor (boolean_map inl p) (boolean_map inr p0))
  <-> Xor (Qin z h p) (Qin z h0 p0).
Proof.
  unfold boolean_xor. simpl Qin.
  setoid_rewrite Qin_sum_inl. setoid_rewrite Qin_sum_inr.
  unfold Xor. tauto.
Qed.

Lemma xor_ok: forall x y z,
  iin z (QXor x y) <-> Xor (iin z x) (iin z y).
Proof.
  intros. destruct x, y. rewrite (xor_iff iin_unfold' iin_unfold').
  rewrite xor_pairs. unfold QXor. rewrite iin_unfold'. apply xor_iff.
  - apply AXor_ok.
  - apply QXor_ok.
Qed.
