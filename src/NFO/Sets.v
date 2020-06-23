From Coq.Program Require Import Basics Combinators.

Add LoadPath "src/NFO/".
Require Import Xor Aux FunExt.
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Iin.

(* Axuliary *)
Definition enum {X} f := S False (Bot _) (False_rect _) X f.

Lemma Ain_sum {X Y} (f: X + Y -> set) x:
  Ain x f <-> Ain x (compose f inl) \/ Ain x (compose f inr).
Proof.
  unfold Ain, compose. split; intros.
  - destruct H, x0. left. eauto. right. eauto.
  - destruct H, H; eauto.
Qed.

Lemma Ain_sums {X X'} {f: X -> set} {f': X' -> set} {x}:
  Ain x (sum_funs f f') <-> (Ain x f) \/ (Ain x f').
Proof.
  setoid_rewrite Ain_sum. unfold compose, sum_funs. tauto.
Qed.

Lemma Ain_sigma {X} (f: X -> set) (P: set -> Prop) a:
  respects eeq P ->
  Ain a
    (fun x : {x & P (f x)} => f (projT1 x))
  <-> P a /\ exists x, f x == a.
Proof.
  unfold Ain. split; intros. destruct H0, x. simpl in *.
  split. rewrite<- (H _ _ H0). auto. eauto.
  destruct H0, H1. rewrite<- (H _ _ H1) in H0.
  exists (existT _ x H0). auto.
Qed.

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

(* Empty set *)
Definition emptyset := enum (False_rect _).

Lemma emptyset_ok: forall x, ~ iin x emptyset.
Proof.
  unfold emptyset, enum. intro x. rewrite iin_unfold.
  unfold Ain, Xor. setoid_rewrite ex_false. tauto.
Qed.

(* Set complement *)
Definition compl x := match x with
  S A p h X f => S A (Not _ p) h X f
end.

Lemma compl_ok: forall x y,
  iin x (compl y) <-> (iin x y -> False).
Proof.
  intros. destruct y. unfold compl. repeat rewrite iin_unfold'.
  simpl Qin. setoid_rewrite xor_neg_commute. tauto.
Qed.

(* Co-singleton *)
Definition cosin x := S unit (Atom _ tt) (fun _ => x) False (False_rect _).

Lemma cosin_ok: forall x y, iin x (cosin y) <-> iin y x.
Proof.
  intros. unfold cosin. rewrite iin_unfold'.
  setoid_rewrite ex_false. simpl Qin. apply xor_false_l.
Qed.

(* Singleton *)
Definition sin x := enum (fun _: unit => x).

Lemma sin_ok: forall x y, iin x (sin y) <-> eeq y x.
Proof.
  intros x y. unfold sin, enum. rewrite iin_unfold'.
  simpl Qin. unfold Ain. setoid_rewrite ex_unit.
  apply xor_false_r.
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
  Ain x (AXor f f') <-> Ain x f <X> Ain x f'.
Proof.
  unfold AXor. setoid_rewrite Ain_sum. unfold compose; simpl.
  setoid_rewrite (Ain_sigma f (fun X => ~ exists y, f' y == X)).
  setoid_rewrite (Ain_sigma f' (fun X => ~ exists x, f x == X)).
  unfold Xor, Ain. tauto.
  unfold respects. intros. setoid_rewrite H. tauto.
  unfold respects. intros. setoid_rewrite H. tauto.
Qed.

Lemma QXor_ok {X Y} {f: X -> set} {g: Y -> set} {z p q}:
  Qin z (sum_funs f g)
    (boolean_xor (boolean_map inl p) (boolean_map inr q))
  <-> Xor (Qin z f p) (Qin z g q).
Proof.
  unfold boolean_xor. simpl Qin.
  setoid_rewrite Qin_sum_inl. setoid_rewrite Qin_sum_inr.
  unfold Xor. tauto.
Qed.

Lemma xor_ok: forall x y z,
  iin z (QXor x y) <-> Xor (iin z x) (iin z y).
Proof.
  intros. destruct x, y. unfold QXor. setoid_rewrite iin_unfold'.
  setoid_rewrite AXor_ok. setoid_rewrite QXor_ok.
  rewrite xor_pairs. tauto.
Qed.