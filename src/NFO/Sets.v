(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Add LoadPath "src".
From Internal Require Import Aux FunExt.
From NFO Require Import Xor BoolExpr Model Eeq Iin.
(* end hide *)

(* Axuliary *)
Definition enum {X} f := S X False f (False_rect _) Bot.

Lemma Ain_sum {X Y} (f: X + Y -> set) x:
  Ain x f <-> Ain x (compose f inl) \/ Ain x (compose f inr).
Proof.
  unfold Ain, compose. split; intros.
  - destruct H, x0. left. eauto. right. eauto.
  - destruct H, H; eauto.
Qed.

Lemma Ain_sums {X X'} {f: X -> set} {f': X' -> set} {x}:
  Ain x (f ⨁ f') <-> (Ain x f) \/ (Ain x f').
Proof.
  setoid_rewrite Ain_sum. unfold compose, sumF. tauto.
Qed.

Lemma Ain_select {X} (f: X -> set) (P: set -> Prop) a:
  respects eeq P ->
    Ain a (select f (P ∘ f)) <-> P a /\ exists x, f x == a.
Proof.
  unfold Ain. intro H. setoid_rewrite (ex_T_resp P f a H). apply iff_refl.
Qed.

Lemma Qin_sum_inl: forall X Y z (f: X -> set) (g: Y -> set) p,
  Qin z (f ⨁ g) (map inl p) <-> Qin z f p.
Proof.
  induction p; simpl.
  - tauto.
  - tauto.
  - setoid_rewrite IHp. tauto.
  - setoid_rewrite IHp1. setoid_rewrite IHp2. tauto.
Qed.

Lemma Qin_sum_inr: forall X Y z (f: X -> set) (g: Y -> set) p,
  Qin z (f ⨁ g) (map inr p) <-> Qin z g p.
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
  unfold Ain, xor. setoid_rewrite ex_false. tauto.
Qed.

(* Set complement *)
Definition compl x := match x with
  S X Y f g e => S X Y f g (Not e)
end.

Lemma compl_ok: forall x y,
  iin x (compl y) <-> (iin x y -> False).
Proof.
  intros. destruct y. unfold compl. repeat rewrite iin_unfold.
  simpl Qin. setoid_rewrite xor_neg_commute. tauto.
Qed.

(* Co-singleton *)
Definition cosin x := S False unit (False_rect _) (fun _ => x) (Atom tt).

Lemma cosin_ok: forall x y, iin x (cosin y) <-> iin y x.
Proof.
  intros. unfold cosin. rewrite iin_unfold.
  setoid_rewrite ex_false. simpl Qin. apply xor_false_l.
Qed.

(* Singleton *)
Definition sin x := enum (fun _: unit => x).

Lemma sin_ok: forall x y, iin x (sin y) <-> eeq y x.
Proof.
  intros x y. unfold sin, enum. rewrite iin_unfold.
  simpl Qin. unfold Ain. setoid_rewrite ex_unit.
  apply xor_false_r.
Qed.

(* Exclusive or of sets *)

Definition AXor {X Y} (f: X -> set) (g: Y -> set)
  : sum {x & ~ exists y, eeq (g y) (f x)} {y & ~ exists x, eeq (f x) (g y)} -> set
  := fun s => match s with
      | inl x => f (projT1 x)
      | inr y => g (projT1 y) 
    end.

Local Definition boolean_xor {A} (p p': @boolean A) :=
  Or (Not (Or p (Not p'))) (Not (Or (Not p) p')).

(** Rename! *)
Definition QXor B C := 
  match B, C with S X Y f g e, S X' Y' f' g' e' =>
    let e'' := boolean_xor (map inl e) (map inr e') in
    S _ (sum Y Y') (AXor f f') (g ⨁ g') e''
  end.

Lemma AXor_ok {X X'} {f: X -> set} {f': X' -> set} {x}:
  Ain x (AXor f f') <-> Ain x f ⊻ Ain x f'.
Proof.
  unfold AXor. setoid_rewrite Ain_sum. unfold compose; simpl.
  setoid_rewrite (Ain_select f (fun X => ~ exists y, f' y == X)).
  setoid_rewrite (Ain_select f' (fun X => ~ exists x, f x == X)).
  unfold xor, Ain. tauto.
  unfold respects. intros. setoid_rewrite H. tauto.
  unfold respects. intros. setoid_rewrite H. tauto.
Qed.

Lemma QXor_ok {X Y} {f: X -> set} {g: Y -> set} {z p q}:
  Qin z (f ⨁ g)
    (boolean_xor (map inl p) (map inr q))
  <-> Qin z f p ⊻ Qin z g q.
Proof.
  unfold boolean_xor. simpl Qin.
  setoid_rewrite Qin_sum_inl. setoid_rewrite Qin_sum_inr.
  unfold xor. tauto.
Qed.

Lemma xor_ok: forall x y z,
  iin z (QXor x y) <-> iin z x ⊻ iin z y.
Proof.
  intros. destruct x, y. unfold QXor. setoid_rewrite iin_unfold.
  setoid_rewrite AXor_ok. setoid_rewrite QXor_ok.
  rewrite xor_pairs. tauto.
Qed.
