(* Warning! This module uses classical logic! *)
Require Import Coq.Logic.Classical_Prop.
Require Import Setoid Morphisms.

(* begin hide *)
Add LoadPath "src".
From Internal Require Import FunExt.
(* end hide *)

(** This module defines exclusive disjunction (xor), noted
    by ⊻. Note: xor is a fundamentally classical operator, and
    in fact from now on we freely use classical logic.  *)

Definition xor p q := (p /\ ~q) \/ (~p /\ q).
Infix "⊻" := xor (at level 80, right associativity).

(** A bunch of trivial but useful properties about xor follow. *)

(** Self-inverse: *)
Lemma xor_absorb : forall p, p ⊻ p <-> False.
Proof. unfold xor. tauto. Qed.
Hint Resolve xor_absorb : xor.

(** Commutativity: *)
Lemma xor_comm: forall p q, p ⊻ q <-> q ⊻ p.
Proof. unfold xor. tauto. Qed.

(** Associativity: *)
Lemma xor_assoc: forall p q r, p ⊻ (q ⊻ r) <-> (p ⊻ q) ⊻ r.
Proof. intros. unfold xor. tauto. Qed.

(** Left and right identity: *)
Lemma xor_false_l: forall p, False ⊻ p <-> p.
Proof. unfold xor. tauto. Qed.
Hint Resolve xor_false_l : xor.

Lemma xor_false_r: forall p, p ⊻ False <-> p.
Proof. unfold xor. tauto. Qed.
Hint Resolve xor_false_l : xor.

(** xor is a morphism: *)
Lemma xor_iff: forall p p' q q', (p <-> p') -> (q <-> q') -> p ⊻ q <-> p' ⊻ q'.
Proof. unfold xor. tauto. Qed.
Add Morphism xor: eeqs.
Proof. unfold xor. tauto. Qed.

(** Negation of xor: *)
Lemma xor_neg: forall p q, ~ (p ⊻ q) <-> (p <-> q).
Proof. unfold xor. split; tauto. Qed.

(** Projections: *)
Lemma xor_1: forall p q: Prop, p -> ~q -> p ⊻ q.
Proof. unfold xor. tauto. Qed.

Lemma xor_2: forall p q: Prop, ~p -> q -> p ⊻ q.
Proof. unfold xor. tauto. Qed.

(** Xor commutes with negation: *)
Lemma xor_neg_commute: forall p q, p ⊻ ~q <-> ~(p ⊻ q).
Proof. unfold xor. intros. tauto. Qed.

(** A technical lemma that interleaves the operands: *)
Lemma xor_pairs: forall p q r s, (p ⊻ q) ⊻ (r ⊻ s) <-> (p ⊻ r) ⊻ (q ⊻ s).
Proof. unfold xor. split; intro; destruct H; tauto. Qed.

(** Exclusive disjunction of predicates: *)
Definition xorP {X} (P Q: X -> Prop) := fun x => P x ⊻ Q x.
Infix "^^" := xorP (at level 80, right associativity).

(** If P and Q are R-morphisms, then P ^^ Q is an R-morphism as well: *)
Lemma xorP_respects {X} (R: X -> X -> Prop) (P Q: X -> Prop) :
  respects R P -> respects R Q -> respects R (P ^^ Q).
Proof.
  unfold respects. intros. unfold xorP. apply xor_iff.
  apply H; auto. apply H0; auto.
Qed.
