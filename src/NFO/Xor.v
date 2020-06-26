(* Warning! This module uses classical logic! *)
Require Import Coq.Logic.Classical_Prop.
Require Import Setoid Morphisms.

Add LoadPath "src".
From Internal Require Import FunExt.

(* Exclusive OR *)
Definition xor a b := (a /\ ~b) \/ (~a /\ b).
Infix "⊻" := xor (at level 80, right associativity).

(* Register xor as a morphism *)
Add Morphism xor: eeqs.
Proof. unfold xor. tauto. Qed.

(* A bunch of useful properties about xor *)

Lemma xor_assoc {a b c}: a ⊻ (b ⊻ c) <-> (a ⊻ b) ⊻ c.
Proof. unfold xor. tauto. Qed.

Lemma xor_absorb {a}: xor a a <-> False.
Proof. unfold xor. tauto. Qed.
Hint Resolve xor_absorb : xor.

Lemma xor_false_l {a}: xor False a <-> a.
Proof. unfold xor. tauto. Qed.
Hint Resolve xor_false_l : xor.

Lemma xor_false_r {a}: xor a False <-> a.
Proof. unfold xor. tauto. Qed.
Hint Resolve xor_false_l : xor.

Lemma xor_comm {a b}: a ⊻ b <-> b ⊻ a.
Proof. unfold xor. tauto. Qed.

Lemma xor_pairs {a b c d}: xor (xor a b) (xor c d) <-> xor (xor a c) (xor b d).
Proof. unfold xor. split; intro; destruct H; tauto. Qed.

Lemma xor_iff {a a' b b'}: (a <-> a') -> (b <-> b') -> xor a b <-> xor a' b'.
Proof. unfold xor. tauto. Qed.

Lemma xor_neg {a b}: (~xor a b) <-> (a <-> b).
Proof. unfold xor. split; tauto. Qed.

Lemma xor_1 {a b: Prop}: a -> (~b) -> xor a b.
Proof. unfold xor. tauto. Qed.

Lemma xor_2 {a b: Prop}: (~a) -> b -> xor a b.
Proof. unfold xor. tauto. Qed.

Lemma xor_neg_commute {a b}: a ⊻ (~ b) <-> ~ (a ⊻ b).
Proof. unfold xor. intros. tauto. Qed.

(* Exclusive disjunction of predicates *)
Definition xorP {X} (P Q: X -> Prop) := fun x => xor (P x) (Q x).

Lemma xorP_respects {X} (R: X -> X -> Prop) (P Q: X -> Prop) :
  respects R P
  -> respects R Q
  -> respects R (xorP P Q).
Proof.
  unfold respects. intros. unfold xorP. apply xor_iff.
  apply H; auto. apply H0; auto.
Qed.
