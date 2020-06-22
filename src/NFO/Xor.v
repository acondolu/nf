(* Warning! This module uses classical logic! *)
Require Import Coq.Logic.Classical_Prop.
Require Import Setoid Morphisms.

Add LoadPath "src/NFO/".
Require Import FunExt.

(* Exclusive OR *)
Definition Xor a b := (a /\ ~b) \/ (~a /\ b).
Infix "<X>" := Xor (at level 80, right associativity).

(* Register Xor as a morphism *)
Add Morphism Xor: eeqs.
Proof. unfold Xor. tauto. Qed.

(* A bunch of useful properties about Xor *)

Lemma xor_assoc {a b c}: a <X> (b <X> c) <-> (a <X> b) <X> c.
Proof. unfold Xor. tauto. Qed.

Lemma xor_absorb {a}: Xor a a <-> False.
Proof. unfold Xor. tauto. Qed.
Hint Resolve xor_absorb : Xor.

Lemma xor_false_l {a}: Xor False a <-> a.
Proof. unfold Xor. tauto. Qed.
Hint Resolve xor_false_l : Xor.

Lemma xor_false_r {a}: Xor a False <-> a.
Proof. unfold Xor. tauto. Qed.
Hint Resolve xor_false_l : Xor.

Lemma xor_comm {a b}: a <X> b <-> b <X> a.
Proof. unfold Xor. tauto. Qed.

Lemma xor_pairs {a b c d}: Xor (Xor a b) (Xor c d) <-> Xor (Xor a c) (Xor b d).
Proof. unfold Xor. split; intro; destruct H; tauto. Qed.

Lemma xor_iff {a a' b b'}: (a <-> a') -> (b <-> b') -> Xor a b <-> Xor a' b'.
Proof. unfold Xor. tauto. Qed.

Lemma Xor_neg {a b}: (~Xor a b) <-> (a <-> b).
Proof. unfold Xor. split; tauto. Qed.

Lemma Xor_1 {a b: Prop}: a -> (~b) -> Xor a b.
Proof. unfold Xor. tauto. Qed.

Lemma Xor_2 {a b: Prop}: (~a) -> b -> Xor a b.
Proof. unfold Xor. tauto. Qed.

Lemma xor_neg_commute {a b}: a <X> (~ b) <-> ~ (a <X> b).
Proof. unfold Xor. intros. tauto. Qed.

(* Exclusive disjunction of predicates *)
Definition xorP {X} (P Q: X -> Prop) := fun x => Xor (P x) (Q x).

Lemma xorP_respects {X} (R: X -> X -> Prop) (P Q: X -> Prop) :
  respects R P
  -> respects R Q
  -> respects R (xorP P Q).
Proof.
  unfold respects. intros. unfold xorP. apply xor_iff.
  apply H; auto. apply H0; auto.
Qed.
