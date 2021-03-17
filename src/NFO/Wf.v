(** * NFO.Wf : Well-founded orders *)
(** This module contain the well-founded orders and some auxiliary lemmas
    that are required by the [NFO] module. 
*)

From Coq.Program Require Import Tactics Equality.
Add LoadPath "src/Internal" as Internal.
From Internal Require Export WfTuples.
Add LoadPath "src/NFO" as NFO.
From NFO Require Import Model.

Section Unfold.
(** First, we prove [Fix_iff]. It is an unfolding lemma for fixpoint definitions;
    the only difference with respect to the existing [Fix_eq] is that here we use
    equivalence instead of equality, so to avoid using the axiom of extensionality.
*)

Variable A: Type.
Variable R: A -> A -> Prop.
Variable Rwf: well_founded R.
Variable F: forall x, (forall y, R y x -> Prop) -> Prop.
Variable F_ext:
  forall x (f g: forall y, R y x -> Prop),
    (forall y (p: R y x), f y p <-> g y p) -> F x f <-> F x g.

(** Variant of [Coq.Init.Wf.Fix_F_inv] using [iff] instead of [eq].
    Necessary to prove [Fix_iff] below.
*)
Lemma Fix_F_inv_iff x (r s: Acc R x):
  Fix_F (fun _ => Prop) F r <-> Fix_F (fun _ => Prop) F s.
Proof.
  intros. induction (Rwf x); intros.
  rewrite <- (Fix_F_eq _ F r); rewrite <- (Fix_F_eq _ F s); intros.
  apply F_ext; auto.
Qed.

(** Variant of [Coq.Init.Wf.Fix_eq]: *)
Lemma Fix_iff x:
  Fix Rwf (fun _ => Prop) F x <-> F x (fun y _ => Fix Rwf (fun _ => Prop) F y).
Proof.
  intros. unfold Fix. rewrite <- Fix_F_eq.
  apply F_ext; intros. apply Fix_F_inv_iff.
Qed.

End Unfold.

(** In the following sections, we define notations and resolving lemmas
    for our well-founded orders on 2-tuples and 3-tuples.

    The trivial lemmas are just named with sequences of letters, denoting
    which elements of the tuple decrease to which positions.
    These lemmas are registered in the [Wff] scope, so that obligations
    coming from fixpoint definitions can be solved automatically using
    [eauto with Wff].
*)
From Coq.Program Require Import Tactics Wf Equality.

Section One.

Inductive lt : SET -> SET -> Prop :=
  | lt_f : forall X Y f g e x, lt (f x) (S X Y f g e)
  | lt_h : forall X Y f g e y, lt (g y) (S X Y f g e)
.

Lemma wf_lt : well_founded lt.
Proof. 
  unfold well_founded.
  induction a.
  apply Acc_intro. intros.
  dependent destruction H1; eauto.
Defined.

End One.
#[export] Hint Constructors lt : Wff.

Section Two.
Infix "<" := lt.
Infix "<<" := (le22 lt) (at level 50).

Variables a a' b b': SET.

Ltac auto2 := unfold le22; unfold le12; tauto.
Lemma AA : a < a' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed.
Lemma AB : a < a' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed.
Lemma BA : a < b' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed.
Lemma BB : a < b' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed.

End Two.

#[export] Hint Resolve AA AB BA BB: Wff.

Section Three.
Infix "<" := lt.
Infix "<<<" := (le33 lt) (at level 50).

Variables a a' b b' c c': SET.

Ltac auto3 := unfold le33; unfold le13; tauto.
Lemma AAA : a < a' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAB : a < a' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAC : a < a' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABA : a < a' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABB : a < a' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABC : a < a' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACA : a < a' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACB : a < a' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACC : a < a' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAA : a < b' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAB : a < b' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAC : a < b' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBA : a < b' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBB : a < b' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBC : a < b' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCA : a < b' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCB : a < b' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCC : a < b' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAA : a < c' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAB : a < c' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAC : a < c' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBA : a < c' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBB : a < c' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBC : a < c' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCA : a < c' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCB : a < c' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCC : a < c' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

End Three.

#[export] Hint Resolve AAA AAB AAC ABA ABB ABC ACA ACB ACC BAA BAB BAC BBA BBB BBC BCA BCB BCC CAA CAB CAC CBA CBB CBC CCA CCB CCC : Wff.

Global Opaque le22 le33.
