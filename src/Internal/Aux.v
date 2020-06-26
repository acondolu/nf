From Coq.Program Require Import Basics Combinators.

(** * Auxiliary Aux

  This module contains various auxiliary definitions.
*)

(** 'select' restricts the domain of a function according to a predicate: *)
Definition select {X Y} (f: X -> Y) (P: X -> Prop) : {x: X & P x} -> Y
  := fun x => f (projT1 x).

(** A couple of trivial equivalences: *)
Lemma rewr_true: forall {p: Prop}, p -> (p <-> True).
Proof. tauto. Qed.

Lemma rewr_false: forall {p: Prop}, ~p -> (p <-> False).
Proof. tauto. Qed.

Lemma ex_false {P: False -> Prop}: (exists x, P x) <-> False.
Proof. split; intros. destruct H, x. destruct H. Qed.

Lemma ex_unit {P: unit -> Prop}: (exists x, P x) <-> P tt.
Proof. split; intros. destruct H, x. auto. eauto. Qed.

(** Trivial properties of conjunction: *)
Lemma and_morph {a a' b b'}:
  (a <-> a') -> (b <-> b') -> (a /\ b) <-> (a' /\ b').
Proof. tauto. Qed.

Lemma and_true: forall X, X /\ True <-> X.
Proof. intro. tauto. Qed.

(* ** Swapping a sum: *)
Definition swap {X Y} (x: X + Y) := match x with
  | inl a => inr a
  | inr b => inl b
end.

Lemma comp_swap_inl {X Y}: (@swap X Y) ∘ inl = inr.
Proof. auto. Qed.
Lemma comp_swap_inr {X Y}: (@swap X Y) ∘ inr = inl.
Proof. auto. Qed.

(* ** Sum of two functions: *)
Definition sumF {X Y Z} f g : X + Y -> Z := fun s =>
  match s with
  | inl x => f x
  | inr y => g y
  end.
Infix "⨁" := sumF (at level 80, right associativity).

Definition invert_sum {X Y Z} P R S (z : Z) := 
  (exists x : X, P (inl x) /\ R x z)
  \/ exists y : Y, P (inr y) /\ S y z.

Definition compR {X Y Z} (R: Y -> Y -> Z) (f: X -> Y) x x' := R (f x) (f x').
Infix "⨀" := compR (at level 79).


Lemma ex_T {Y} (P Q: Y -> Prop):
  (exists x : {y : Y & P y}, Q (projT1 x)) <-> (exists x, P x /\ Q x).
Proof.
  split; intro H; destruct H. destruct x. eauto.
  destruct H. exists (existT _ x H). auto.
Qed.

From Coq.Logic Require Import Classical_Prop.
Ltac classic P := 
destruct (classic P) as [H | H];
[setoid_rewrite (rewr_true H) | setoid_rewrite (rewr_false H)]; clear H.

(* ** Inverting function for orders TODO *)
Definition invF {X Y} (f: X -> Y) (y: Y) := exists x, f x = y.

Definition inv2 {X Y W} (f: X -> W) (g : Y -> W) w :=
  invF f w \/ invF g w.

Definition inv3 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) w :=
  invF f w \/ invF g w \/ invF h w.

Lemma inv2_1 {X Y W} (f: X -> W) (g : Y -> W) x:
  inv2 f g (f x).
Proof. unfold inv2. unfold invF. left. exists x. auto. Qed.
Lemma inv2_2 {X Y W} (f: X -> W) (g : Y -> W) y:
  inv2 f g (g y).
Proof. unfold inv2. unfold invF. right. exists y. auto. Qed.
Hint Resolve inv2_1. Hint Resolve inv2_2.

Lemma inv3_1 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) x:
  inv3 f g h (f x).
Proof. unfold inv3. unfold invF. left. exists x. auto. Qed.
Lemma inv3_2 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) y:
  inv3 f g h (g y).
Proof. unfold inv3. unfold invF. right. left. exists y. auto. Qed.
Lemma inv3_3 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) z:
  inv3 f g h (h z).
Proof. unfold inv3. unfold invF. right. right. exists z. auto. Qed.
Hint Resolve inv3_1. Hint Resolve inv3_2. Hint Resolve inv3_3.