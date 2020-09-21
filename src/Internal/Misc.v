(** * Internal.Misc : Auxiliary concepts and definitions *)
From Coq.Program Require Import Basics Combinators.

(** Some trivial equivalences: *)
Lemma rewr_true: forall {p: Prop}, p -> (p <-> True).
Proof. tauto. Qed.

Lemma rewr_false: forall {p: Prop}, ~p -> (p <-> False).
Proof. tauto. Qed.

Lemma rewr_not_true: ~True <-> False.
Proof. tauto. Qed.
Hint Rewrite rewr_not_true : log.

Lemma rewr_not_false: ~False <-> True.
Proof. tauto. Qed.
Hint Rewrite rewr_not_false : log.

Lemma ex_false {P: False -> Prop}: (exists x, P x) <-> False.
Proof. split; intros. destruct H, x. destruct H. Qed.

Lemma ex_unit {P: unit -> Prop}: (exists x, P x) <-> P tt.
Proof. split; intros. destruct H, x. auto. eauto. Qed.

Lemma ex_T {Y} (P Q: Y -> Prop):
  (exists x : {y : Y & P y}, Q (projT1 x)) <-> (exists x, P x /\ Q x).
Proof.
  split; intro H; destruct H. destruct x. eauto.
  destruct H. exists (existT _ x H). auto.
Qed.

(** 'select f P' restricts the domain of a function f according to a predicate P: *)
Definition select {X Y} (f: X -> Y) (P: X -> Prop) : {x: X & P x} -> Y
  := fun x => f (projT1 x).

(** Composition of a predicate with a function (on both its arguments): *)
Definition compR {X Y Z} (R: Y -> Y -> Z) (f: X -> Y) x x' := R (f x) (f x').
Infix "⨀" := compR (at level 79).

(** * Conjunction
  Trivial properties of conjunction: *)
Lemma and_morph {a a' b b'}:
  (a <-> a') -> (b <-> b') -> (a /\ b) <-> (a' /\ b').
Proof. tauto. Qed.

Lemma and_true: forall X, X /\ True <-> X.
Proof. intro. tauto. Qed.

(** * Sums *)

(** Swapping a sum: *)
Definition swap {X Y}: X + Y -> Y + X := 
  fun x => match x with
  | inl a => inr a
  | inr b => inl b
  end.

(** Composing swap with injections: *)
Lemma comp_swap_inl {X Y}: (@swap X Y) ∘ inl = inr.
Proof. auto. Qed.
Lemma comp_swap_inr {X Y}: (@swap X Y) ∘ inr = inl.
Proof. auto. Qed.

(** Sum of two functions: *)
Definition sumF {X Y Z} : (X -> Z) -> (Y -> Z) -> X + Y -> Z := fun f g s =>
  match s with
  | inl x => f x
  | inr y => g y
  end.
Infix "⨁" := sumF (at level 80, right associativity).

(** TODO: used only in transitivity proofs *)
Definition invert_sum {X Y Z} P R S (z : Z) := 
  (exists x : X, P (inl x) /\ R x z)
  \/ exists y : Y, P (inr y) /\ S y z.

(** Inverting function for orders TODO: *)
Definition invF {X Y} (f: X -> Y) (y: Y) := exists x, f x = y.

Definition inv3 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) w :=
  invF f w \/ invF g w \/ invF h w.

Lemma inv3_1 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) x:
  inv3 f g h (f x).
Proof. unfold inv3. unfold invF. left. exists x. auto. Qed.
Lemma inv3_2 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) y:
  inv3 f g h (g y).
Proof. unfold inv3. unfold invF. right. left. exists y. auto. Qed.
Lemma inv3_3 {X Y Z W} (f: X -> W) (g : Y -> W) (h : Z -> W) z:
  inv3 f g h (h z).
Proof. unfold inv3. unfold invF. right. right. exists z. auto. Qed.
Hint Resolve inv3_1 inv3_2 inv3_3: misc.