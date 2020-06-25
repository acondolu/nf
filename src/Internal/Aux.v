Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

(* This module contains some auxiliary functions *)

Definition select {X Y} (f: X -> Y) (P: X -> Prop) : {x: X & P x} -> Y
  := fun x => f (projT1 x).

Lemma And_eq3 {a a' b b' c c'}:
  (a <-> a') -> (b <-> b') -> (c <-> c') -> (a /\ b /\ c) <-> (a' /\ b' /\ c').
Proof. tauto. Qed.

Lemma ex_false {P: False -> Prop}: (exists x, P x) <-> False.
Proof. split; intros. destruct H, x. destruct H. Qed.

Lemma ex_unit {P: unit -> Prop}: (exists x, P x) <-> P tt.
Proof. split; intros. destruct H, x. auto. eauto. Qed.

Lemma and_true: forall X, X /\ True <-> X.
Proof. intro. tauto. Qed.

(* Lemma compose_sum_inl {X Y Z} {f: X -> Z} {g: Y -> Z} :
  ext (compose (sum_funs f g) inl) f.
Proof. unfold ext. intros. apply eq_refl. Qed.
Hint Resolve compose_sum_inl : Bool.

Lemma compose_sum_inr {X Y Z} {f: X -> Z} {g: Y -> Z} :
  ext (compose (sum_funs f g) inr) g.
Proof. intro x. apply eq_refl. Qed.
Hint Resolve compose_sum_inr : Bool. *)

Definition swap {X Y} (x: X + Y) := match x with
  | inl a => inr a
  | inr b => inl b
end.

Lemma comp_swap_inl {X Y}: compose (@swap X Y) inl = inr.
Proof. auto. Qed.
Lemma comp_swap_inr {X Y}: compose (@swap X Y) inr = inl.
Proof. auto. Qed.

Definition sum_funs {X Y Z} f g : X + Y -> Z := fun s =>
  match s with
  | inl x => f x
  | inr y => g y
  end.

Definition invert_sum {X Y Z} P R S (z : Z) := 
  (exists x : X, P (inl x) /\ R x z)
  \/ exists y : Y, P (inr y) /\ S y z.

(* Inverts a  *)
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