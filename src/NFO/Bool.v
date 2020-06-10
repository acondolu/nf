Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.


(* A boolean expression with atoms of type X *)
Inductive boolean X :=
  | Bot : boolean X
  | Atom : X -> boolean X
  | Not : boolean X -> boolean X
  | Or : boolean X -> boolean X -> boolean X
.

(* Evaluate a closed boolean formula to a Prop *)
Fixpoint eval (p: boolean Prop) := match p with
  | Atom _ a => a
  | Bot _ => False
  | Not _ p => eval p -> False
  | Or _ p1 p2 => eval p1 \/ eval p2
end.

(* Maps the atoms in a boolean expression *)
Fixpoint boolean_map {X Y} (f: X -> Y) (p: boolean X) : boolean Y :=
match p with
  | Atom _ a => Atom _ (f a)
  | Bot _ => Bot _
  | Not _ p => Not _ (boolean_map f p)
  | Or _ p1 p2 => Or _ (boolean_map f p1) (boolean_map f p2)
end.

Lemma boolean_map_compose {X Y Z f g p}:
  boolean_map f (boolean_map g p) = boolean_map (@compose X Y Z f g) p.
Proof.
  induction p; simpl; auto.
  - rewrite IHp. auto.
  - rewrite IHp1. rewrite IHp2. auto.
Qed.

(* EEQ PROP *)

Definition respects {X} (f: X -> Prop) (P: X -> X -> Prop) :=
  forall x x', P x x' -> (f x <-> f x').

Definition eeq_boolean {X} (p1 p2: boolean X) P : Prop :=
  forall f, respects f P ->
    eval (boolean_map f p1) <-> eval (boolean_map f p2).

(* SUM_I *)

Definition sum_i {X Y Z} (R: Z -> Z -> Prop) h h' (i j: X + Y) := 
match i, j with
  | inl i', inl j' => R (h i') (h j')
  | inl i', inr j' => R (h i') (h' j')
  | inr i', inl j' => R (h' i') (h j')
  | inr i', inr j' => R (h' i') (h' j')
end.

(* REFLEXIVITY *)

Lemma eeq_boolean_refl : forall {X Y} (p: boolean X) (f: Y -> Y -> Prop) (h: X -> Y), (forall x, f (h x) (h x)) -> eeq_boolean (boolean_map inl p) (boolean_map inr p) (sum_i f h h).
Proof.
  unfold eeq_boolean. intros.
  induction p; simpl.
  - tauto.
  - apply H0. apply H.
  - tauto.
  - tauto.
Qed.

(* SYMMETRY *)

Definition swap {X Y} (x: X + Y) := match x with
  | inl a => inr a
  | inr b => inl b
end.

Lemma comp_swap_inl {X Y}: compose (@swap X Y) inl = inr.
Proof. auto. Qed.
Lemma comp_swap_inr {X Y}: compose (@swap X Y) inr = inl.
Proof. auto. Qed.

Lemma sum_i_sym: forall {X Y Z P h h' x x'},
  sum_i P h h' x x' -> @sum_i X Y Z P h' h (swap x) (swap x').
Proof.
  unfold sum_i.
  intros. destruct x; destruct x'; assumption.
Qed.

Lemma respects_swap: forall {X Y Z P} {h: X -> Z} {h0: Y -> Z} g, respects g (sum_i P h0 h) -> respects (compose g swap) (sum_i P h h0).
Proof.
  unfold respects.
  intros. destruct x; destruct x'; unfold compose; simpl; apply H; apply (sum_i_sym H0).
Qed.

Lemma eeq_boolean_sym : forall {X Y Z p p0 h h0 P},
eeq_boolean (boolean_map inl p) (boolean_map inr p0) (@sum_i X Y Z P h h0)
-> 
eeq_boolean (boolean_map inl p0) (boolean_map inr p) (sum_i P h0 h).
Proof.
  intros. unfold eeq_boolean in *. intros.
  pose proof (H (compose f swap)).
  repeat rewrite boolean_map_compose in H1.
  repeat rewrite compose_assoc in H1.
  rewrite comp_swap_inl in H1.
  rewrite comp_swap_inr in H1.
  repeat rewrite<- compose_assoc in H1.
  repeat rewrite<- boolean_map_compose in H1.
  apply (fun X => iff_sym (H1 X)).
  apply respects_swap. assumption.
Qed.

(* TRANSITIVITY *)

Definition extends {X} (f g: X -> X -> Prop) :=
  forall x y, f x y -> g x y.

Lemma respects_extends : forall {X g h h'}, @extends X h h' -> respects g h' -> respects g h.
Proof.
  unfold respects. unfold extends.
  intros. apply H0. apply H. assumption.
Qed.

Lemma eeq_boolean_extends {X} {p1 p2: boolean X} {h h'} :
  extends h h' -> eeq_boolean p1 p2 h -> eeq_boolean p1 p2 h'.
Proof.
  unfold eeq_boolean. intros.
  pose proof (respects_extends H H1).
  apply (H0 _ H2).
Qed.

(* Lemma eeq_boolean_trans : forall {X1 X2 X3} (p1 p2 p3: boolean X) eqX, eeq_boolean p1 p2 eqX -> eeq_boolean p2 p3 eqX' -> 
Proof.
  unfold eeq_boolean. intros. rewrite (H g H0). trivial.
Qed. *)

Lemma eeq_boolean_trans {X Y Z W} {p: boolean X} {p': boolean Y} {p'': boolean Z} {h h' h''} {P: W -> W -> Prop}:
eeq_boolean (boolean_map inl p) (boolean_map inr p') (sum_i P h h')
-> eeq_boolean (boolean_map inl p') (boolean_map inr p'') (sum_i P h' h'')
-> eeq_boolean (boolean_map inl p) (boolean_map inr p'') (sum_i P h h'').
Proof.
  unfold eeq_boolean.
  intros.
Admitted.
