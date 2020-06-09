Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

(* A boolean expression with atoms of type X *)
Inductive prop X :=
  | Bot : prop X
  | Atom : X -> prop X
  | Or : prop X -> prop X -> prop X
  | And : prop X -> prop X -> prop X
  | Not : prop X -> prop X
.

(* Evaluate a closed boolean formula to a boolean *)
Fixpoint eval (p: prop bool) := match p with
  | Atom _ a => a
  | Bot _ => false
  | Not _ p => negb (eval p)
  | And _ p1 p2 => andb (eval p1) (eval p2)
  | Or _ p1 p2 => orb (eval p1) (eval p2)
end.

(* Maps the atoms in a boolean expression *)
Fixpoint prop_map {X Y} (f: X -> Y) (p: prop X) : prop Y :=
match p with
  | Atom _ a => Atom _ (f a)
  | Bot _ => Bot _
  | Not _ p => Not _ (prop_map f p)
  | And _ p1 p2 => And _ (prop_map f p1) (prop_map f p2)
  | Or _ p1 p2 => Or _ (prop_map f p1) (prop_map f p2)
end.

Lemma prop_map_compose {X Y Z f g p}:
  prop_map f (prop_map g p) = prop_map (@compose X Y Z f g) p.
Proof.
  induction p; simpl; auto.
  - rewrite IHp1. rewrite IHp2. auto.
  - rewrite IHp1. rewrite IHp2. auto.
  - rewrite IHp. auto.
Qed.

(* EEQ PROP *)

Definition respects {X Y} (f: X -> Y) (P: X -> X -> Prop) :=
  forall x x', P x x' -> f x = f x'.

Definition eeq_prop {X} (p1 p2: prop X) P : Prop :=
  forall f, respects f P ->
    eval (prop_map f p1) = eval (prop_map f p2).

(* SUM_I *)

Definition sum_i {X Y Z} (R: Z -> Z -> Prop) h h' (i j: X + Y) := 
match i, j with
  | inl i', inl j' => R (h i') (h j')
  | inl i', inr j' => R (h i') (h' j')
  | inr i', inl j' => R (h' i') (h j')
  | inr i', inr j' => R (h' i') (h' j')
end.

(* REFLEXIVITY *)

Lemma eeq_prop_refl : forall {X Y} (p: prop X) (f: Y -> Y -> Prop) (h: X -> Y), (forall x, f (h x) (h x)) -> eeq_prop (prop_map inl p) (prop_map inr p) (sum_i f h h).
Proof.
  unfold eeq_prop. intros.
  induction p; simpl.
  - trivial.
  - apply H0. apply H.
  - rewrite IHp1. rewrite IHp2. auto.
  - rewrite IHp1. rewrite IHp2. auto.
  - rewrite IHp. auto.
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

Lemma respects_swap: forall {X Y Z W P} {h: X -> Z} {h0: Y -> Z} {g: _ -> W}, respects g (sum_i P h0 h) -> respects (compose g swap) (sum_i P h h0).
Proof.
  unfold respects.
  intros. destruct x; destruct x'; unfold compose; simpl; apply H; apply (sum_i_sym H0).
Qed.

Lemma eeq_prop_sym : forall {X Y Z p p0 h h0 P},
eeq_prop (prop_map inl p) (prop_map inr p0) (@sum_i X Y Z P h h0)
-> 
eeq_prop (prop_map inl p0) (prop_map inr p) (sum_i P h0 h).
Proof.
  intros. unfold eeq_prop in *. intros.
  pose proof (H (compose f swap)).
  repeat rewrite prop_map_compose in H1.
  repeat rewrite compose_assoc in H1.
  rewrite comp_swap_inl in H1.
  rewrite comp_swap_inr in H1.
  repeat rewrite<- compose_assoc in H1.
  repeat rewrite<- prop_map_compose in H1.
  apply (fun X => eq_sym (H1 X)).
  apply respects_swap. assumption.
Qed.

(* TRANSITIVITY *)

Definition extends {X} (f g: X -> X -> Prop) :=
  forall x y, f x y -> g x y.

Lemma respects_extends : forall {X Y g h h'}, @extends X h h' -> respects g h' -> @respects X Y g h.
Proof.
  unfold respects. unfold extends.
  intros. apply H0. apply H. assumption.
Qed.

Lemma eeq_prop_extends {X} {p1 p2: prop X} {h h'} :
  extends h h' -> eeq_prop p1 p2 h -> eeq_prop p1 p2 h'.
Proof.
  unfold eeq_prop. intros.
  pose proof (respects_extends H H1).
  apply (H0 _ H2).
Qed.

(* Lemma eeq_prop_trans : forall {X1 X2 X3} (p1 p2 p3: prop X) eqX, eeq_prop p1 p2 eqX -> eeq_prop p2 p3 eqX' -> 
Proof.
  unfold eeq_prop. intros. rewrite (H g H0). trivial.
Qed. *)

Lemma eeq_prop_trans {X Y Z W} {p: prop X} {p': prop Y} {p'': prop Z} {h h' h''} {P: W -> W -> Prop}:
eeq_prop (prop_map inl p) (prop_map inr p') (sum_i P h h')
-> eeq_prop (prop_map inl p') (prop_map inr p'') (sum_i P h' h'')
-> eeq_prop (prop_map inl p) (prop_map inr p'') (sum_i P h h'').
Proof.
  unfold eeq_prop.
  intros.
Admitted.
