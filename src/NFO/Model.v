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

Definition respects {X Y} (f: X -> Y) (h: X -> X -> Prop) :=
  forall x y, h x y -> f x = f y.

Definition eeq_prop {X} (p1 p2: prop X) eqX : Prop :=
  forall g, respects g eqX -> eval (prop_map g p1) = eval (prop_map g p2)
.

Definition sum_i {X Y Z} (R: Z -> Z -> Prop) h h' (i j: X + Y) := 
match i, j with
  | inl i', inl j' => R (h i') (h j')
  | inl i', inr j' => R (h i') (h' j')
  | inr i', inl j' => R (h' i') (h j')
  | inr i', inr j' => R (h' i') (h' j')
end.

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

Definition swap {X Y} (x: X + Y) := match x with
  | inl a => inr a
  | inr b => inl b
end.

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

Lemma comp_swap_inl {X Y}: compose (@swap X Y) inl = inr.
Proof. auto. Qed.
Lemma comp_swap_inr {X Y}: compose (@swap X Y) inr = inl.
Proof. auto. Qed.

Lemma prop_map_compose {X Y Z f g p}:
  prop_map f (prop_map g p) = prop_map (@compose X Y Z f g) p.
Proof.
  induction p; simpl; auto.
  - rewrite IHp1. rewrite IHp2. auto.
  - rewrite IHp1. rewrite IHp2. auto.
  - rewrite IHp. auto. 
Qed.

Lemma sum_i_sym: forall {X Y Z P h h' x x'},
  sum_i P h h' x x' -> @sum_i X Y Z P h' h (swap x) (swap x').
Proof.
  unfold sum_i.
  intros. destruct x; destruct x'; assumption.
Qed.

Lemma respects_swap: forall {X Y Z W P} {h: X -> Z} {h0: Y -> Z} {g: _ -> W}, respects g (sum_i P h0 h) -> respects (compose g swap) (sum_i P h h0).
Proof.
  unfold respects.
  intros. destruct x; destruct y; unfold compose; simpl; apply H; apply (sum_i_sym H0).
Qed.



Lemma eeq_prop_sym : forall {X Y Z p p0 h h0 P},
eeq_prop (prop_map inl p) (prop_map inr p0) (@sum_i X Y Z P h h0)
-> 
eeq_prop (prop_map inl p0) (prop_map inr p) (sum_i P h0 h).
Proof.
  intros. unfold eeq_prop in *. intros.
  pose proof (H (compose g swap)).
  repeat rewrite prop_map_compose in H1.
  repeat rewrite compose_assoc in H1.
  rewrite comp_swap_inl in H1.
  rewrite comp_swap_inr in H1.
  repeat rewrite<- compose_assoc in H1.
  repeat rewrite<- prop_map_compose in H1.
  apply (fun X => eq_sym (H1 X)).
  apply respects_swap. assumption.
Qed.

Lemma eeq_prop_trans {X Y Z W} {p: prop X} {p': prop Y} {p'': prop Z} {h h' h''} {P: W -> W -> Prop}:
eeq_prop (prop_map inl p) (prop_map inr p') (sum_i P h h')
-> eeq_prop (prop_map inl p') (prop_map inr p'') (sum_i P h' h'')
-> eeq_prop (prop_map inl p) (prop_map inr p'') (sum_i P h h'').
Proof.
  unfold eeq_prop.
  intros.

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

Inductive set :=
  | C : forall A (p : prop A) (h: A -> set) X (f: X -> set), set
.

Definition emptyset := C False (Bot _) (fun x => match x with end) False (fun x => match x with end).

Definition compl x := match x with
  | C A p h X f => C A (Not _ p) h X f
  end.

Require Import Coq.Program.Tactics .
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.

Add LoadPath "src/NFO/".
Require Wff.
Inductive le_set : set -> set -> Prop :=
  | Ff : forall A p h X f i, le_set (f i) (C A p h X f)
  | Hh : forall A p h X f i, le_set (h i) (C A p h X f)
.
Lemma wf_le_set : well_founded le_set.
Proof.
  unfold well_founded.
  induction a.
  apply Acc_intro. intros.
  dependent destruction H1.
  apply H0. apply H.
Qed.

Inductive le_two : (set * set) -> (set * set) -> Prop :=
  | Aa : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
  | Bb : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | Bb' : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | Bb'' : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
.

Axiom wf_two: well_founded le_two.

Program Fixpoint eeq' x { wf le_two x } := match x with
  | (C A p h X f, C A' p' h' X' f') =>
          (forall x, exists y, eeq' (f x, f' y))
          /\ (forall y, exists x, eeq' (f x, f' y))
          /\ let w (i j: A + A') := match i, j with
            | inl i', inl j' => eeq' (h i', h j')
            | inl i', inr j' => eeq' (h i', h' j')
            | inr i', inl j' => eeq' (h' i', h j')
            | inr i', inr j' => eeq' (h' i', h' j')
            end in 
            eeq_prop (prop_map inl p) (prop_map inr p') w
end.
Next Obligation. apply Aa; apply Ff. Qed.
Next Obligation. apply Aa; apply Ff. Qed.
Next Obligation. apply Bb'; apply Hh. Qed.
Next Obligation. apply Aa; apply Hh. Qed.
Next Obligation. apply Bb; apply Hh. Qed.
Next Obligation. apply Bb''; apply Hh. Qed.
Next Obligation. apply wf_two. Qed.

Definition eeq x y := eeq' (x, y).

Axiom eeq_def : forall x y, eeq x y = match x, y with
| C A p h X f, C A' p' h' X' f' =>
        (forall x, exists y, eeq (f x) (f' y))
        /\ (forall y, exists x, eeq (f x) (f' y))
        /\  
          eeq_prop (prop_map inl p) (prop_map inr p') (sum_i eeq h h')
end.

Lemma eeq_refl : forall x, eeq x x.
Proof.
  induction x.
  rewrite eeq_def. split.
  intro. exists x. apply H0.
  split. intro x. exists x. apply H0.
  apply (eeq_prop_refl p eeq h H).
Qed.

Lemma wf_two_ind: forall P : set -> set -> Prop,
(forall x1 x2 : set,
 (forall y1 y2 : set, le_two (y1, y2) (x1, x2) -> P y1 y2) -> P x1 x2) ->
forall x y : set, P x y.
Proof.
  intros P H.
  cut (forall z, P (fst z) (snd z)).
  intros. apply (H0 (x, y)).
  apply (well_founded_ind wf_two).
  intros. destruct x. apply (H s s0). intros.
  apply (H0 (y1, y2)). assumption.
Qed.

Lemma eeq_sym : forall x y, eeq x y -> eeq y x.
Proof.
  apply (wf_two_ind (fun x y => eeq x y -> eeq y x)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *. destruct H0. destruct H1. 
  split.
  - intro x. destruct (H1 x). exists x0. apply H. apply Aa ; apply Ff. assumption.
  - split. intro x0. destruct (H0 x0). exists x. apply H. apply Aa ; apply Ff. assumption.
  revert H2. apply eeq_prop_sym.
Qed.

Lemma eeq_trans : forall x y z, eeq x y -> eeq y z -> eeq x z.
Proof.
  apply (wf_two_ind (fun x y => forall z, eeq x y -> eeq y z -> eeq x z)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *. destruct H0. destruct H1. 
  split.
  - intro x. destruct (H1 x). exists x0. apply H. apply Aa ; apply Ff. assumption.
  - split. intro x0. destruct (H0 x0). exists x. apply H. apply Aa ; apply Ff. assumption.
  revert H2. apply eeq_prop_sym.
Qed.
