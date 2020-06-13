Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Add LoadPath "src/NFO/".
Require Import Aux.
Require Import FunExt.


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

Lemma boolean_map_ext {X Y} {p} (f: X -> Y) (g: X -> Y):
  ext f g -> boolean_map f p = boolean_map g p.
Proof.
  intro E. induction p; simpl; auto.
  - rewrite (E x). auto.
  - rewrite IHp. auto.
  - rewrite IHp1. rewrite IHp2. auto.
Qed.

Require Import Setoid.
Lemma boolean_map_extP {X} {p: boolean X} f g:
  extP f g -> eval (boolean_map f p) <-> eval (boolean_map g p).
Proof.
  intro E. induction p; simpl; auto.
  - tauto.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

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

(* mk_sum *)

Definition mk_sum {X Y Z} f g : X + Y -> Z := fun s =>
  match s with
  | inl x => f x
  | inr y => g y
  end.

Lemma compose_sum_inl {X Y Z} {f: X -> Z} {g: Y -> Z} :
  ext ((compose (mk_sum f g) inl)) f.
Proof. unfold ext. intros. apply eq_refl. Qed.

Lemma compose_sum_inr {X Y Z} {f: X -> Z} {g: Y -> Z} :
  ext ((compose (mk_sum f g) inr)) g.
Proof. intro x. apply eq_refl. Qed.

Lemma boolean_map_compose_inl {X Y Z} {f: X -> Z} {g: Y -> Z} {a}:
  boolean_map (compose (mk_sum f g) inl) a = boolean_map f a.
Proof. induction a; simpl; auto. Qed.

Lemma boolean_map_compose_inr {X Y Z} {f: X -> Z} {g: Y -> Z} {a}:
  boolean_map (compose (mk_sum f g) inr) a = boolean_map g a.
Proof. induction a; simpl; auto. Qed.

Lemma eeq_boolean_trans {X Y Z W} {h h' h''}
  {p : boolean X} {p' : boolean Y} {p'' : boolean Z}
  {P : W -> W -> Prop}
  :  (forall a b, P a b -> P b a)
  -> (forall a b c, inv3 h h' h'' a -> inv3 h h' h'' b -> inv3 h h' h'' c -> P a b -> P b c -> P a c)
  -> eeq_boolean (boolean_map inl p) (boolean_map inr p')
      (sum_i P h h')
  -> eeq_boolean (boolean_map inl p') (boolean_map inr p'')
      (sum_i P h' h'')
  -> eeq_boolean (boolean_map inl p) (boolean_map inr p'')
      (sum_i P h h'').
Proof.
  intros sym trans.
  unfold eeq_boolean.
  intros.
  pose (fun y => 
    (exists x, f (inl x) /\ P (h x) (h' y))
    \/ (exists z, f (inr z) /\ P (h' y) (h'' z))
    ) as g.
  specialize H with (mk_sum (compose f inl) g).
  specialize H0 with (mk_sum g (compose f inr)).
  revert H H0.
  repeat rewrite boolean_map_compose.
  repeat rewrite boolean_map_compose_inl.
  repeat rewrite boolean_map_compose_inr.
  intros.
  apply (fun A B => iff_trans (H A) (H0 B)); unfold respects; intros; destruct x; destruct x'; simpl mk_sum; unfold respects in H1; simpl in H2; unfold g; unfold compose.
  - apply (H1 (inl x) (inl x0) H2).
  - split; intro.
    -- left. exists x. auto.
    -- repeat destruct H3.
      specialize H1 with (inl x) (inl x0). simpl sum_i in H1.
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z H2 (sym _ _ H4))); auto.
      specialize H1 with (inl x) (inr x0). simpl sum_i in H1.
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z H2 H4)); auto.
  - split; intro.
    -- repeat destruct H3.
      specialize H1 with (inl x) (inl x0). simpl sum_i in H1.
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z (sym _ _ H2) (sym _ _ H4))); auto.
      specialize H1 with (inl x) (inr x0). simpl sum_i in H1.
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z (sym _ _ H2) H4)); auto.
    -- left. exists x. auto.
  - split; intro.
  -- repeat destruct H3. left. exists x. split; auto.
     apply (fun X Y Z => trans _ _ _ X Y Z H4 H2); auto.
     right. exists x. split; auto.
     apply (fun X Y Z => trans _ _ _ X Y Z (sym _ _ H2) H4); auto.
  -- repeat destruct H3. left. exists x. split; auto.
     apply (fun X Y Z => trans _ _ _ X Y Z H4 (sym _ _ H2)); auto.
     right. exists x. split; auto.
     apply (fun X Y Z => trans _ _ _ X Y Z H2 H4); auto.
  - split; intro.
    -- repeat destruct H3. left. exists x. split; auto.
      apply (fun X Y Z => trans _ _ _ X Y Z H4 H2); auto.
      right. exists x. split; auto.
      apply (fun X Y Z => trans _ _ _ X Y Z (sym _ _ H2) H4); auto.
    -- repeat destruct H3. left. exists x. split; auto.
      apply (fun X Y Z => trans _ _ _ X Y Z H4 (sym _ _ H2)); auto.
      right. exists x. split; auto.
      apply (fun X Y Z => trans _ _ _ X Y Z H2 H4); auto.
  - split; intro.
    -- repeat destruct H3.
      specialize H1 with (inl x) (inr z). simpl sum_i in H1.
      apply H1. apply (fun X Y Z => trans _ _ _ X Y Z H4 H2); auto.
      assumption. specialize H1 with (inr x) (inr z). simpl sum_i in H1.
      apply H1. apply (fun X Y Z => trans _ _ _ X Y Z (sym _ _ H4) H2); auto.
      assumption.
    -- right. exists z. split; auto. 
  - split; intro.
  -- right. exists z. split; auto. 
  -- repeat destruct H3.
    specialize H1 with (inl x) (inr z). simpl sum_i in H1.
    apply H1. apply (fun X Y Z => trans _ _ _ X Y Z H4 (sym _ _ H2)); auto.
    auto.
    specialize H1 with (inr x) (inr z); auto. simpl sum_i in H1.
    apply H1. apply (fun X Y Z => sym _ _ (trans _ _ _ X Y Z H2 H4)); auto. auto.
  - apply H1. assumption.
Qed.
