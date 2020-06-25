Require Import Setoid.
From Coq.Program Require Import Basics Combinators.

Add LoadPath "src".
From Internal Require Import Aux FunExt.


(** A boolean expression with atoms of type X *)
Inductive boolean {X} :=
  | Bot : boolean
  | Atom : X -> boolean
  | Not : boolean -> boolean
  | Or : boolean -> boolean -> boolean
.

(** Evaluate a boolean expression of Props to a Prop *)
Fixpoint eval (p: boolean) := match p with
  | Atom a => a
  | Bot => False
  | Not p => eval p -> False
  | Or p1 p2 => eval p1 \/ eval p2
end.

(** Maps the atoms in a boolean expression *)
Fixpoint boolean_map {X Y} (f: X -> Y) (p: boolean) : boolean :=
match p with
  | Atom a => Atom (f a)
  | Bot => Bot
  | Not p => Not (boolean_map f p)
  | Or p1 p2 => Or (boolean_map f p1) (boolean_map f p2)
end.

(** Evaluating a boolean expression with respect to equivalent predicates
    yields equivalent results.
*)
Lemma boolean_map_extP {X} {b: @boolean X} P Q:
  extP P Q -> eval (boolean_map P b) <-> eval (boolean_map Q b).
Proof.
  unfold extP. intro E. induction b; simpl; eauto. tauto.
  rewrite IHb. tauto.
  rewrite IHb1. rewrite IHb2. tauto.
Qed.

(** The composition of maps on boolean expressions *)
Lemma boolean_map_compose {X Y Z f g b}:
  boolean_map f (boolean_map g b) = boolean_map (@compose X Y Z f g) b.
Proof.
  induction b; simpl; auto.
  - rewrite IHb. auto.
  - rewrite IHb1. rewrite IHb2. auto.
Qed.

(** Extensional equality of boolean expressions *)

Definition eeq_boolean {X} (R: X -> X -> Prop) b1 b2 : Prop :=
  forall P, respects R P ->
    eval (boolean_map P b1) <-> eval (boolean_map P b2).

Lemma eeq_boolean_ext {X} {R1 R2: X -> X -> Prop} :
  extP2 R1 R2 -> extP2 (eeq_boolean R1) (eeq_boolean R2).
Proof.
  unfold eeq_boolean. split; intros; apply H0;
  apply (respects_ext _ _ H); assumption.
Qed.

(* SUM_I *)
Definition sum_i {X Y Z} (R: Z -> Z -> Prop) f g (i j: X + Y) := 
match i, j with
  | inl x, inl x' => R (f x) (f x')
  | inl x, inr y => R (f x) (g y)
  | inr y, inl x => R (g y) (f x)
  | inr y, inr y' => R (g y) (g y')
end.

(** Rexflexivity for eeq_boolean *)
Lemma eeq_boolean_refl {X Y} :
  forall b (R: Y -> Y -> Prop) (f: X -> Y),
    (forall x, R (f x) (f x))
      -> eeq_boolean (sum_i R f f)
          (boolean_map inl b) (boolean_map inr b).
Proof.
  unfold eeq_boolean. intros.
  induction b; simpl; try tauto; eauto.
  apply H0. apply H.
Qed.
Hint Resolve eeq_boolean_refl : Bool.

(** SYMMETRY *)

Lemma sum_i_sym: forall {X Y Z R f g b1 b2},
  sum_i R f g b1 b2 -> @sum_i X Y Z R g f (swap b1) (swap b2).
Proof.
  unfold sum_i. intros. destruct b1, b2; assumption.
Qed.

Lemma respects_swap {X Y Z P} :
  forall (f: X -> Z) (g: Y -> Z) h,
    respects (sum_i P f g) h
      -> respects (sum_i P g f) (compose h swap).
Proof.
  unfold respects.
  intros. destruct x, x'; unfold compose; simpl; apply H; apply (sum_i_sym H0).
Qed.

Lemma eeq_boolean_sym {X Y Z R p1 p2 h1 h2} :
  eeq_boolean (@sum_i X Y Z R h1 h2)
    (boolean_map inl p1) (boolean_map inr p2) 
  -> eeq_boolean (sum_i R h2 h1)
      (boolean_map inl p2) (boolean_map inr p1).
Proof.
  intros. unfold eeq_boolean in *. intros.
  pose proof (H (compose P swap)).
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

(* sum_funs *)

Lemma boolean_map_compose_inl {X Y Z} {f: X -> Z} {g: Y -> Z} {a}:
  boolean_map (compose (sum_funs f g) inl) a = boolean_map f a.
Proof. induction a; simpl; auto. Qed.

Lemma boolean_map_compose_inr {X Y Z} {f: X -> Z} {g: Y -> Z} {a}:
  boolean_map (compose (sum_funs f g) inr) a = boolean_map g a.
Proof. induction a; simpl; auto. Qed.

Lemma eeq_boolean_trans {X Y Z W} {h h' h''}
  {p : @boolean X} {p' : @boolean Y} {p'' : @boolean Z}
  {P : W -> W -> Prop}
  :  (forall a b, P a b -> P b a)
  -> (forall a b c, inv3 h h' h'' a -> inv3 h h' h'' b -> inv3 h h' h'' c -> P a b -> P b c -> P a c)
  -> eeq_boolean (sum_i P h h') (boolean_map inl p) (boolean_map inr p')
  -> eeq_boolean (sum_i P h' h'') (boolean_map inl p') (boolean_map inr p'')
  -> eeq_boolean (sum_i P h h'') (boolean_map inl p) (boolean_map inr p'').
Proof.
  Ltac lr H3 x :=
    repeat destruct H3; [left | right]; exists x; split; eauto.
  intros sym trans.
  unfold eeq_boolean.
  intros.
  pose (invert_sum P0 (fun a b => P (h a) (h' b)) (fun a b => P (h' b) (h'' a))) as g.
  specialize H with (sum_funs (compose P0 inl) g).
  specialize H0 with (sum_funs g (compose P0 inr)).
  revert H H0.
  repeat rewrite boolean_map_compose.
  repeat rewrite boolean_map_compose_inl.
  repeat rewrite boolean_map_compose_inr.
  intros.
  apply (fun A B => iff_trans (H A) (H0 B)); unfold respects; intros; destruct x; destruct x'; simpl sum_funs; unfold respects in H1; simpl in H2; unfold g; unfold compose; auto.
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
  - split; intro; lr H3 x.
  - split; intro; lr H3 x.
  - split; intro.
    -- repeat destruct H3.
      specialize H1 with (inl x) (inr z). simpl sum_i in H1.
      apply H1; eauto.
      specialize H1 with (inr x) (inr z). simpl sum_i in H1.
      apply H1; eauto.
    -- right. exists z. split; auto. 
  - split; intro.
  -- right. exists z. split; auto. 
  -- repeat destruct H3.
     specialize H1 with (inl x) (inr z). simpl sum_i in H1.
     apply H1; eauto.
     specialize H1 with (inr x) (inr z). simpl sum_i in H1. 
     apply H1; eauto.
Qed.
