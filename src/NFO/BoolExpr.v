(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Require Import Setoid.
Add LoadPath "src/Internal" as Internal.
From Internal Require Import Misc FunExt.
(* end hide *)

(** A boolean expression with atoms of type [X] *)
Inductive BExpr {X} :=
  | Bot : BExpr
  | Atom : X -> BExpr
  | Not : BExpr -> BExpr
  | Or : BExpr -> BExpr -> BExpr
.

(** Evaluate a boolean expression to a [Prop] 
    when the atoms are of type [Prop]:
*)
Fixpoint eval (e: BExpr) := match e with
  | Atom p => p
  | Bot => False
  | Not e => ~ eval e
  | Or e e' => eval e \/ eval e'
end.
Notation "⟦ e ⟧" := (eval e).

(** Map the atoms in a boolean expression: *)
Fixpoint map {X Y} (f: X -> Y) (e: BExpr) : BExpr :=
match e with
  | Atom a => Atom (f a)
  | Bot => Bot
  | Not e => Not (map f e)
  | Or e e' => Or (map f e) (map f e')
end.

(** Evaluating a boolean expression with respect to equivalent predicates
    yields equivalent results.
*)
Lemma map_extP {X} {e: @BExpr X} P Q:
  extP P Q -> ⟦map P e⟧ <-> ⟦map Q e⟧.
Proof.
  unfold extP. intro E. induction e; simpl; eauto. tauto.
  rewrite IHe. tauto.
  rewrite IHe1. rewrite IHe2. tauto.
Qed.

(** The usual property about compositions of maps: *)
Lemma map_compose {X Y Z} {f: Y -> Z} {g: X -> Y} {e}:
  map f (map g e) = map (f ∘ g) e.
Proof.
  induction e; simpl; auto.
  - rewrite IHe. auto.
  - rewrite IHe1. rewrite IHe2. auto.
Qed.

(* Auxiliary lemmas on mapping and composing with projections. *)
Lemma map_compose_inl {X Y Z} {f: X -> Z} {g: Y -> Z} {e}:
  map ((f ⨁ g) ∘ inl) e = map f e.
Proof. induction e; simpl; auto. Qed.

Lemma map_compose_inr {X Y Z} {f: X -> Z} {g: Y -> Z} {e}:
  map ((f ⨁ g) ∘ inr) e = map g e.
Proof. induction e; simpl; auto. Qed.

(** * Semantics *)

(** Two boolean expressions are equivalent iff 
    they evaluate to equivalent values with respect to every
    truth assignment P. However, not every assignment is allowed.
    Here we consider only P's that respect the binary relation
    R in input. R is supposed to characterize the equality on atoms of 
    type X. *)
Definition eq_bexpr {X} (R: X -> X -> Prop) e e' : Prop :=
  forall P, respects R P -> ⟦map P e⟧ <-> ⟦map P e'⟧.

Lemma eq_bexpr_ext {X} {R R': X -> X -> Prop} :
  extR R R' -> extR (eq_bexpr R) (eq_bexpr R').
Proof.
  unfold eq_bexpr; split; intros; apply H0;
  apply (respects_ext _ _ H); assumption.
Qed.


(** This lemma is quite important: it will show that our initial
    definition of NFO equality is correct.
    TODO: Because: we wanted to write the rhs, but we had to write
    the lhs in order to be able to prove termination.
*)
Lemma eq_bexpr_simpl {X Y Z R} {f: X -> Z} {g: Y -> Z} {e e'}:
  Equivalence R ->
    eq_bexpr R (map f e) (map g e')
    <->
    eq_bexpr (R ⨀ (f ⨁ g)) (map inl e) (map inr e').
Proof.
  intro EE.
  unfold eq_bexpr. split; intros.
  - pose (fun z => exists u, P u /\ R z ((f ⨁ g) u)) as K.
    specialize H with K.
    repeat rewrite map_compose.
    rewrite (map_extP (compose P inl) (compose K f)).
    rewrite (map_extP (compose P inr) (compose K g)).
    repeat rewrite<- map_compose.
    apply (H (invert_sum_respects (f ⨁ g) R P EE)).
    apply invert_sum_respects_g; auto.
    apply invert_sum_respects_f; auto.
  - specialize H with (P ∘ (f ⨁ g)).
    repeat rewrite map_compose in H.
    repeat rewrite compose_assoc in H.
    rewrite<- map_compose in H.
    rewrite map_compose_inl in H.
    rewrite<- map_compose in H.
    rewrite map_compose_inr in H.
    apply H. unfold respects in *. intros.
    destruct x, x'; unfold compose, sumF; apply H0; apply H1.
Qed.

(** * Equivalence

    In this section, we prove that eq_bexpr is an equivalence relation.
    Actually, we prove variations of the usual reflexivity, symmetry and
    trasitivity. These variants are exactly what is needed to prove
    that equality of NFO sets is an equivalence relation (see NFO.Eeq).
*)

Lemma eq_bexpr_refl X Y e (f: X -> Y) (R: Y -> Y -> Prop)
  (Hrefl: forall x, R (f x) (f x)) :
    eq_bexpr (R ⨀ (f ⨁ f)) (map inl e) (map inr e).
Proof.
  unfold eq_bexpr. intros.
  induction e; simpl; try tauto; eauto.
  apply H. apply Hrefl.
Qed.

Lemma eq_bexpr_sym X Y Z R e e' (f: X -> Z) (g: Y -> Z):
  eq_bexpr (R ⨀ (f ⨁ g)) (map inl e) (map inr e')
    -> eq_bexpr (R ⨀ (g ⨁ f)) (map inl e') (map inr e).
Proof.
  intros. unfold eq_bexpr in *. intros.
  specialize H with (P ∘ swap).
  repeat rewrite map_compose in H.
  repeat rewrite compose_assoc in H.
  rewrite comp_swap_inl in H.
  rewrite comp_swap_inr in H.
  repeat rewrite<- map_compose in H.
  apply iff_sym. apply H.
  apply respects_swap. assumption.
Qed.

Lemma aux_inl X Y Z W f1 f2 f3 P (R : W -> W -> Prop)
  (sym: forall a b, R a b -> R b a)
  (trans: forall a b c, inv3 f1 f2 f3 a -> inv3 f1 f2 f3 b -> inv3 f1 f2 f3 c -> R a b -> R b c -> R a c):
  let g := invert_sum P (fun (a : X) (b : Y) => R (f1 a) (f2 b))
  (fun (a : Z) (b : Y) => R (f2 b) (f3 a)) in
  respects (R ⨀ (f1 ⨁ f3)) P
  -> respects (R ⨀ (f1 ⨁ f2)) (P ∘ inl ⨁ g).
Proof.
  intros.
  unfold compR, sumF in H.
  unfold respects; intros; destruct x, x'; firstorder;
  unfold sumF, compose; unfold sumF, compR in H.
  - apply (H (inl x0) (inl x)). firstorder; eauto with misc. auto.
  - apply (H (inl x) (inr x0)). firstorder; eauto with misc. auto.
  - apply (H (inl x0) (inl x)). firstorder; eauto with misc. auto.
  - apply (H (inr x0) (inl x)). firstorder; eauto with misc. auto.
Admitted.
(* Qed. *)

Lemma aux_inr X Y Z W f1 f2 f3 P (R : W -> W -> Prop)
  (sym: forall a b, R a b -> R b a)
  (trans: forall a b c, inv3 f1 f2 f3 a -> inv3 f1 f2 f3 b -> inv3 f1 f2 f3 c -> R a b -> R b c -> R a c):
  let g := invert_sum P (fun (a : X) (b : Y) => R (f1 a) (f2 b))
  (fun (a : Z) (b : Y) => R (f2 b) (f3 a)) in
  respects (R ⨀ (f1 ⨁ f3)) P
  -> respects (R ⨀ (f2 ⨁ f3)) (g ⨁ P ∘ inr).
Proof.
  intros. unfold compR, sumF in H.
  unfold respects; intros; destruct x, x'; firstorder;
  unfold sumF, compose; unfold sumF, compR in H.
Admitted.
  (* - apply (H (inl x) (inr z)). firstorder. auto.
  - apply (H (inr x) (inr z)). firstorder. auto.
  - apply (H (inl x) (inr z)). firstorder. auto.
  - apply (H (inr x) (inr z)). firstorder. auto.
Qed. *)

(** TODO: This needs some love... *)
Lemma eq_bexpr_trans {X Y Z W} {R : W -> W -> Prop} {f1 f2 f3}
  {e1 : @BExpr X} {e2 : @BExpr Y} {e3 : @BExpr Z}
  (sym: forall a b, R a b -> R b a)
  (trans: forall a b c, inv3 f1 f2 f3 a -> inv3 f1 f2 f3 b -> inv3 f1 f2 f3 c -> R a b -> R b c -> R a c)
  : eq_bexpr (R ⨀ (f1 ⨁ f2)) (map inl e1) (map inr e2)
  -> eq_bexpr (R ⨀ (f2 ⨁ f3)) (map inl e2) (map inr e3)
  -> eq_bexpr (R ⨀ (f1 ⨁ f3)) (map inl e1) (map inr e3).
Proof.
  unfold eq_bexpr. intros.
  pose (invert_sum P (fun a b => R (f1 a) (f2 b)) (fun a b => R (f2 b) (f3 a))) as g.
  specialize H with (P ∘ inl ⨁ g).
  specialize H0 with (g ⨁ P ∘ inr).
  revert H H0.
  repeat rewrite map_compose.
  repeat rewrite map_compose_inl.
  repeat rewrite map_compose_inr.
  intros.
  apply (fun A B => iff_trans (H A) (H0 B)).
  apply aux_inl; assumption.
  apply aux_inr; assumption.
Qed.
