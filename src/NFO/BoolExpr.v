(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Require Import Setoid.
Add LoadPath "src".
From Internal Require Import Misc FunExt.
(* end hide *)

(** A boolean expression with atoms of type X *)
Inductive boolean {X} :=
  | Bot : boolean
  | Atom : X -> boolean
  | Not : boolean -> boolean
  | Or : boolean -> boolean -> boolean
.

(** Evaluate a boolean expression of Props to a Prop *)
Fixpoint eval (e: boolean) := match e with
  | Atom p => p
  | Bot => False
  | Not e => ~ eval e
  | Or e e' => eval e \/ eval e'
end.
Notation "⟦ e ⟧" := (eval e).

(** Maps the atoms in a boolean expression *)
Fixpoint map {X Y} (f: X -> Y) (e: boolean) : boolean :=
match e with
  | Atom a => Atom (f a)
  | Bot => Bot
  | Not e => Not (map f e)
  | Or e e' => Or (map f e) (map f e')
end.

(** Evaluating a boolean expression with respect to equivalent predicates
    yields equivalent results.
*)
Lemma map_extP {X} {e: @boolean X} P Q:
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

(** * Extensional equality of boolean expressions *)

(** Two boolean expressions are extensionally equal iff 
    they evaluate to equivalent values with respect to every
    truth assignment P. However, not every assignment is allowed.
    Here we consider only P's that respect the binary relation
    R in input. R is supposed to characterize the equality on atoms of 
    type X. *)
Definition eeq_boolean {X} (R: X -> X -> Prop) e e' : Prop :=
  forall P, respects R P -> ⟦map P e⟧ <-> ⟦map P e'⟧.

Lemma eeq_boolean_ext {X} {R R': X -> X -> Prop} :
  extR R R' -> extR (eeq_boolean R) (eeq_boolean R').
Proof.
  unfold eeq_boolean. split; intros; apply H0;
  apply (respects_ext _ _ H); assumption.
Qed.


(** Gosh: important. This shows that the initial approximation of eeq is correct. *)
Lemma eeq_boolean_simpl:
  forall {X Y Z R} {f: X -> Z} {g: Y -> Z} {e e'},
    Equivalence R ->
      eeq_boolean (R ⨀ (f ⨁ g)) (map inl e) (map inr e')
        <-> eeq_boolean R (map f e) (map g e').
Proof.
  intros. rename H into EE. pose EE as EE'. destruct EE.
  unfold eeq_boolean. split; intros.
  - specialize H with (P ∘ (f ⨁ g)).
    repeat rewrite map_compose in H.
    repeat rewrite compose_assoc in H.
    rewrite<- map_compose in H.
    rewrite map_compose_inl in H.
    rewrite<- map_compose in H.
    rewrite map_compose_inr in H.
    apply H. unfold respects in *. intros.
    destruct x, x'; unfold compose, sumF; apply H0; apply H1.
  - pose (invert_sum P (R ∘ f) (R ∘ g)) as K.
    specialize H with K.
    cut (respects R K).
  -- intro. repeat rewrite map_compose.
    rewrite (map_extP (compose P inl) (compose K f)).
    rewrite (map_extP (compose P inr) (compose K g)).
    repeat rewrite<- map_compose. apply (H H1).
    --- unfold FunExt.extP. unfold compose.
        intros. unfold K. split; intro.
        right. exists x. split; auto.
        repeat destruct H2.
        apply (H0 (inl x0)); auto.
        apply (H0 (inr x0)); auto.
    --- unfold FunExt.extP. unfold compose.
        intros. unfold K. split; intro.
        left. exists x. split; auto.
        repeat destruct H2.
        apply (H0 (inl x0)); auto.
        apply (H0 (inr x0)); auto.
  -- revert H0. apply (invert_sum_respects EE').
Qed.

(** * Equivalence

    In this section, we prove that eeq_boolean is an equivalence relation.
    Actually, we prove variations of the usual reflexivity, symmetry and
    trasitivity. These variants are exactly what is needed to prove
    that equality of NFO sets is an equivalence relation (see NFO.Eeq).
*)

Lemma eeq_boolean_refl {X Y} {f: X -> Y} {R: Y -> Y -> Prop} {e}:
    (forall x, R (f x) (f x))
      -> eeq_boolean (R ⨀ (f ⨁ f)) (map inl e) (map inr e).
Proof.
  unfold eeq_boolean. intros.
  induction e; simpl; try tauto; eauto.
  apply H0. apply H.
Qed.
Hint Resolve eeq_boolean_refl : Bool.

Lemma eeq_boolean_sym {X Y Z R} {f: X -> Z} {g: Y -> Z} {e e'} :
  eeq_boolean (R ⨀ (f ⨁ g)) (map inl e) (map inr e')
    -> eeq_boolean (R ⨀ (g ⨁ f)) (map inl e') (map inr e).
Proof.
  intros. unfold eeq_boolean in *. intros.
  specialize H with (P ∘ swap).
  repeat rewrite map_compose in H.
  repeat rewrite compose_assoc in H.
  rewrite comp_swap_inl in H.
  rewrite comp_swap_inr in H.
  repeat rewrite<- compose_assoc in H.
  repeat rewrite<- map_compose in H.
  apply iff_sym. apply H.
  apply respects_swap. assumption.
Qed.

(** TODO: This needs some love... *)
Lemma eeq_boolean_trans {X Y Z W} {R : W -> W -> Prop} {f1 f2 f3}
  {e1 : @boolean X} {e2 : @boolean Y} {e3 : @boolean Z}
  :  (forall a b, R a b -> R b a)
  -> (forall a b c, inv3 f1 f2 f3 a -> inv3 f1 f2 f3 b -> inv3 f1 f2 f3 c -> R a b -> R b c -> R a c)
  -> eeq_boolean (R ⨀ (f1 ⨁ f2)) (map inl e1) (map inr e2)
  -> eeq_boolean (R ⨀ (f2 ⨁ f3)) (map inl e2) (map inr e3)
  -> eeq_boolean (R ⨀ (f1 ⨁ f3)) (map inl e1) (map inr e3).
Proof.
  Ltac lr H3 x :=
    repeat destruct H3; [left | right]; exists x; split; eauto with misc.
  intros sym trans. unfold eeq_boolean. intros.
  pose (invert_sum P (fun a b => R (f1 a) (f2 b)) (fun a b => R (f2 b) (f3 a))) as g.
  specialize H with (P ∘ inl ⨁ g).
  specialize H0 with (g ⨁ P ∘ inr).
  revert H H0.
  repeat rewrite map_compose.
  repeat rewrite map_compose_inl.
  repeat rewrite map_compose_inr.
  intros.
  apply (fun A B => iff_trans (H A) (H0 B)); unfold respects; intros; destruct x, x'; simpl sumF; unfold respects in H1; simpl; unfold g; unfold compose; auto; unfold compR, sumF.
  - split; intro.
  -- left. exists x. auto.
  -- repeat destruct H3; unfold compR, sumF in H1.
      specialize H1 with (inl x) (inl x0). 
      unfold sumF in H2.
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z H2 (sym _ _ H4))); eauto with misc.
      specialize H1 with (inl x) (inr x0).
      unfold sumF in H2.
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z H2 H4)); eauto with misc.
  - split; intro.
    -- repeat destruct H3; unfold compR, sumF in H2.
      specialize H1 with (inl x) (inl x0).
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z (sym _ _ H2) (sym _ _ H4))); eauto with misc.
      specialize H1 with (inl x) (inr x0).
      apply (fun X Y Z => H1 (trans _ _ _ X Y Z (sym _ _ H2) H4)); eauto with misc.
    -- left. exists x. auto.
  - split; intro; lr H3 x.
  - split; intro; lr H3 x.
  - split; intro.
    -- repeat destruct H3.
      specialize H1 with (inl x) (inr z). unfold compR, sumF in H1.
      apply H1; eauto with misc.
      specialize H1 with (inr x) (inr z). unfold compR, sumF in H1.
      apply H1; eauto with misc.
    -- right. exists z. split; auto. 
  - split; intro.
  -- right. exists z. split; auto. 
  -- repeat destruct H3.
     specialize H1 with (inl x) (inr z). unfold compR, sumF in H1.
     apply H1; eauto with misc.
     specialize H1 with (inr x) (inr z). unfold compR, sumF in H1. 
     apply H1; eauto with misc.
Qed.
