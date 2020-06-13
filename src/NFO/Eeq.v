Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Wff.

Definition eeq' : set * set -> Prop.
refine ( Fix wf_two (fun _ => Prop) (
  fun x rec => (
    match x as x0 return (x = x0 -> Prop) with
    | (S A p h X f, S A' p' h' X' f') => fun eqx =>
          (forall x, exists y, rec (f x, f' y) _)
          /\ (forall y, exists x, rec (f x, f' y) _)
          /\ let w (i j: A + A') := match i, j with
            | inl i', inl j' => rec (h i', h j') _
            | inl i', inr j' => rec (h i', h' j') _
            | inr i', inl j' => rec (h' i', h j') _
            | inr i', inr j' => rec (h' i', h' j') _
            end in 
            eeq_boolean
              (boolean_map inl p) (boolean_map inr p') w
    end) eq_refl
 ))
.
  rewrite eqx; apply AB; apply lt_f.
  rewrite eqx; apply AB; apply lt_f.
  rewrite eqx; apply AA; apply lt_h.
  rewrite eqx; apply AB; apply lt_h.
  rewrite eqx; apply BA; apply lt_h.
  rewrite eqx; apply BB; apply lt_h.
Qed.

Definition eeq x y := eeq' (x, y).

Definition eeq_low {X Y} f g :=
  (forall x: X, exists y, eeq (f x) (g y))
  /\ forall y: Y, exists x, eeq (f x) (g y).

Axiom eeq_def : forall x y, eeq x y =
  match x, y with S A p h X f, S A' p' h' X' f'
    => eeq_low f f'
        /\  
          eeq_boolean (boolean_map inl p) (boolean_map inr p')
            (sum_i eeq h h')
end.

Lemma eeq_refl {x} : eeq x x.
Proof.
  induction x.
  rewrite eeq_def. unfold eeq_low. split.
  split; intro.
  - exists x. apply H0.
  - exists y. apply H0.
  - apply eeq_boolean_refl. apply H.
Qed.

Lemma eeq_sym : forall {x y}, eeq x y -> eeq y x.
Proof.
  apply (wf_two_ind (fun x y => eeq x y -> eeq y x)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *. unfold eeq_low in *. repeat destruct H0.
  split. split.
  - intro x0. destruct (H2 x0). exists x. apply H. apply AB ; apply lt_f. assumption.
  - intro x. destruct (H0 x). exists x0. apply H. apply AB ; apply lt_f. assumption.
  - revert H1. apply eeq_boolean_sym.
Qed.

Lemma eeq_trans : forall {x y z}, eeq x y -> eeq y z -> eeq x z.
Proof.
  apply (wf_two_ind (fun x y => forall z, eeq x y -> eeq y z -> eeq x z)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *. unfold eeq_low in *.
  repeat destruct H0.
  destruct z. repeat destruct H1. split. split.
  - intro x. destruct (H0 x). destruct (H1 x0). exists x1.
    apply (fun X => H _ _ X _ H6 H7).
    apply AB; apply lt_f.
  - intro y. destruct (H5 y). destruct (H3 x). exists x0.
    apply (fun X => H _ _ X _ H7 H6).
    apply AB; apply lt_f.
  - apply (fun X => eeq_boolean_trans (@eeq_sym) X H2 H4).
    intros. repeat destruct H6; destruct H7; repeat destruct H6; destruct H8; repeat destruct H6; apply (fun X => H _ _ X _ H9 H10).
    apply AA; apply lt_h. apply AA; apply lt_h. apply AA; apply lt_h.
    apply AB; apply lt_h. apply AB; apply lt_h. apply AB; apply lt_h.
    admit.
    (* apply H. *)
Admitted.

(* WOW *)
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Lemma eeq_b_simplified:
  forall {X Y p p'} {h: X -> set} {h': Y -> set},
    eeq_boolean (boolean_map inl p) (boolean_map inr p')
      (sum_i eeq h h')
    <->
    eeq_boolean (boolean_map h p) (boolean_map h' p') eeq.
Proof.
  intros. unfold eeq_boolean. split; intros.
  - specialize H with (compose f (mk_sum h h')).
  repeat rewrite boolean_map_compose in H.
  repeat rewrite compose_assoc in H.
  rewrite<- boolean_map_compose in H.
  rewrite boolean_map_compose_inl in H.
  rewrite<- boolean_map_compose in H.
  rewrite boolean_map_compose_inr in H.
  apply H.
  unfold respects in *. intros.
  destruct x, x'; unfold compose, mk_sum; apply H0; apply H1.
  -
  pose (fun z => (exists x, eeq (h x) z /\ f (inl x)) \/ (exists y, eeq (h' y) z /\ f (inr y))) as g.
  specialize H with g.
  cut (respects g eeq).
  intro. pose proof (H H1).
  admit.
  unfold respects in *. unfold g. intros.
  split; intros; repeat destruct H2.
  left. exists x0. split; auto. admit.
  right. exists x0. split; auto. admit.
  left. exists x0. split; auto. admit.
(* 


  repeat rewrite boolean_map_compose in H.
  repeat rewrite boolean_map_compose.
  unfold respects, sum_i in H0.
  repeat rewrite compose_assoc in H.
  rewrite<- boolean_map_compose in H.
  rewrite boolean_map_compose_inl in H.
  rewrite<- boolean_map_compose in H.
  rewrite boolean_map_compose_inr in H.
  apply H.
  unfold respects in *. intros.
  destruct x, x'; unfold compose, mk_sum; apply H0; apply H1.
  unfold respects in H, H0.
  rewrite compose_sum_inr in H. *)
Admitted.

Require Import Setoid.
Lemma eeq_unfold : forall x y, eeq x y <->
  match x, y with S A p h X f, S A' p' h' X' f'
    => eeq_low f f'
      /\  
      eeq_boolean (boolean_map h p) (boolean_map h' p') eeq
end.
Proof.
  intros. destruct x, y. rewrite<- eeq_b_simplified.
  rewrite eeq_def. tauto.
Qed.
