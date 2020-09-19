(** * NFO.Morphism : Morphisms *)
(** In this module we prove that:
    - IN, AIN, BIN are EQ-morphisms.
    - AIN and BIN are respectively AEQ- and BEQ-morphisms.
    - The axiom of extensionality for AEQ and BEQ.
      Extensionality for IN and EQ will be proved in NFO.Ext.
*)

(* begin hide *)
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Export Relation_Definitions.
Require Export Setoid.

Add LoadPath "src".
From Internal Require Import Misc FunExt.
From NFO Require Import BoolExpr Model Wf Eq In Xor.
(* end hide *)

(** * Proofs for AEQ and AIN *)

Lemma AEQ_AIN: forall {X Y} {f: X -> _} {g: Y -> _},
  AEQ f g -> forall x, AIN x f <-> AIN x g.
Proof.
  intros. unfold AIN. destruct H. split; intro; destruct H1.
  - destruct (H x0). exists x1. eauto with Eeq.
  - destruct (H0 x0). exists x1. eauto with Eeq.
  Qed.
Lemma AIN_AEQ: forall {X Y} {f: X -> _} {g: Y -> _},
  (forall x, AIN x f <-> AIN x g) -> AEQ f g.
Proof.
  intros. unfold AEQ. split; intro x.
  - destruct (H (f x)). cut (AIN (f x) f). intro. destruct (H0 H2).
    exists x0. eauto with Eeq. unfold AIN. eauto with Eeq.
  - destruct (H (g x)). cut (AIN (g x) g). intro. destruct (H1 H2).
    exists x0. eauto with Eeq. unfold AIN. eauto with Eeq.
Qed.

Theorem Aext {X Y} {f: X -> _} {g: Y -> _} :
  AEQ f g <-> forall x, AIN x f <-> AIN x g.
Proof. split. apply AEQ_AIN. apply AIN_AEQ. Qed.

(** TODO: Vale anche nell'altra direzione, ma non ci serve. Lo stesso per BIN. *)
Lemma EQ_AIN: forall {x y X} {f: X -> _},
  x == y -> AIN x f <-> AIN y f.
Proof.
  intros. unfold AIN. split; intro; destruct H0; exists x0; eauto with Eeq.
Qed.

(** * Proofs for EQ and IN *)

(* respects EQ (IN z)
/\ respecs EQ (fun x => IN x z) *)
(** TODO: pose g is suspiciously similar to invert_sum
  and then simply prove cut (respects EQ g)
  with invert_sum_respects.
*)
Lemma IN_respects_EQ: forall z x y, EQ x y ->
  (IN z x <-> IN z y)
  /\ (IN x z <-> IN y z).
Proof.
  induction z.
  apply (wf_two_ind wf_lt (fun x y => EQ x y -> _: Prop)).
  destruct x1, x2. intros. repeat rewrite IN_unfold. split; apply xor_iff.
  - apply AEQ_AIN. rewrite EQ_unfold in H2; destruct H2. assumption.
  - rewrite EQ_unfold in H2; destruct H2. 
    pose (fun s : SET =>
      (exists a0, s == g0 a0 /\ IN (g0 a0) (S X Y f g e))
      \/ (exists a1, s == g1 a1 /\ IN (g1 a1) (S X Y f g e))
    ) as K.
    repeat rewrite map_compose in H3. setoid_rewrite<- BIN_bexpr_map.
    cut (eval (map (Basics.compose K g0) e0) <-> (let w := fun a => IN (g0 a) (S X Y f g e) in eval (map w e0))). intro.
    cut (eval (map (Basics.compose K g1) e1) <-> (let w := fun a => IN (g1 a) (S X Y f g e) in eval (map w e1))). intro.
    rewrite<- H4. rewrite<- H5. 
    cut (respects EQ K). 
    -- repeat rewrite<- map_compose. apply H3.
    -- unfold respects. intros. unfold K. split; intro; repeat destruct H7.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
    -- apply map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold K. split; intro. repeat destruct H5; auto.
       apply (fun K => proj2 (H1 (g0 x) (g1 a1) K (EQ_sym _ _ H5))).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (g1 x) (g1 a1) K (EQ_sym _ _ H5))).
       auto with Wff. assumption.
       right. exists a1. split; eauto with Eeq.
    -- apply map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold K. split; intro. repeat destruct H4; auto.
       apply (fun K => proj2 (H1 (g0 a1) (g0 x) K H4)).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (g0 a1) (g1 x) K H4)).
       auto with Wff. assumption.
       left. exists a1. split; eauto with Eeq.
  - apply (EQ_AIN H2).
  - setoid_rewrite<- BIN_bexpr_map. apply map_extP. unfold FunExt.extP. intro a.
    apply (proj1 (H0 a (S X0 Y0 f0 g0 e0) (S X1 Y1 f1 g1 e1) H2)).
Qed.

(** Register IN as a EQ-morphism: *)
Add Morphism IN with signature EQ ==> EQ ==> iff as IN_mor.
Proof.
  intros. destruct (IN_respects_EQ x x0 y0 H0).
  destruct (IN_respects_EQ y0 x y H). tauto.
Qed.

(** * Proofs for BEQ and BIN *)

Lemma BEQ_BIN {e e'}:
  BEQ e e' -> forall x, BIN x e <-> BIN x e'.
Proof.
  intros. unfold eq_bexpr in H.
  pose proof (H (fun s => IN s x)).
  repeat rewrite<- BIN_bexpr. apply H0.
  unfold respects. intros.
  apply IN_respects_EQ. assumption.
Qed.

Lemma BIN_BEQ: forall {X Y} {e e'} {h: X -> _} {h': Y -> _},
  (forall x, BIN x (map h e) <-> BIN x (map h' e'))
    -> BEQ (map h e) (map h' e').
Proof.
  intros. unfold BEQ, eq_bexpr. intros.
  rewrite<- (xxx_r h' H0). rewrite<- (xxx h H0). apply H.
Qed.

Theorem Bext {X Y} {e e'} {h: X -> _} {h': Y -> _} :
  BEQ (map h e) (map h' e')
  <-> forall x, BIN x (map h e) <-> BIN x (map h' e').
Proof. split. apply BEQ_BIN. apply BIN_BEQ. Qed.

Lemma EQ_BIN {x y e}:
  x == y -> BIN x e <-> BIN y e.
Proof.
  intros. induction e; simpl BIN; try tauto.
  apply IN_respects_EQ. auto.
Qed.
