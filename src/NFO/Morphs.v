(** * NFO.Morphs : Morphisms *)
(** In this module we prove that:
    - iin, Ain, Bin are eeq-morphisms.
    - Ain and Bin are respectively Aeq- and Beq-morphisms.
    - The axiom of extensionality for Aeq and Beq.
      Extensionality for iin and eeq will be proved in NFO.Ext.
*)

(* begin hide *)
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Export Relation_Definitions.
Require Export Setoid.

Add LoadPath "src".
From Internal Require Import FunExt Aux.
From NFO Require Import BoolExpr Model Wff Eeq Iin Xor.
(* end hide *)

(** * Proofs for Aeq and Ain *)

Lemma Aeq_Ain: forall {X Y} {f: X -> _} {g: Y -> _},
  Aeq f g -> forall x, Ain x f <-> Ain x g.
Proof.
  intros. unfold Ain. destruct H. split; intro; destruct H1.
  - destruct (H x0). exists x1. eauto with Eeq.
  - destruct (H0 x0). exists x1. eauto with Eeq.
  Qed.
Lemma Ain_Aeq: forall {X Y} {f: X -> _} {g: Y -> _},
  (forall x, Ain x f <-> Ain x g) -> Aeq f g.
Proof.
  intros. unfold Aeq. split; intro x.
  - destruct (H (f x)). cut (Ain (f x) f). intro. destruct (H0 H2).
    exists x0. eauto with Eeq. unfold Ain. eauto with Eeq.
  - destruct (H (g x)). cut (Ain (g x) g). intro. destruct (H1 H2).
    exists x0. eauto with Eeq. unfold Ain. eauto with Eeq.
Qed.

Theorem Aext {X Y} {f: X -> _} {g: Y -> _} :
  Aeq f g <-> forall x, Ain x f <-> Ain x g.
Proof. split. apply Aeq_Ain. apply Ain_Aeq. Qed.

(** TODO: Vale anche nell'altra direzione, ma non ci serve. Lo stesso per Bin. *)
Lemma eeq_Ain: forall {x y X} {f: X -> _},
  x == y -> Ain x f <-> Ain y f.
Proof.
  intros. unfold Ain. split; intro; destruct H0; exists x0; eauto with Eeq.
Qed.

(** * Proofs for eeq and iin *)

(* respects eeq (iin z)
/\ respecs eeq (fun x => iin x z) *)
(** TODO: pose g is suspiciously similar to invert_sum
  and then simply prove cut (respects eeq g)
  with invert_sum_respects.
*)
Lemma iin_respects_eeq: forall z x y, eeq x y ->
  (iin z x <-> iin z y)
  /\ (iin x z <-> iin y z).
Proof.
  induction z.
  apply (wf_two_ind wf_lt (fun x y => eeq x y -> _: Prop)).
  destruct x1, x2. intros. repeat rewrite iin_unfold. split; apply xor_iff.
  - apply Aeq_Ain. rewrite eeq_unfold in H2; destruct H2. assumption.
  - rewrite eeq_unfold in H2; destruct H2. 
    pose (fun s : set =>
      (exists a0, s == g0 a0 /\ iin (g0 a0) (S X Y f g e))
      \/ (exists a1, s == g1 a1 /\ iin (g1 a1) (S X Y f g e))
    ) as K.
    repeat rewrite map_compose in H3. setoid_rewrite<- Bin_bexpr.
    cut (eval (map (Basics.compose K g0) e0) <-> (let w := fun a => iin (g0 a) (S X Y f g e) in eval (map w e0))). intro.
    cut (eval (map (Basics.compose K g1) e1) <-> (let w := fun a => iin (g1 a) (S X Y f g e) in eval (map w e1))). intro.
    rewrite<- H4. rewrite<- H5. 
    cut (respects eeq K). 
    -- repeat rewrite<- map_compose. apply H3.
    -- unfold respects. intros. unfold K. split; intro; repeat destruct H7.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
    -- apply map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold K. split; intro. repeat destruct H5; auto.
       apply (fun K => proj2 (H1 (g0 x) (g1 a1) K (eeq_sym _ _ H5))).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (g1 x) (g1 a1) K (eeq_sym _ _ H5))).
       auto with Wff. assumption.
       right. exists a1. split; eauto with Eeq.
    -- apply map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold K. split; intro. repeat destruct H4; auto.
       apply (fun K => proj2 (H1 (g0 a1) (g0 x) K H4)).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (g0 a1) (g1 x) K H4)).
       auto with Wff. assumption.
       left. exists a1. split; eauto with Eeq.
  - apply (eeq_Ain H2).
  - setoid_rewrite<- Bin_bexpr. apply map_extP. unfold FunExt.extP. intro a.
    apply (proj1 (H0 a (S X0 Y0 f0 g0 e0) (S X1 Y1 f1 g1 e1) H2)).
Qed.

(** Register iin as a eeq-morphism: *)
Add Morphism iin with signature eeq ==> eeq ==> iff as iin_mor.
Proof.
  intros. destruct (iin_respects_eeq x x0 y0 H0).
  destruct (iin_respects_eeq y0 x y H). tauto.
Qed.

(** * Proofs for Beq and Bin *)

Lemma Qeq_Qin: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  Qeq (map h p) (map h' p')
  -> forall x, Qin x h p <-> Qin x h' p'.
Proof.
  intros. unfold eeq_boolean in H.
  pose proof (H (fun s => iin s x)).
  repeat rewrite map_compose in H0.
  unfold Basics.compose in H0.
  repeat rewrite<- Bin_bexpr. apply H0.
  unfold respects. intros.
  apply iin_respects_eeq. assumption.
Qed.

Lemma Qin_Qeq: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  (forall x, Qin x h p <-> Qin x h' p')
    -> Qeq (map h p) (map h' p').
Proof.
  intros. unfold Qeq, eeq_boolean. intros.
  rewrite<- (xxx_r h' H0). rewrite<- (xxx h H0). apply H.
Qed.

Theorem Qext {X Y} {p p'} {h: X -> _} {h': Y -> _} :
  Qeq (map h p) (map h' p')
  <-> forall x, Qin x h p <-> Qin x h' p'.
Proof. split. apply Qeq_Qin. apply Qin_Qeq. Qed.

Lemma eeq_Qin: forall {x y A p} {h: A -> _},
  x == y -> Qin x h p <-> Qin y h p.
Proof.
  intros x y A p. induction p; simpl Qin. 
  - tauto.
  - intro. apply iin_respects_eeq.
  - intro. specialize IHp with h. tauto.
  - intro h. specialize IHp1 with h. specialize IHp2 with h. tauto.
Qed.
