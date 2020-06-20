Add LoadPath "src/NFO/".
Require Import FunExt.
Require Import Bool.
Require Import Model.
Require Import Wff.
Require Import Eeq.
Require Import Iin.

Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.

Require Import Xor.

(* Aext *)

Lemma Aeq_Ain: forall {X Y} {f: X -> _} {g: Y -> _},
  Aeq f g -> forall x, Ain x f <-> Ain x g.
Proof.
  intros. unfold Ain. destruct H. split; intro; destruct H1.
  - destruct (H x0). exists x1. apply (eeq_trans (eeq_sym H2) H1).
  - destruct (H0 x0). exists x1. apply (eeq_trans H2 H1).
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

Lemma eeq_Ain: forall {x y X} {f: X -> _},
  x == y -> Ain x f <-> Ain y f.
Proof.
  intros. unfold Ain. split; intro; destruct H0; exists x0.
  apply (eeq_trans H0 H). apply (eeq_trans H0 (eeq_sym H)).
Qed.

(* respects eeq (iin z)
/\ respecs eeq (fun x => iin x z) *)

Lemma iin_respects_eeq: forall z x y, eeq x y ->
  (iin z x <-> iin z y)
  /\ (iin x z <-> iin y z).
Proof.
  induction z.
  apply (wf_two_ind (fun x y => eeq x y -> _: Prop)).
  destruct x1, x2. intros. repeat rewrite iin_unfold. split; apply Xor_eq.
  - apply Aeq_Ain. rewrite eeq_unfold in H2; destruct H2. assumption.
  - rewrite eeq_unfold in H2; destruct H2. unfold eeq_boolean in H1.
    pose (fun s : set =>
      (exists a0, s == h0 a0 /\ iin (h0 a0) (S A p h X f))
      \/ (exists a1, s == h1 a1 /\ iin (h1 a1) (S A p h X f))
    ) as g.
    repeat rewrite boolean_map_compose in H3.
    cut (eval (boolean_map (Basics.compose g h0) p0) <-> (let w := fun a : A0 => iin (h0 a) (S A p h X f) in eval (boolean_map w p0))). intro.
    cut (eval (boolean_map (Basics.compose g h1) p1) <-> (let w := fun a : A1 => iin (h1 a) (S A p h X f) in eval (boolean_map w p1))). intro.
    rewrite<- H4. rewrite<- H5. 
    cut (respects eeq g). 
    -- repeat rewrite<- boolean_map_compose. apply H3.
    -- unfold respects. intros. unfold g. split; intro; repeat destruct H7.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
    -- apply boolean_map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold g. split; intro. repeat destruct H5; auto.
       apply (fun K => proj2 (H1 (h0 x) (h1 a1) K (eeq_sym H5))).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (h1 x) (h1 a1) K (eeq_sym H5))).
       auto with Wff. assumption.
       right. exists a1. split; eauto with Eeq.
    -- apply boolean_map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold g. split; intro. repeat destruct H4; auto.
       apply (fun K => proj2 (H1 (h0 a1) (h0 x) K H4)).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (h0 a1) (h1 x) K H4)).
       auto with Wff. assumption.
       left. exists a1. split; eauto with Eeq.
  - apply eeq_Ain. rewrite eeq_unfold. rewrite eeq_unfold in H2; destruct H2. auto.
  - apply boolean_map_extP. unfold FunExt.extP. intro a.
    apply (proj1 (H a (S A0 p0 h0 X0 f0) (S A1 p1 h1 X1 f1) H2)).
Qed.

(* Qext *)

Lemma aux {X p} {h: X -> _} {x}:
  eval (boolean_map (fun x' => iin (h x') x) p)
  <-> 
  Qin x h p.
Proof. induction p; simpl; tauto. Qed.


Lemma Qeq_Qin: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  Qeq (boolean_map h p) (boolean_map h' p')
  -> forall x, Qin x h p <-> Qin x h' p'.
Proof.
  intros. unfold eeq_boolean in H.
  pose proof (H (fun s => iin s x)).
  repeat rewrite boolean_map_compose in H0.
  unfold Basics.compose in H0.
  repeat rewrite<- aux. apply H0.
  unfold respects. intros.
  apply iin_respects_eeq. assumption.
Qed.

Definition mk_low {X} f h :=
S False (Bot _) (False_rect _) { x: X & f (h x) } (fun k => h (projT1 k)).

Lemma Xor_AF : forall X, Xor X False <-> X.
Proof. intros. unfold Xor. tauto. Qed.

Lemma xxx {X Y} {p} {h: X -> _} {f: set -> Prop} (g: Y -> _):
  respects eeq f ->
  Qin (mk_low f (mk_sum h g)) h p <-> eval (boolean_map f (boolean_map h p)).
Proof.
  intro. induction p; simpl; simpl boolean_map; simpl Qin; simpl eval.
  - tauto.
  - unfold mk_low. rewrite iin_unfold. simpl. unfold Ain.
    rewrite Xor_AF. split; intros.
    destruct H0, x0, x0.
    simpl mk_sum in *. apply (H (h x0) (h x) H0). assumption.
    simpl mk_sum in *. apply (H (g y) (h x) H0). assumption.
    exists (existT _ (inl x) H0). eauto with Eeq.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma xxx_r {X Y} {p} {h: X -> _} {f: set -> Prop} (g: Y -> _):
  respects eeq f ->
  Qin (mk_low f (mk_sum g h)) h p <-> eval (boolean_map f (boolean_map h p)).
Proof.
  intro. induction p; simpl; simpl boolean_map; simpl Qin; simpl eval.
  - tauto.
  - unfold mk_low. rewrite iin_unfold. simpl. unfold Ain.
    rewrite Xor_AF. split; intros.
    destruct H0, x0, x0.
    simpl mk_sum in *. apply (H (g y) (h x) H0). assumption.
    simpl mk_sum in *. apply (H (h x0) (h x) H0). assumption.
    exists (existT _ (inr x) H0). eauto with Eeq.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma Qin_Qeq: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  (forall x, Qin x h p <-> Qin x h' p')
  -> Qeq (boolean_map h p) (boolean_map h' p').
Proof.
  intros. unfold Qeq, eeq_boolean. intros.
  pose (mk_low f h) as g.
  pose proof (H g).
  rewrite<- (xxx h'). rewrite<- (xxx_r h). apply H. auto. auto.
Qed.

Theorem Qext {X Y} {p p'} {h: X -> _} {h': Y -> _} :
  Qeq (boolean_map h p) (boolean_map h' p')
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

(* Extensionality *)

Lemma eeq_iin: forall x y, 
  x == y -> forall z, iin z x <-> iin z y.
Proof.
  destruct x, y.
  rewrite eeq_unfold. intros. repeat rewrite iin_unfold'.
  destruct H. apply Xor_eq. apply Aext; assumption.
  apply Qext; assumption.
Qed.
(* 
Lemma abc: forall A (p: boolean A) h X (f: X -> set),
  (exists x, Qin x h p) -> (exists x, ~Qin x h p)
  -> ((forall x, Ain x f <-> Qin x h p) \/ (forall x, Ain x f <-> ~ Qin x h p))
  -> exists a X' (f': X' -> set), 
    (forall z, Ain z f' <-> iin a z) \/ (forall z, Ain z f' <-> ~iin a z).
Proof.
  Require Import Coq.Logic.Classical_Prop.
  induction p; intros; simpl in *.
  - destruct H. tauto.
  - exists (h x). exists X. exists f. destruct H1.
    left; intro. rewrite<- H1. tauto. right; intro. rewrite<- H1. tauto.
  - destruct H. destruct H0. apply (IHp h X f). exists x0. apply NNPP. assumption.
    exists x. tauto. destruct H1. 
    right; intro. apply H1. left; intro.
    specialize H1 with x1. destruct (classic (Qin x h p)); tauto.
  - 
    (* specialize IHp1 with h { x: X & Qin (f x) h p1 } (fun k => f (projT1 k)).
    specialize IHp2 with h { x: X & Qin (f x) h p2 } (fun k => f (projT1 k)). *)
    destruct H, H0.
    destruct (not_or_and _ _ H0).

    destruct H1; destruct H.
    -- apply (IHp1 h { x: X & Qin (f x) h p1 } (fun k => f (projT1 k))).
        exists x. apply H. exists x0. apply H2.
        left. unfold Ain. split; intros.
        destruct H4. destruct x2. simpl in H4. apply (eeq_Qin H4). assumption.
        destruct (H1 x1). destruct (H6 (or_introl H4)).
        destruct (@eeq_Qin _ _ A p1 h (eeq_sym H7)).
        exists (existT _ x2 (H8 H4)). assumption.
    -- apply (IHp2 h { x: X & Qin (f x) h p2 } (fun k => f (projT1 k))).
        exists x. apply H. exists x0. apply H3.
        left. unfold Ain. split; intros.
        destruct H4. destruct x2. simpl in H4. apply (eeq_Qin H4). assumption.
        destruct (H1 x1). destruct (H6 (or_intror H4)).
        destruct (@eeq_Qin _ _ A p2 h (eeq_sym H7)).
        exists (existT _ x2 (H8 H4)). assumption.
    -- apply (IHp1 h { x: X & Qin (f x) h p1 /\ ~Qin (f x) h p2 } (fun k => f (projT1 k))).
        exists x. apply H. exists x0. apply H2.
        left. unfold Ain. split; intros.
        destruct H4, x2, a. simpl in H4.
        apply (eeq_Qin H4). apply NNPP. intro O.
        destruct (H1 (f x2)). cut (Ain (f x2) f).
        intro. destruct (H5 H7). tauto. unfold Ain. exists x2. apply eeq_refl.
        destruct (H1 x1). cut (Ain x1 f). intro.
        destruct H7.
        destruct (H6 (or_introl H4)).
        destruct (@eeq_Qin _ _ A p1 h (eeq_sym H7)).
        exists (existT _ x2 (H8 H4)). assumption.
    -- apply (IHp2 h { x: X & Qin (f x) h p2 } (fun k => f (projT1 k))).
        exists x. apply H. exists x0. apply H3.
        left. unfold Ain. split; intros.
        destruct H4. destruct x2. simpl in H4. apply (eeq_Qin H4). assumption.
        destruct (H1 x1). destruct (H6 (or_intror H4)).
        destruct (@eeq_Qin _ _ A p2 h (eeq_sym H7)).
        exists (existT _ x2 (H8 H4)). assumption.


    
    -- 
    apply (IHp1 h { x: X & Qin (f x) h p1 } (fun k => f (projT1 k))).
    exists x. apply H. exists x0. apply H2.
    left. unfold Ain. split; intros.
      destruct H4. destruct x2. simpl in H4. apply (eeq_Qin H4). assumption.
      

    unfold Ain. left; intros; split; intro. destruct H4; destruct x1. simpl in H4.
    apply (eeq_Qin H4). assumption.
    destruct (H0 x0). destruct (H6 (or_introl H4)).
    cut (Qin (f x1) h p1). intro.
    exists (existT _ x1 H8). apply H7. apply (eeq_Qin (eeq_sym H7)). assumption.

    apply (IHp2 (ex_intro (fun _: {x : X & Qin (f x) h p2} => True) (existT _ x H3) I)).
    unfold Ain. left; intros; split; intro. destruct H4; destruct x1. simpl in H4.
    apply (eeq_Qin H4). assumption.
    destruct (H0 x0). destruct (H6 (or_intror H4)).
    cut (Qin (f x1) h p2). intro.
    exists (existT _ x1 H8). simpl. apply H7. apply (eeq_Qin (eeq_sym H7)). assumption.

    pose proof (H1 (ex_intro _ x eeq_refl)).
    apply (IHp1 (ex_intro (fun _: {x : X & Qin (f x) h p1} => True) (existT _ x H3) I)).
    unfold Ain. left; intros; split; intro. destruct H4; destruct x1. simpl in H4.
    apply (eeq_Qin H4). assumption.
    destruct (H0 x0). destruct (H6 (or_introl H4)).
    cut (Qin (f x1) h p1). intro.
    exists (existT _ x1 H8). apply H7. apply (eeq_Qin (eeq_sym H7)). assumption.

    apply (IHp2 (ex_intro (fun _: {x : X & Qin (f x) h p2} => True) (existT _ x H3) I)).
    unfold Ain. left; intros; split; intro. destruct H4; destruct x1. simpl in H4.
    apply (eeq_Qin H4). assumption.
    destruct (H0 x0). destruct (H6 (or_intror H4)).
    cut (Qin (f x1) h p2). intro.
    exists (existT _ x1 H8). simpl. apply H7. apply (eeq_Qin (eeq_sym H7)). assumption.

    specialize IHp2 with h { x: X & Qin (f x) h p2 } (fun k => f (projT1 k)) .


    classical (Qin (f x) h).
    apply (IHp2 h X f H). destruct H.
    destruct H0.  left; intro. rewrite H0. admit. right; intro. rewrite H0. tauto.

    Definition mk_low {X} f h :=
    S False (Bot _) (False_rect _) { x: X & f (h x) } (fun k => h (projT1 k)). *)

(* Definition Aof {X} f :=
S False (Bot _) (False_rect _) X f.

Lemma Qin_False: forall z, 
  Qin z (False_rect set) (Bot False) = False.
Proof. unfold Qin. auto. Qed.

Lemma wow_empty {A p h X f}:
  (exists x: X, True) (* no! p must be non-empty *)
  -> (forall z, ~ iin z (S A p h X f))
  -> exists X' f', forall z, iin z (@Aof X' f').
Proof. revert h X f. induction p; intros.
  - admit.
  - Axiom add: set -> set -> set.
  exists (sum X X). pose (fun a => match a with inl a' => f a' | inr a'' => add (f a'') (h x) end) as g. exists g.
  intro z. pose proof (H0 z).
  unfold Aof.
  rewrite iin_unfold' in H1.
  rewrite iin_unfold'. rewrite Qin_False. apply Xor_AF.
  unfold Ain. setoid_rewrite<- negb_xor in H1. destruct H1.
  destruct H1. destruct H1. exists (inl x0). unfold g. assumption.
  pose proof (fun X => H2 X H1).
  unfold Qin in H1.
  
  specialize H0 with (add z (h x)).


Lemma wow_full {A p h X f}:
  (exists x: X, True)
  -> (forall z, iin z (S A p h X f))
  -> exists X' f', forall z, iin z (@Aof X' f').
Proof. revert h X f.
  induction p; intros; simpl iin in *.
  - exists X. exists f. intro z. specialize H0 with z.
  unfold Aof.
    rewrite iin_unfold' in H0.
    rewrite iin_unfold'.
    revert H0. apply Xor_eq. tauto.
    apply Qext. unfold Qeq, eeq_boolean. intros.
    repeat rewrite boolean_map_compose. simpl eval. tauto.
  - exists (sum X X). pose (fun a => match a with inl a' => f a' | inr a'' => f a'' end) as g. exists g.
    intro z. specialize H0 with z.
    unfold Aof.
    rewrite iin_unfold' in H0.
    rewrite iin_unfold'.
    admit.
  - 

Lemma wow_empty {A p h X f}:
  (forall z, ~ iin z (S A p h X f))
  -> forall z, ~ Ain z f /\ ~ Qin z h p.
Proof.
  setoid_rewrite iin_unfold'.
  intros. split; intro.
  

Lemma iin_eeq_aux1 {A p h X f A' p' h' X' f'}:
  let _ := eeq (S A p h X f) (S A' p' h' X' f') in
  (forall z : set,
  Xor (Ain z f) (Qin z h p) <-> Xor (Ain z f') (Qin z h' p'))
  -> forall z, Ain z f <-> Ain z f'.
Proof.
  intros. split; intro. admit.
  specialize H with z. unfold Xor in H. destruct H.
  cut (Qin z h' p' -> False). intro.
  destruct (H1 (conj (or_introl H0) (fun _ => H2))).
  destruct H3; auto.


Lemma iin_eeq: forall x y, 
  (forall z, iin z x <-> iin z y) -> x == y.
Proof.
  destruct x, y. rewrite eeq_unfold.
  setoid_rewrite iin_unfold'. intros.
  split.
  - apply Aext. intro z. specialize H with z.
    repeat rewrite iin_unfold' in H. *)
