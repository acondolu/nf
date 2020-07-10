(** * NFO.Ext : Extensionality of NFO sets *)
(** This module proves extensionality, i.e. that two sets are equivalent
    if and only they have the same elements.
*)

(* begin hide *)
Add LoadPath "src".
From Internal Require Import Misc FunExt.
From NFO Require Import BoolExpr Model Wf Eq In Sets Xor Morphism.
(* end hide *)



(** TODO: This file needs cleaning!!! *)

(** * ? *)

Definition ext_empty x := forall z, ~ iin z x.

Lemma xor_ext: forall {x y},
  (forall z, iin z x <-> iin z y) <-> ext_empty (x ^^^ y).
Proof.
  intros.
  unfold ext_empty.
  setoid_rewrite xor_ok.
  setoid_rewrite xor_neg.
  apply iff_refl.
Qed.

Lemma weak_regularity x :
  match x with S _ _ f _ _ => Ain x f -> False end.
Proof.
  induction x. intros. unfold Ain in H1. destruct H1.
  pose proof (H x). assert (H1' := H1). destruct (f x) in H1, H2.
  apply H2. unfold Ain. assert (H1'' := H1).
  rewrite eeq_unfold in H1. destruct H1, H1.
  destruct (H4 x). exists x0. eauto with Eeq.
Qed.

(** * ? *)

(** B-sets have the following property: if two sets agree (or not) on the sets enumerated by 'h', then the B-set agrees on them. *)
Lemma sloppy_Qext {J} {b: J -> set} {p : boolean} {x y} :
  (forall i, iin (b i) y <-> iin (b i) x) -> Qin x b p -> Qin y b p.
Proof.
  revert x y. induction p; simpl; intros.
  - destruct H0.
  - specialize H with x. tauto.
  - intro. apply H0. apply (fun X => IHp y x X H1). intro i.
    specialize H with i. tauto.
  - destruct H0.
  -- left. apply (IHp1 x y H H0).
  -- right. apply (IHp2 x y H H0).
Qed.

(** In case a A-set is extensionally equal to a B-set, the
    same holds for the A-set: it cannot distinguish between
    sets that agree on the image of 'h'. *)
Lemma sloppy_Aext {J X} {f: X -> set} {h: J -> set} {p x y}:
  (forall x, Ain x f <-> Qin x h p)
  -> (forall i, iin (h i) y <-> iin (h i) x) -> Ain x f -> Ain y f.
Proof.
  intros H. repeat setoid_rewrite H. apply sloppy_Qext.
Qed.

Lemma Aeq_AXor_assoc {X Y Z} {f: X -> set} {g: Y -> set} {h: Z -> set}:
  Aeq (AXor f g) h <-> Aeq f (AXor g h).
Proof.
  repeat setoid_rewrite Aext.
  repeat setoid_rewrite AXor_ok.
  setoid_rewrite<- (@xor_neg _ (Ain _ h)).
  setoid_rewrite<- (@xor_neg (Ain _ f) _).
  setoid_rewrite xor_assoc.
  apply iff_refl.
Qed.

Lemma Aeq_AXor_select {Y} (h: Y -> set) sig sig' :
  respects (eeq ⨀ h) sig
    -> respects (eeq ⨀ h) sig'
      -> Aeq
          (select h sig ^A^ select h sig')
          (select h (sig' ^^ sig)).
Proof.
  intros. apply Aext. intro. rewrite AXor_ok.
  unfold Aeq, AXor, select. unfold xorP. unfold Ain.
  setoid_rewrite (ex_T sig (fun X => h X == x)).
  setoid_rewrite (ex_T sig' (fun X => h X == x)).
  setoid_rewrite (ex_T (sig' ^^ sig) (fun X => h X == x)).
  split; intros. 
  - destruct H1, H1. clear H H0.
  -- destruct H1. exists x0. unfold xorP. firstorder.
  -- destruct H2. exists x0. unfold xorP. firstorder.
  - destruct H1, H1. setoid_rewrite<- H2. destruct H1, H1.
  -- right. split. intro. destruct H4, H4. firstorder. firstorder.
  -- left. split. firstorder. intro. destruct H4, H4. firstorder.
Qed.

Definition completion A {B} (h: B -> set) :=
  prod A { sig : B -> Prop & respects (eeq ⨀ h) sig }.

(* Enumerates all sets, under the hypothesis that there exists a paradoxical set *)
Definition All {X Y} (f: X -> set) (h: Y -> set)
  : completion X h -> set :=
  fun c =>
    let (x, resp) := c in
    let (sig, _) := resp in
    match f x with
    | S X Y f g e =>  S _ Y (AXor f (select h sig)) g e
    end.

Lemma inv_sig {X X' J} {f: X -> set} {f': X' -> set} h {sig sig': J -> Prop}:
  respects (eeq ⨀ h) sig -> respects (eeq ⨀ h) sig'
  -> Aeq f (AXor (AXor f' (select h sig)) (select h sig'))
  -> Aeq (AXor f (select h (sig' ^^ sig))) f'.
Proof.
  repeat rewrite Aeq_AXor_assoc.
  intros A B. intro. apply (fun X => Aeq_trans _ _ _ H X).
  (* apply (ing_sig_aux_2 A B). *)
  (* intros A B. *)
  setoid_rewrite Aext. intro x.
  repeat setoid_rewrite AXor_ok.
  (* setoid_rewrite<- xor_assoc.
  setoid_rewrite xor_comm. *)
  refine (iff_trans _ _).
  setoid_rewrite xor_iff.
  apply iff_refl.
  repeat setoid_rewrite AXor_ok.
  apply iff_refl.
  apply iff_refl.
  refine (iff_trans _ _).
  apply (iff_sym (xor_assoc _ _ _)).
  refine (iff_trans _ _).
  apply xor_comm.
  apply xor_iff; try apply iff_refl.
  setoid_rewrite<- AXor_ok.
  apply Aext.
  
  apply Aeq_AXor_select; assumption.
Qed.

Local Lemma trivial_xor_lemma {a b c d}:
  ((a ⊻ (a ⊻ b)) ⊻ (c ⊻ d)) ⊻ b <-> c ⊻ d.
Proof.
  repeat setoid_rewrite xor_assoc.
  setoid_rewrite xor_absorb.
  setoid_rewrite xor_comm.
  setoid_rewrite xor_false_l.
  setoid_rewrite xor_assoc.
  setoid_rewrite xor_assoc.
  setoid_rewrite xor_absorb.
  setoid_rewrite xor_false_l.
  setoid_rewrite xor_comm.
  apply xor_comm.
Qed.

Lemma universal_low {J X} {f: X -> set} (h: J -> set) (p : boolean):
  (forall x, Ain x f <-> Qin x h p)
  -> (exists x, Ain x f)
  -> forall x, Ain x (All f h).
Proof.
  intros. destruct H0.
  pose (fun j => iin (h j) x0) as sig_x0 (* the good signature *) .
  pose (fun j => iin (h j) x) as sig_x (* the current signature *) .
  cut (respects (eeq ⨀ h) sig_x0). cut (respects (eeq ⨀ h) sig_x). intros R1 R2.

  destruct x.
  pose (S _ Y (AXor (AXor f0 (select h sig_x)) (select h (sig_x0))) g e) as x_signed.
  pose proof (fun X => @sloppy_Aext _ _ f h p _ x_signed H X H0).
  cut ((forall i : J, iin (h i) x_signed <-> iin (h i) x0)). intro.
  destruct (H1 H2). clear H1 H2.
  pose (sig_x0 ^^ sig_x) as sig_xor.
  cut (respects (eeq ⨀ h) sig_xor). intro xr.
  exists (x, existT _ sig_xor xr).

  unfold All. unfold Ain. simpl.
  destruct (f x). unfold x_signed in H3. rewrite eeq_unfold in H3. destruct H3.
  rewrite eeq_unfold. split.
  - revert H1. apply (inv_sig h R1 R2).
  - exact H2.
  - apply xorP_respects; assumption.
  - intros. destruct x0.
    unfold x_signed, sig_x0, sig_x, select.
    repeat rewrite iin_unfold.
    (* Deep rewrites *)
    repeat setoid_rewrite AXor_ok.
    setoid_rewrite (Ain_select h (fun X => iin X (S X0 Y f0 g e))).
    setoid_rewrite (Ain_select h (fun X => iin X (S X1 Y0 f1 g0 e0))).
    setoid_rewrite iin_unfold.
    cut (forall i, (exists x : J, h x == h i) <-> True). intro.
     setoid_rewrite H2.
     setoid_rewrite and_true.
     apply trivial_xor_lemma.
     intro. split; intros; auto. exists i0. reflexivity.
   unfold sig_x, respects. intros.
    apply (iin_respects_eeq _ _ _ H2).
   unfold sig_x, respects. intros.
    apply (iin_respects_eeq _ _ _ H2).
  -unfold sig_x, respects. intros.
  apply (iin_respects_eeq _ _ _ H1).
  -unfold sig_x, respects. intros.
  apply (iin_respects_eeq _ _ _ H1). 
Qed.

Lemma not_iin_not_Ain {X Y f g e}:
  ext_empty (S X Y f g e) -> forall x, ~ Ain x f.
Proof.
  unfold ext_empty.
  setoid_rewrite iin_unfold.
  setoid_rewrite xor_neg.
  intros H x H0. pose proof (universal_low _ _ H).
  destruct (weak_regularity (enum (All f g)) (H1 (ex_intro _ x H0) _)).
Qed.


Lemma no_urelements: forall x, ext_empty x -> x == emptyset.
Proof.
  destruct x. intro. pose proof (not_iin_not_Ain H).
  unfold emptyset, enum. setoid_rewrite eeq_unfold.
  unfold ext_empty in H. setoid_rewrite iin_unfold in H.
  setoid_rewrite xor_neg in H. pose H0 as H0'.
  setoid_rewrite H in H0'. split.
  - rewrite Aext. firstorder.
  - rewrite Qext. firstorder.
Qed.

(* As a consequence of the  *)
Lemma iin_eeq: forall x y, 
  (forall z, iin z x <-> iin z y) -> x == y.
Proof.
  intros. apply xor_empty. apply no_urelements. apply xor_ext. assumption.
Qed.

(** We can finally prove extensionality of NFO sets: *)
Theorem ext:
  forall x y, x == y <-> forall z, iin z x <-> iin z y.
Proof.
  intros. split. intro H. setoid_rewrite H. tauto. apply iin_eeq.
Qed.
