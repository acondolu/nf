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

(** Extensionally empty sets: *)
Definition ext_empty s := forall t, ~ IN t s.

(** Two sets are extensionally equal iff their XOR is
    extensionally empty:
*)
Lemma xor_ext: forall {s s'},
  (forall t, IN t s <-> IN t s') <-> ext_empty (s ^^^ s').
Proof.
  intros.
  unfold ext_empty.
  setoid_rewrite xor_ok.
  setoid_rewrite xor_neg.
  apply iff_refl.
Qed.

(** TODO: define "paradoxical set := urelement" in the article (a set where the A-part has the same extension as the B-part, i.e. it's extensionally empty, but it's different from the empty set, i.e. has non-empty (and with same extension) parts ) *)

Lemma weak_regularity s :
  match s with S _ _ f _ _ => AIN s f -> False end.
Proof.
  induction s. intros. unfold AIN in H1. destruct H1.
  pose proof (H x). assert (H1' := H1). destruct (f x) in H1, H2.
  apply H2. unfold AIN. assert (H1'' := H1).
  rewrite EQ_unfold in H1. destruct H1, H1.
  destruct (H4 x). exists x0. eauto with Eeq.
Qed.

(** * ? *)

(** B-sets have the following property: if two sets agree (or not) on the sets enumerated by 'g', then the B-set agrees on them. *)
Lemma sloppy_Bext {Y} {g: Y -> SET} {e : BExpr} {s s'} :
  (forall y, IN (g y) s' <-> IN (g y) s)
    -> BIN s (map g e) -> BIN s' (map g e).
Proof.
  revert s s'. induction e; simpl; intros.
  - destruct H0.
  - specialize H with x. tauto.
  - intro. apply H0. apply (fun X => IHe s' s X H1). intro y.
    specialize H with y. tauto.
  - destruct H0.
  -- left. apply (IHe1 s s' H H0).
  -- right. apply (IHe2 s s' H H0).
Qed.

(** In case a A-set is extensionally equal to a B-set, the
    same holds for the A-set: it cannot distinguish between
    sets that agree on the image of 'g'. *)
Lemma sloppy_Aext {X Y} {f: X -> SET} {g: Y -> SET} {e s s'}:
  (forall t, AIN t f <-> BIN t (map g e))
  -> (forall y, IN (g y) s' <-> IN (g y) s)
  -> AIN s f -> AIN s' f.
Proof.
  intros H. repeat setoid_rewrite H. apply sloppy_Bext.
Qed.

Lemma AEQ_AXor_assoc {X Y Z}
  {f: X -> SET} {g: Y -> SET} {h: Z -> SET}
  : AEQ (AXor f g) h <-> AEQ f (AXor g h).
Proof.
  repeat setoid_rewrite Aext.
  repeat setoid_rewrite AXor_ok.
  setoid_rewrite<- (@xor_neg _ (AIN _ h)).
  setoid_rewrite<- (@xor_neg (AIN _ f) _).
  setoid_rewrite xor_assoc.
  apply iff_refl.
Qed.

Lemma AEQ_AXor_select {Y}
  (f: Y -> SET) (P Q: Y -> Prop)
  : respects (EQ ⨀ f) P
    -> respects (EQ ⨀ f) Q
      -> AEQ
          (select f P ^A^ select f Q)
          (select f (Q ^^ P)).
Proof.
  intros. apply Aext. intro. rewrite AXor_ok.
  unfold AEQ, AXor, select. unfold xorP. unfold AIN.
  setoid_rewrite (ex_T P (fun X => f X == x)).
  setoid_rewrite (ex_T Q (fun X => f X == x)).
  setoid_rewrite (ex_T (Q ^^ P) (fun X => f X == x)).
  split; intros. 
  - destruct H1, H1. clear H H0.
  -- destruct H1. exists x0. unfold xorP. firstorder.
  -- destruct H2. exists x0. unfold xorP. firstorder.
  - destruct H1, H1. setoid_rewrite<- H2. destruct H1, H1.
  -- right. split. intro. destruct H4, H4. firstorder. firstorder.
  -- left. split. firstorder. intro. destruct H4, H4. firstorder.
Qed.

Definition completion {X} A (f: X -> SET) :=
  prod A { P: X -> Prop & respects (EQ ⨀ f) P }.

(* Enumerates all sets, under the hypothesis that there exists a paradoxical set *)
Definition All {X Y} (f: X -> SET) (g: Y -> SET)
  : completion X g -> SET :=
  fun c => match c with (x, (existT _ P _)) =>
    match f x with
    | S _ _ f' g' e' =>  S _ _ (AXor f' (select g P)) g' e'
    end
  end.

Lemma inv_sig {X X' Y}
  {f: X -> SET} {f': X' -> SET} {P Q: Y -> Prop} g
  : respects (EQ ⨀ g) P
  -> respects (EQ ⨀ g) Q
  -> AEQ f (AXor (AXor f' (select g P)) (select g Q))
  -> AEQ (AXor f (select g (Q ^^ P))) f'.
Proof.
  repeat rewrite AEQ_AXor_assoc.
  intros A B. intro. apply (fun X => AEQ_trans _ _ _ H X).
  setoid_rewrite Aext. intro x.
  repeat setoid_rewrite AXor_ok.
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
  
  apply AEQ_AXor_select; assumption.
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

Lemma universal_low {X Y} {f: X -> SET} (g: Y -> SET) (e: BExpr):
  (forall s, AIN s f <-> BIN s (map g e))
  -> (exists s, AIN s f)
  -> forall s, AIN s (All f g).
Proof.
  intros. destruct H0 as [t H0].
  pose (fun y => IN (g y) t) as sig_t (* the good signature *) .
  pose (fun y => IN (g y) s) as sig_s (* the current signature *) .
  cut (respects (EQ ⨀ g) sig_t).
  cut (respects (EQ ⨀ g) sig_s). intros R1 R2.

  destruct s.
  pose (S _ _ (AXor (AXor f0 (select g sig_s)) (select g sig_t)) g0 e0) as s_signed.
  cut (forall y, IN (g y) s_signed <-> IN (g y) t). intro H1.
  destruct (@sloppy_Aext _ _ f g e _ s_signed H H1 H0).
  pose (sig_t ^^ sig_s) as sig_xor.
  cut (respects (EQ ⨀ g) sig_xor). intro xr.
  exists (x, existT _ sig_xor xr).

  unfold All. unfold AIN. simpl.
  destruct (f x). unfold s_signed in H2. rewrite EQ_unfold in H2. destruct H2.
  rewrite EQ_unfold. split.
  - revert H2. apply (inv_sig g R1 R2).
  - assumption.
  - apply xorP_respects; assumption.
  - intros. destruct t.
    unfold s_signed, sig_t, sig_s, select.
    repeat rewrite IN_unfold.
    (* Deep rewrites *)
    repeat setoid_rewrite AXor_ok.
    setoid_rewrite (AIN_select g (fun X => IN X (S _ _ f0 g0 e0))).
    setoid_rewrite (AIN_select g (fun X => IN X (S _ _ f1 g1 e1))).
    setoid_rewrite IN_unfold.
    cut (forall y, (exists y', g y' == g y) <-> True). intro.
     setoid_rewrite H1.
     setoid_rewrite and_true.
     apply trivial_xor_lemma.
     intro. split; intros; auto. exists y0. reflexivity.
   unfold sig_s, respects. intros.
    apply (IN_respects_EQ _ _ _ H1).
   unfold sig_s, respects. intros.
    apply (IN_respects_EQ _ _ _ H1).
  - unfold sig_s, respects. intros.
  apply (IN_respects_EQ _ _ _ H1).
  -unfold sig_s, respects. intros.
  apply (IN_respects_EQ _ _ _ H1). 
Qed.

Lemma not_IN_not_AIN {X Y f g e}:
  ext_empty (S X Y f g e) -> forall x, ~ AIN x f.
Proof.
  unfold ext_empty.
  setoid_rewrite IN_unfold.
  setoid_rewrite xor_neg.
  intros H x H0. pose proof (universal_low _ _ H).
  destruct (weak_regularity (enum (All f g)) (H1 (ex_intro _ x H0) _)).
Qed.


Lemma no_urelements: forall x, ext_empty x -> x == emptyset.
Proof.
  destruct x. intro. pose proof (not_IN_not_AIN H).
  unfold emptyset, enum. setoid_rewrite EQ_unfold.
  unfold ext_empty in H. setoid_rewrite IN_unfold in H.
  setoid_rewrite xor_neg in H. pose H0 as H0'.
  setoid_rewrite H in H0'. split.
  - rewrite Aext. firstorder.
  - rewrite Bext. firstorder.
Qed.

(* As a consequence of the  *)
Lemma IN_EQ: forall x y, 
  (forall z, IN z x <-> IN z y) -> x == y.
Proof.
  intros. apply xor_empty. apply no_urelements. apply xor_ext. assumption.
Qed.

(** We can finally prove extensionality of NFO sets: *)
Theorem ext:
  forall x y, x == y <-> forall z, IN z x <-> IN z y.
Proof.
  intros. split. intro H. setoid_rewrite H. tauto. apply IN_EQ.
Qed.
