(** * NFO.Ext : Extensionality of NFO sets *)
(** This module proves extensionality, i.e. that two sets are equivalent
    if and only they have the same elements.
*)

(* begin hide *)
Add LoadPath "src".
From Internal Require Import Misc FunExt.
From NFO Require Import BoolExpr Model Wf Eq In Sets Xor Morphism.
(* end hide *)

(** Set with empty extension: *)
Definition ext_empty s := forall t, ~ IN t s.

(** Two sets are extensionally equal iff their XOR has
    empty extension:
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

(** B-sets have the following property: if two sets agree (or not) on the sets enumerated by 'g', then the B-set agrees on them. *)
Lemma sloppy_Bext {Y} {g: Y -> SET} {e: BExpr} {s s'} :
  (forall y, IN (g y) s <-> IN (g y) s')
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
  -> (forall y, IN (g y) s <-> IN (g y) s')
  -> AIN s f -> AIN s' f.
Proof.
  intros H. repeat setoid_rewrite H. apply sloppy_Bext.
Qed.

Definition X_univ {Y} X (g: Y -> SET) :=
  prod X { P: Y -> Prop & respects (EQ ⨀ g) P }.

(* Enumerates all sets, under the hypothesis that there exists a paradoxical set *)
Definition f_univ {X Y} (f: X -> SET) (g: Y -> SET)
  : X_univ X g -> SET :=
  fun c => match c with (x, existT _ P _) =>
    match f x with
    | S _ _ f' g' e' =>  S _ _ (f' ^A^ select g P) g' e'
    end
  end.



Lemma AIN_AXOR_select {Y} (g: Y -> _) (P Q: Y -> Prop) s :
  respects (EQ ⨀ g) P
  -> respects (EQ ⨀ g) Q
  -> AIN s (select g (P ^^ Q))
  <-> AIN s (select g P) ⊻ AIN s (select g Q).
Proof.
  unfold AIN, select, AXor.
  setoid_rewrite (ex_T (P ^^ Q) (fun y => g y == s)).
  setoid_rewrite (ex_T P (fun y => g y == s)).
  setoid_rewrite (ex_T Q (fun y => g y == s)).
  unfold xorP. split; intro. (* Brute force proof...: *)
  - destruct H1, H1, H1, H1. left. split. firstorder. intro. apply H3. destruct H4, H4. apply (H0 x0 x). red. transitivity s; auto. symmetry. auto. auto.
  -- right. split. intro. destruct H4, H4. apply H1. apply (H x0 x). red. transitivity s; auto. symmetry. auto. auto. firstorder.
  - destruct H1, H1. destruct H1. exists x. destruct H1. split; auto. left. split; auto. intro. apply H2. exists x. tauto.
  destruct H2, H2. exists x. split; auto. right. split; auto. intro. apply H1. exists x. split; auto.
Qed.

Lemma universal_low {X Y} {f: X -> SET} (g: Y -> SET) (e: BExpr):
  (forall s, AIN s f <-> BIN s (map g e))
  -> (exists t, AIN t f)
  -> forall s, AIN s (f_univ f g).
Proof.
  intros. destruct H0 as [t H0].

  (* Get the signatures *)
  pose (fun y => IN (g y) t) as sig_t (* the good signature *) .
  pose (fun y => IN (g y) s) as sig_s (* the current signature *) .
  cut (respects (EQ ⨀ g) sig_t).
  cut (respects (EQ ⨀ g) sig_s). intros Rs Rt.
  pose (sig_s ^^ sig_t) as sig_xor.
  cut (respects (EQ ⨀ g) sig_xor). intro Rx.

  destruct s.
  pose (S _ _ (AXor f0 (select g sig_xor)) g0 e0) as s_signed.
  cut (forall y, IN (g y) t <-> IN (g y) s_signed). intro H1.

  (* Ok, begin: *)
  destruct (@sloppy_Aext _ _ f g e _ s_signed H H1 H0).

  exists (x, existT _ _ Rx).
  unfold f_univ, AIN.
  destruct (f x). unfold s_signed in H2. rewrite EQ_unfold in H2.
  destruct H2. rewrite EQ_unfold. split; auto.
  - revert H2.
    setoid_rewrite Aext.
    setoid_rewrite AXor_ok.
    intros. specialize H2 with x0. revert H2.
    clear; classic (AIN x0 f1); classic (AIN x0 f0);
       classic (AIN x0 (select g sig_xor)); autorewrite with xor log; tauto.
  - (* Prove that t and s_signed have the same signature *)
    intros. destruct t. unfold s_signed.
    repeat rewrite IN_unfold.
    repeat setoid_rewrite AXor_ok.
    pose proof (AIN_AXOR_select g sig_s sig_t) as H1.
    fold sig_xor in H1.
    setoid_rewrite (H1 _ Rs Rt).
    unfold sig_s, sig_t.
    setoid_rewrite (AIN_select g (fun X => IN X (S _ _ f0 g0 e0))).
    setoid_rewrite (AIN_select g (fun X => IN X (S _ _ f1 g1 e1))).
    cut (forall y, (exists y', g y' == g y) <-> True). intro.
    setoid_rewrite H2.
    setoid_rewrite IN_unfold.
    setoid_rewrite and_true.
    clear;
      classic (AIN (g y) f1);
        classic (AIN (g y) f0);
          classic (BIN (g y) (map g1 e1));
            classic (BIN (g y) (map g0 e0));
              autorewrite with xor log; tauto.
    (* Trivial rewrite lemma *)
    split; intro; auto. exists y0. reflexivity.
   (* Signature respects EQ (s) *)
   unfold respects. intros. apply (IN_respects_EQ _ _ _ H2).
   (* Signature respects EQ (t) *)
   unfold respects. intros. apply (IN_respects_EQ _ _ _ H2).
  - (* Respects (sig_xor) *)
    unfold sig_xor, respects, sig_s, sig_t, xorP. intros.
    red in H1. setoid_rewrite H1. apply iff_refl.
  - (* Respects (sig_s) *)
    unfold sig_s, respects, xorP. intros.
    red in H1. setoid_rewrite H1. apply iff_refl.
  - (* Respects (sig_t) *)
    unfold sig_t, respects, xorP. intros.
    red in H1. setoid_rewrite H1. apply iff_refl.
Qed.

Lemma not_IN_not_AIN {X Y f g e}:
  ext_empty (S X Y f g e) -> forall x, ~ AIN x f.
Proof.
  unfold ext_empty.
  setoid_rewrite IN_unfold.
  setoid_rewrite xor_neg.
  intros H x H0. pose proof (universal_low _ _ H).
  destruct (weak_regularity (enum (f_univ f g)) (H1 (ex_intro _ x H0) _)).
Qed.


Lemma no_urelements: forall x, ext_empty x -> x == emptyset.
Proof.
  destruct x. intro. pose proof (not_IN_not_AIN H).
  unfold ext_empty in H. setoid_rewrite IN_unfold in H.
  setoid_rewrite xor_neg in H. pose H0 as H0'.
  setoid_rewrite H in H0'.
  unfold emptyset, enum. setoid_rewrite EQ_unfold. split.
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
