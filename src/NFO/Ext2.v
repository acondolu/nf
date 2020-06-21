Add LoadPath "src/NFO/".
Require Import FunExt.
Require Import Bool.
Require Import Model.
Require Import Wff.
Require Import Eeq.
Require Import Iin.
Require Import Sets.
Require Import Xor.
Require Import Ext.

(* This file needs cleaning!!! *)

Lemma sloppy_Qext {A} {h: A -> set} {p : boolean A} {x y} :
  (forall i, iin (h i) y <-> iin (h i) x) -> Qin x h p -> Qin y h p.
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

Lemma sloppy_Aext {x y} {J X} {f: X -> set} {h: J -> set} {p : boolean J}:
  (forall x, Ain x f <-> Qin x h p)
  -> (forall i, iin (h i) y <-> iin (h i) x) -> Ain x f -> Ain y f.
Proof.
  intros H. repeat setoid_rewrite H. apply sloppy_Qext.
Qed.

Definition select {X Y} (f: X -> Y) (P: X -> Prop) : {x: X & P x} -> Y
  := fun x' => match x' with
      | existT _ x _ => f x
      end.

Definition respects_sig {A} (h: A -> set) (sig: A -> Prop) :=
  respects (fun a b => h a == h b) sig.
Definition completion A {B} (h: B -> set) := prod A { sig : B -> Prop & respects_sig h sig }.

Definition All {X Y} (f: X -> set) (h: Y -> set) : completion X h -> set :=
  fun pr => match f (fst pr) with
  | S A p h' X f =>  S A p h' _ (AXor f (select h (projT1 (snd pr))))
  end.

Lemma inv_sig_aux {X Y Z} {f: X -> set} {g: Y -> set} {h: Z -> set}:
  Aeq (AXor f g) h <-> Aeq f (AXor g h).
Proof.
  repeat setoid_rewrite Aext.
  repeat setoid_rewrite AXor_ok.
  setoid_rewrite<- (@Xor_neg _ (Ain _ h)).
  setoid_rewrite<- (@Xor_neg (Ain _ f) _).
  setoid_rewrite xor_assoc2.
  apply iff_refl.
Qed.

Lemma ing_sig_aux_2 {X Z sig sig'} {f: X -> set} {h: Z -> set}:
  respects_sig h sig -> respects_sig h sig'
-> Aeq
  (AXor (AXor f (select h sig)) (select h sig'))
  (AXor (select h (xorP sig' sig)) f).
Proof.
  intros A B.
  setoid_rewrite Aext. intro x.
  repeat setoid_rewrite AXor_ok.
  refine (iff_trans _ _).
  setoid_rewrite Xor_eq.
  apply iff_refl.
  repeat setoid_rewrite AXor_ok.
  apply iff_refl.
  apply iff_refl.
  refine (iff_trans _ _).
  apply (iff_sym xor_assoc2).
  refine (iff_trans _ _).
  apply xor_comm2.
  apply Xor_eq; try apply iff_refl.
  setoid_rewrite<- AXor_ok.
  apply Aext.
  (* NICE *)
  apply Aext. intro. rewrite AXor_ok.
  unfold Aeq, AXor, select. unfold xorP. unfold Ain. split; intros.
  destruct H, H.
  - destruct H, x1. cut (Xor (sig' x1) (sig x1)). intro.
  unfold xorP. exists (existT _ x1 H1). assumption. apply Xor_2. intro H'.
  apply (H0 (ex_intro _ (existT _ x1 H') H)).
  assumption.
  - destruct H0, x1. cut (Xor (sig' x1) (sig x1)). intro.
  unfold xorP. exists (existT _ x1 H1). assumption. apply Xor_1. assumption.
  intro H'. apply (H (ex_intro _ (existT _ x1 H') H0)).
  - destruct H, x1. destruct x2, H0.
  -- apply Xor_2.
      intro H'. destruct H', x2. pose proof (A x1 x2 (eeq_trans H (eeq_sym H2))). tauto.
      exists (existT _ x1 H0). assumption.
  -- apply Xor_1.
      exists (existT _ x1 H1). assumption.
      intro H'. destruct H', x2. pose proof (B x1 x2 (eeq_trans H (eeq_sym H2))). tauto.
Qed.

Lemma inv_sig {X X' J} {f: X -> set} {f': X' -> set} h {sig sig': J -> Prop}:
  respects_sig h sig -> respects_sig h sig'
  -> Aeq f (AXor (AXor f' (select h sig)) (select h sig'))
  -> Aeq (AXor f (select h (xorP sig' sig))) f'.
Proof.
  repeat rewrite inv_sig_aux.
  intros A B. intro. apply (fun X => Aeq_trans _ _ _ H X).
  apply (ing_sig_aux_2 A B).
Qed.

Lemma ain_aux {J h z i}:
Ain (h i) (fun y : {x : J & iin (h x) z} => let (x, _) := y in h x)
<-> iin (h i) z.
Proof.
  unfold Ain. split; intros.
  - destruct H, x. destruct (iin_respects_eeq z _ _ H). tauto.
  - exists (existT _ i H). apply eeq_refl.
Qed.

Local Lemma stupid_xor_aux {a b c d}:
  Xor (Xor (Xor a (Xor a b)) (Xor c d)) b <-> Xor c d.
Proof.
  refine (iff_trans _ _).
  refine (Xor_eq _ _).
  refine (Xor_eq _ _).
  refine (_ : _ <-> b).
  rewrite xor_assoc2. unfold Xor. tauto.
  apply iff_refl. apply iff_refl.
  refine (iff_trans _ _).
  refine (xor_comm2).
  unfold Xor. tauto.
Qed.

Lemma wow {J X} {f: X -> set} (h: J -> set) (p : boolean J):
(forall x, Ain x f <-> Qin x h p)
-> (exists x, Ain x f)
-> forall x, Ain x (All f h).
Proof.
  intros. destruct H0.
  pose (fun j => iin (h j) x0) as sig_x0 (* the good signature *) .
  pose (fun j => iin (h j) x) as sig_x (* the current signature *) .
  cut (respects_sig h sig_x0). cut (respects_sig h sig_x). intros R1 R2.

  pose x as was_x.
  destruct x.
  pose (S A p0 h0 _ (AXor (AXor f0 (select h sig_x)) (select h (sig_x0)))) as x_signed.
  pose proof (fun X => @sloppy_Aext _ x_signed _ _ f h p H X H0).
  cut ((forall i : J, iin (h i) x_signed <-> iin (h i) x0)). intro.
  destruct (H1 H2). clear H1 H2.
  pose (xorP sig_x0 sig_x) as sig_xor.
  cut (respects_sig h sig_xor). intro xr.
  exists (x, existT _ sig_xor xr).

  unfold All. unfold Ain. simpl.
  destruct (f x). unfold x_signed in H3. rewrite eeq_unfold in H3. destruct H3.
  rewrite eeq_unfold. split.
  - revert H1. apply (inv_sig h R1 R2).
  - exact H2.
  - apply xorP_respects; assumption.
  - unfold x_signed. intros. destruct x0. repeat rewrite iin_unfold'.
    unfold sig_x0, sig_x, select.
    (* Deep rewrites *)
    refine (iff_trans _ _).
    refine (Xor_eq _ _).
    repeat rewrite AXor_ok.
    refine (Xor_eq _ _).
    repeat rewrite AXor_ok.
    refine (Xor_eq _ _). apply iff_refl.
    apply ain_aux. apply ain_aux.
    apply iff_refl.

    refine (iff_trans _ _).
    refine (Xor_eq _ _).
    refine (Xor_eq _ _).
    refine (Xor_eq _ _).
    apply iff_refl.
    apply iin_unfold'. apply iin_unfold'.
    apply iff_refl.

    apply stupid_xor_aux.
  - unfold sig_x, respects_sig, respects. intros. apply (iin_respects_eeq _ (h x1) (h x')). auto.
  - unfold sig_x, respects_sig, respects. intros. apply (iin_respects_eeq x0 (h x1) (h x')). auto.
Qed.

Lemma not_iin_not_Ain {A p h X f}:
  (forall z, ~ iin z (S A p h X f)) -> forall x, ~ Ain x f.
Proof.
  setoid_rewrite iin_unfold'.
  setoid_rewrite Xor_neg.
  intros H x H0. pose proof (wow _ _ H).
  destruct (weak_regularity (enum (All f h)) (H1 (ex_intro _ x H0) _)).
Qed.

Lemma no_urelements: forall x y, is_empty (QXor x y) -> x == y.
Proof.
  intros x y. unfold is_empty.
  setoid_rewrite xor_ok. destruct x, y.
  intro. setoid_rewrite Xor_neg in H.
  setoid_rewrite iin_unfold' in H.
  setoid_rewrite<- Xor_neg in H.
  setoid_rewrite xor_pairs in H.
  setoid_rewrite Xor_neg in H.
  pose H as H'.
  setoid_rewrite<- AXor_ok in H'.
  setoid_rewrite<- QXor_ok in H'.
  setoid_rewrite<- Xor_neg in H'.
  setoid_rewrite<- iin_unfold' in H'.
  pose proof (not_iin_not_Ain H').
  rewrite eeq_unfold.
  setoid_rewrite AXor_ok in H0.
  pose H0 as H0'.
  setoid_rewrite Xor_neg in H0'.
  rewrite<- Aext in H0'.
  cut (forall z, ~Xor (Qin z h p) (Qin z h0 p0)). intro.
  setoid_rewrite Xor_neg in H1.
  setoid_rewrite<- Qext in H1.
  split; auto.
  intro z.
  specialize H with z. setoid_rewrite<- H. apply H0.
Qed.

Lemma iin_eeq: forall x y, 
  (forall z, iin z x <-> iin z y) -> x == y.
Proof.
  intros. pose proof (xor_ext H). apply no_urelements. auto.
Qed.

Theorem ext: forall x y, 
  x == y <-> forall z, iin z x <-> iin z y.
Proof.
  intros. split. apply eeq_iin. apply iin_eeq.
Qed.
