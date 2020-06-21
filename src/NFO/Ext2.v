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

Definition subsetOf {X} (f: X -> set) (P: X -> Prop)
  : { x: X & P x} -> set
  := fun x' => match x' with
      | existT _ x _ => f x
      end.

Definition Para (A B: Type) := prod A (B -> Prop).

Definition All {X Y} (f: X -> set) (h: Y -> set) : Para X Y -> set :=
  fun pr => match f (fst pr) with
  | S A p h' X f =>  S A p h' _ (AXor f (subsetOf h (snd pr)))
  end.

Lemma inv_sig_aux {X Y Z} {f: X -> set} {g: Y -> set} {h: Z -> set}:
Aeq (AXor f g) h
<-> 
Aeq f (AXor g h).
Proof.
Admitted.

Lemma ing_sig_aux_2 {X Z sig sig'} {f: X -> set} {h: Z -> set}:
Aeq
  (AXor (AXor f (subsetOf h sig)) (subsetOf h sig'))
  (AXor (subsetOf h (fun z => Xor (sig' z) (sig z))) f).
Proof.
  repeat rewrite<- inv_sig_aux.
Admitted.

Lemma inv_sig {X X' J} {f: X -> set} {f': X' -> set} h {sig sig': J -> Prop}:
Aeq f (AXor (AXor f' (subsetOf h sig)) (subsetOf h sig'))
-> 
Aeq (AXor f (subsetOf h (fun j : J => Xor (sig' j) (sig j)))) f'.
Proof.
  repeat rewrite inv_sig_aux.

Admitted.

Lemma ain_aux {J h z i}:
Ain (h i) (fun y : {x : J & iin (h x) z} => let (x, _) := y in h x)
<-> iin (h i) z.
Proof.
  unfold Ain. split; intros.
  - destruct H, x. destruct (iin_respects_eeq z _ _ H). tauto.
  - exists (existT _ i H). apply eeq_refl.
Qed.

Lemma stupid_xor_aux {a b c d}:
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

  pose x as was_x.
  destruct x.
  pose (S A p0 h0 _ (AXor (AXor f0 (subsetOf h sig_x)) (subsetOf h (sig_x0)))) as x_signed.
  pose proof (fun X => @sloppy_Aext _ x_signed _ _ f h p H X H0).
  cut ((forall i : J, iin (h i) x_signed <-> iin (h i) x0)). intro.
  destruct (H1 H2). clear H1 H2.
  exists (x, (fun j => Xor (sig_x0 j) (sig_x j))).

  unfold All. unfold Ain. simpl.
  destruct (f x). unfold x_signed in H3. rewrite eeq_unfold in H3. destruct H3.
  rewrite eeq_unfold. split.
  - revert H1. apply inv_sig.
  - exact H2.
  - unfold x_signed. intros. destruct x0. repeat rewrite iin_unfold'.
    unfold sig_x0, sig_x, subsetOf.
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
Qed.
