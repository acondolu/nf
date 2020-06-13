Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Wff.
Require Import Eeq.
Require Import Iin.

(* TODO: Prove extensionality *)

Lemma ext_easy: forall x y, eeq x y ->
  (forall z, iin z x <-> iin z y)
  /\ (forall z, iin x z <-> iin y z).
Proof.
  apply (@wf_two_ind (
    fun x y => eeq x y -> _ : Prop
  )).
  intros. split.
  * intro z. destruct x1, x2.
  repeat rewrite iin_unfold in *.
  rewrite eeq_def in H0.
  repeat destruct H0.
  unfold Xor.Xor. 
  split; split; destruct H3; destruct H3.
  - left. destruct H3. destruct (H0 x). exists x0.
    apply (eeq_trans (eeq_sym H5) H3).
  - right. unfold eeq_boolean in H1.
    pose proof (H1 (fun x => match x with inl a => iin (h a) z | inr b => iin (h0 b) z end)).
    repeat rewrite boolean_map_compose in H5.
    cut (respects
    (fun x : A + A0 =>
     match x with
     | inl a => iin (h a) z
     | inr b => iin (h0 b) z
     end) (sum_i eeq h h0)).
     --- admit.
     --- unfold respects. destruct x, x'; unfold sum_i.
          intro. apply H. apply AA; apply lt_h. assumption.
          intro. apply H. apply AB; apply lt_h. assumption.
          intro. apply H. apply BA; apply lt_h. assumption.
          intro. apply H. apply BB; apply lt_h. assumption.
Admitted.
(* TODO *)