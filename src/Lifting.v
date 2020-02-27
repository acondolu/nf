Require Import Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import Coq.Program.Equality.

Add LoadPath "src/".
Require Import Base.

Fixpoint lift {k} (y: set k) : set (S k) :=
  match y with
  | prop _ c => prop _ c
  | binop _ P y' y'' => binop _ P (lift y') (lift y'')
  | sin _ y' => sin _ (lift y')
  | cos _ y' => cos _ (lift y')
end.

Lemma smatch_lift_0: forall f g x, Base.smatch f g (lift x) = eval0 x.
Proof.
  intros. dependent induction x.
  -  auto.
  - simpl lift. rewrite Base.smatch_binop. rewrite Base.eval0_binop.
    rewrite (IHx1 x1). rewrite (IHx2 x2). auto. auto. auto. auto. auto.
Qed.

Theorem ambiguityEeq:
  forall i x y, Eeq i x y <-> Eeq _ (lift x) (lift y).
Proof.
  simple induction i.
  - dependent destruction x; dependent destruction y.
    -- simpl. unfold eq0. repeat rewrite eval0_prop.
       split; intros. repeat rewrite smatch_prop. auto.
      apply (H eval0 (fun _ => True)); intros; auto. split; auto.
    -- split; intros.
       --- simpl Eeq. intros. rewrite Base.smatch_prop. rewrite Base.smatch_binop.
        repeat rewrite smatch_lift_0. assumption.
       --- pose proof (H eval0 (fun _ => True)).
       repeat rewrite smatch_lift_0 in H0.
       unfold Eeq. unfold eq0. apply H0; intros; auto.
       unfold eq0. tauto.
    -- admit.
    -- admit.
  - intros.
Admitted. 

Theorem ambiguityIinR:
  forall i x y, Iin _ x (lift y) = IinS i x y
with ambiguityEeqL:
  forall i x y, Eeq _ x y = EeqS i (lift x) y.
Proof.
* intros.
  dependent induction x.
  - simpl. apply eq_refl.
  - rewrite Iin_binop. rewrite IinS_binop.
    apply f_equal2. 
    -- apply IHx1; auto.
    -- apply IHx2; auto.
  - rewrite Iin_sin. rewrite IinS_sin.
    rewrite ambiguityEeqL. auto.
  - admit.
* intros.
  induction i. simpl. admit. admit. 
  (* unfold EeqS. unfold eeqS. simpl Eeq.
  dependent induction y.
  - simpl. unfold Eeq.  apply eq_refl.
  - rewrite Iin_binop. rewrite IinS_binop.
    apply f_equal2. 
    -- apply IHx1; auto.
    -- apply IHx2; auto.
  - rewrite Iin_sin. rewrite IinS_sin.
    rewrite ambiguityEeqL. auto. *)
Admitted.

Theorem ambiguityEeqR:
  forall i x y, Eeq _ x (lift y) = EeqS i x y.
Proof.
  intros.
  induction i.
  - dependent induction y.
    --
    (* pose proof (IHy1 y1 eq_refl). simpl. unfold EeqS.
        unfold eeq. unfold eeqS.
        
       simpl lift. simpl Eeq.
       simpl in H. *)
Admitted.

(* Theorem ambiguityEeqL:
  forall i x y, Eeq _ x y <-> EeqS i (lift x) y.
Proof.
  intros.
  induction i.
  - simpl. unfold EeqS. simpl. unfold eeqS. unfold IimS. unfold Eeq. dependent induction x.
    -- cbv. tauto.
Admitted. *)