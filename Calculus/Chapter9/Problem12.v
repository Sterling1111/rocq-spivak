From Calculus.Chapter9 Require Import Prelude.

Section CarSpeedLimit.

Variable L : R -> R.
Variable a b a' b' : R -> R.

Hypothesis H1 : ⟦ der ⟧ a = a'.
Hypothesis H2 : ⟦ der ⟧ b = b'.
Hypothesis H3 : forall t, a' t = L (a t).

Lemma lemma_9_12_b :
  (forall t, b t = a (t - 1)) ->
  (forall t, b' t = L (b t)).
Proof.
  intros H4 t.
  assert (H5 : ⟦ der ⟧ b = (fun x => a' (x - 1))).
  {
    apply derivative_eq with (f1 := fun x => a (x - 1)).
    - intros x. symmetry. apply H4.
    - apply derivative_shift. apply H1.
  }
  assert (H6 : b' t = a' (t - 1)).
  {
    pose proof (derivative_unique b b' (fun x => a' (x - 1)) H2 H5) as H6.
    rewrite H6. reflexivity.
  }
  rewrite H6, H3, <- H4. reflexivity.
Qed.

Variable c : R.

Lemma lemma_9_12_c :
  (forall t, b t = a t - c) ->
  (forall t, b' t = L (b t)) ->
  (forall t, L (a t) = L (a t - c)).
Proof.
  intros H4 H5 t.
  assert (H6 : ⟦ der ⟧ b = a').
  {
    apply derivative_eq with (f1 := fun x => a x - c).
    - intros x. symmetry. apply H4.
    - apply derivative_ext with (f1' := fun x => a' x - 0).
      + intros x. lra.
      + apply (derivative_minus a (fun _ => c) a' (fun _ => 0) H1 (derivative_const c)).
  }
  assert (H7 : b' t = a' t).
  {
    pose proof (derivative_unique b b' a' H2 H6) as H7.
    rewrite H7. reflexivity.
  }
  rewrite <- H3, <- H7, H5, H4. reflexivity.
Qed.

End CarSpeedLimit.