From Calculus.Chapter18 Require Import Prelude.

Lemma problem_18_37 : ∀ f,
  ⟦ der ⟧ f = f ->
  (∀ x y, f (x + y)= f x * f y) ->
  f = exp \/ f = λ _, 0.
Proof.
  intros f H1 H2. 
  pose proof theorem_18_5 f f H1 ltac:(intros x; reflexivity) as [c H3].
  specialize (H2 0).
  assert (H4 : ∀ x, f x = 0 \/ f 0 = 1).
  {
    intros x.
    specialize (H2 x). 
    rewrite Rplus_0_l in H2.
    nra.
  }
  assert (c = 1 \/ c <> 1) as [H5 | H5] by lra.
  - left. subst. extensionality x. rewrite exp_Rpower. specialize (H3 x). lra.
  - right. extensionality x. specialize (H2 x). rewrite Rplus_0_l in H2.
    specialize (H4 x) as [H4 | H4]; auto.
    specialize (H3 0). rewrite <- exp_Rpower, exp_0 in H3. rewrite H4, Rmult_1_r in H3.
    exfalso. apply H5. symmetry in H3. apply H3.
Qed.