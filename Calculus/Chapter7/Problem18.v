From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_18 : ∀ f,
  continuous f ->
  (∀ x, f x > 0) ->
  ⟦ lim ∞ ⟧ f = 0 ->
  ⟦ lim -∞ ⟧ f = 0 ->
  ∃ y, ∀ x, f y >= f x.
Proof.
  intros f H1 H2 H3 H4.

  specialize (H3 (f 0) ltac:(auto)) as [N1 H3].
  specialize (H4 (f 0) ltac:(auto)) as [N2 H4].

  set (b := Rmax (|N1|) (|N2|) + 1).

  assert (H5 : forall x, |x| > b -> f x < f 0).
  {
    intros x H5.
    apply Raux.Rabs_gt_inv in H5 as [H5 | H5].
    - specialize (H4 x); unfold b in *; solve_R.
    - specialize (H3 x); unfold b in *; solve_R.
  }

  pose proof (continuous_on_interval_attains_maximum f (-b) b
    ltac:(unfold b; solve_R)
    ltac:(apply continuous_imp_continuous_on; auto)) as [y [_ H8]].
  
  exists y.
  intros x.

  specialize (H8 0 ltac:(unfold b; solve_R)) as H9.
  assert (|x| <= b \/ |x| > b) as [H10 | H10] by solve_R.
  - specialize (H8 x); solve_R.
  - specialize (H5 x); solve_R.
Qed.