From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_24 : ∀ f,
  integrable f ->
  (∀ x, f x = ∫ 0 x f) -> f = λ _, 0.
Proof.
  intros f H1 H2.
  extensionality x.
  destruct (Rtotal_order 0 x) as [H3 | [H3 | H3]].
  - pose proof theorem_13_8 f 0 x H3 ltac:(apply H1) as H4. 

    assert (H5 : f 0 = 0).
    { rewrite H2. apply integral_n_n. }

    assert (H6 : continuous_on f [0, x]).
    { replace f with (λ x, ∫ 0 x f); auto. extensionality y. auto. }

    assert (H7 : ⟦ der ⟧ f [0, x] = f).
    {
      pose proof FTC1 f 0 x H3 H6 as H7.
      replace (λ x : ℝ, ∫ 0 x f) with f in H7 by (extensionality y; auto); auto.
    }
    admit.
  - subst. rewrite H2, integral_n_n. reflexivity.
  - admit.
Admitted.