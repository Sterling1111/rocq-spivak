From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_9 : ∀ f f_inv f_inv',
  one_to_one f ->
  inverse f f_inv ->
  ⟦ der ⟧ f_inv = f_inv' ->
  (∀ x, f_inv' x <> 0) ->
  differentiable f.
Proof.
  intros f f_inv f_inv' H1 H2 H3 H4.
  apply derivative_imp_differentiable with (f' := λ x, / f_inv' (f x)).
  apply global_inverse_theorem with (f := f_inv); auto.
  apply inverse_symmetric; auto.
Qed.
