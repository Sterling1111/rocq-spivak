From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_8 : ∀ f f_inv f' f_inv' f_inv'',
  inverse f f_inv ->
  ⟦ der ⟧ f = f' ->
  (∀ x, f' x = 1 / sqrt (1 + x^3)) ->
  ⟦ der ⟧ f_inv = f_inv' ->
  ⟦ der ⟧ f_inv' = f_inv'' ->
  ∀ x, f_inv'' x = (3/2) * (f_inv x)^2.
Abort.
