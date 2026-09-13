From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_35 : ∃ f g : R -> R,
  integrable f /\ integrable g /\ ~ integrable_on 0 1 (λ x, g (f x)).
Abort.
