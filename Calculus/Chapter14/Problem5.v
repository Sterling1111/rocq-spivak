From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_5_i : exists g : R -> R,
  forall x, ∫ 0 x (fun t => t * g t) = x + x^2.
Abort.

Lemma lemma_14_5_ii : exists g : R -> R,
  forall x, ∫ 0 (x^2) (fun t => t * g t) = x + x^2.
Abort.
