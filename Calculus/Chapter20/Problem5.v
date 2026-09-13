From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_5_a : ∃ r, r > 0 /\
  (∀ x, x^2 = cos x <-> |x| = r) /\
  |r - sqrt (2/3)| < 1/50 /\
  |r - sqrt (18 - 10 * sqrt 3)| < 1/1000.
Abort.

Lemma lemma_20_5_b : ∃ r, r > 0 /\
  (∀ x, 2*x^2 = x * sin x + (cos x)^2 <-> |x| = r) /\
  |r - sqrt (1/2)| < 1/50 /\
  |r - sqrt (6 - sqrt 30)| < 3/1000.
Abort.
