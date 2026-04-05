From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_4_a :
  limit_at_point (fun x => exp (1 / x^2 * log (sin x / x))) 0 (exp (-1/6)).
Admitted.

Lemma lemma_20_4_b :
  limit_at_point (fun x => (sin x - x + x^3/6) / (x^5)) 0 (1/120).
Admitted.
