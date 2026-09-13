From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_3_a :
  improper_integrable_pinf 1 (λ y, exp y / y ^^ y).
Abort.

Lemma problem_23_3_b :
  series_converges (λ n, 1 / (log (((n+2)%nat : ℝ))) ^^ (log (((n+2)%nat : ℝ)))).
Abort.

Lemma problem_23_3_c :
  ~ series_converges (λ n, 1 / (log (((n+2)%nat : ℝ))) ^^ (log (log (((n+2)%nat : ℝ))))).
Abort.
