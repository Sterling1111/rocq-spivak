From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_4 :
  ~ series_converges (λ n, 1 / (S n)%nat ^^ (1 + 1 / (S n)%nat)).
Abort.
