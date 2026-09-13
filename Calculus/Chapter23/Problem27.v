From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_27 : ∀ a,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  (~ series_converges (λ n, a (S n)) <->
   ~ series_converges (λ n, a (S n) / (1 + a (S n)))).
Abort.
