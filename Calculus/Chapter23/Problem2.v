From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_2_a :
  ~ series_converges (λ n, exp ((S n)%nat) * (fact (S n))%nat / (S n)%nat^(S n)).
Abort.

Lemma problem_23_2_b : ∀ a, a <> 0 ->
  (series_converges (λ n, (S n)%nat^(S n) / (a^(S n) * (fact (S n))%nat))
   <-> exp 1 < |a| \/ a = - exp 1).
Abort.
