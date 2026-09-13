From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_26 :
  ∃ a, bounded (λ n, ∑ 1 (S n) a) /\
    ⟦ lim ⟧ a = 0 /\ ~ series_converges (λ n, a (S n)).
Abort.
