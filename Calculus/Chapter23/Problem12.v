From Calculus.Chapter23 Require Import Prelude.


Definition cesaro_summable (a : sequence) (l : R) : Prop :=
  ⟦ lim ⟧ (λ (n : ℕ), (∑ 1 n (λ k, ∑ 1 k a)) / n) = l.

Lemma problem_23_12 :
  ∃ a l, cesaro_summable a l /\ ~ (∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n) = S).
Abort.
