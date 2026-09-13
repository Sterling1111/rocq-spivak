From Calculus.Chapter23 Require Import Prelude.

Definition is_distinct_egyptian_fractions (x : R) : Prop :=
  ∃ denominators : list nat,
    NoDup denominators /\
    (∀ n, List.In n denominators -> (n > 0)%nat) /\
    x = fold_right Rplus 0 (map (λ (n : ℕ), 1 / n) denominators).

Lemma problem_23_30_a_numerator : ∀ p q n : nat,
  (p > 0)%nat -> (q > 0)%nat -> (n > 0)%nat ->
  1 / (S n)%nat < p / q < 1 / n ->
  (0 < p * (n+1) - q < p)%nat /\
  p / q - 1 / (S n)%nat =
    (p * (n+1) - q)%nat / (q * (n+1))%nat.
Abort.

Lemma problem_23_30_a : ∀ x (n : ℕ),
  rational x -> (n > 0)%nat ->
  1 / (S n)%nat < x < 1 / n ->
  is_distinct_egyptian_fractions x.
Abort.

Lemma problem_23_30_b : ∀ x,
  rational x -> x > 0 -> is_distinct_egyptian_fractions x.
Abort.
