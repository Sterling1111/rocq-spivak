From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_6_a :
  ∃ f, (∀ x, (∃ n : nat, (n > 0)%nat /\ x = 1 / n) -> ~ continuous_at f x) /\
            (∀ x, ~ (∃ n : nat, (n > 0)%nat /\ x = 1 / n) -> continuous_at f x).
Proof. Abort.

Lemma lemma_6_6_b :
  ∃ f, ~(continuous_at f 0) /\ (∀ x, (∃ n : nat, (n > 0)%nat /\ x = 1 / n) -> ~ continuous_at f x) /\
            (∀ x, x <> 0 -> ~ (∃ n : nat, (n > 0)%nat /\ x = 1 / n) -> continuous_at f x).
Proof. Abort.
