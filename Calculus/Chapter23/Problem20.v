From Calculus.Chapter23 Require Import Prelude.

Definition figure5 (f : R -> R) : Prop :=
  f 0 = 0 /\ ∀ n : nat,
    let left := 1 / 2^(S n) in
    let right := 1 / 2^n in
    ∃ c, left < c < right /\
      (∀ x, left <= x <= c -> f x = (-1)^n * (x-left)/(c-left)) /\
      (∀ x, c <= x <= right -> f x = (-1)^n * (right-x)/(right-c)).

Lemma problem_23_20 : ∀ f, figure5 f ->
  integrable_on 0 1 f /\ integrable_on 0 1 (λ x, |f x|) /\
  ∫ 0 1 f = 1/6 /\ ∫ 0 1 (λ x, |f x|) = 1/2.
Abort.
