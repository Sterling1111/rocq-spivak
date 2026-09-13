From Calculus.Chapter21 Require Import Prelude.

Definition nondecreasing_on (f : R -> R) (D : Ensemble R) : Prop :=
  ∀ x y, x ∈ D -> y ∈ D -> x < y -> f x <= f y.

Lemma lemma_21_7_a : ∀ f ε,
  nondecreasing_on f (λ x, 0 <= x <= 1) ->
  ε > 0 ->
  Finite_set (λ a, 0 <= a <= 1 /\
    ∃ L R_val, ⟦ lim a⁻ ⟧ f = L /\ ⟦ lim a⁺ ⟧ f = R_val /\ R_val - L > ε).
Abort.

Lemma lemma_21_7_b : ∀ f,
  nondecreasing_on f (λ x, 0 <= x <= 1) ->
  countable (λ a, 0 <= a <= 1 /\ ~ continuous_at f a).
Abort.
