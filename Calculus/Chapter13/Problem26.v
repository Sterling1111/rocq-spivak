From Calculus.Chapter13 Require Import Prelude.

Definition step_function_on (s : R -> R) (a b : R) : Prop :=
  ∃ P : partition a b, ∀ i,
    (i < List.length (points a b P) - 1)%nat ->
    ∃ c, ∀ x,
      x ∈ ((points a b P).[i], (points a b P).[i+1]) -> s x = c.

Lemma lemma_13_26_a : ∀ f a b ε,
  a < b -> integrable_on a b f -> ε > 0 ->
  ∃ s1 s2, step_function_on s1 a b /\ step_function_on s2 a b /\
    (∀ x, x ∈ [a, b] -> s1 x <= f x <= s2 x) /\
    ∫ a b f - ∫ a b s1 < ε /\ ∫ a b s2 - ∫ a b f < ε.
Abort.

Lemma lemma_13_26_b : ∀ f a b,
  a < b ->
  (∀ ε, ε > 0 -> ∃ s1 s2,
    step_function_on s1 a b /\ step_function_on s2 a b /\
    (∀ x, x ∈ [a, b] -> s1 x <= f x <= s2 x) /\
    ∫ a b s2 - ∫ a b s1 < ε) ->
  integrable_on a b f.
Abort.

Lemma lemma_13_26_c : ∀ a b,
  a < b -> ∃ (bf : bounded_function_R a b) (P : partition a b),
  integrable_on a b (bounded_f a b bf) /\
  ~ step_function_on (bounded_f a b bf) a b /\
  ∫ a b (bounded_f a b bf) = L(bf, P).
Abort.
