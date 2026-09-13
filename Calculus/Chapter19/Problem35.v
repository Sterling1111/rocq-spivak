From Calculus.Chapter19 Require Import Prelude.

Definition second_mean_value_19 (f φ : R -> R) (a b : R) : Prop :=
  ∃ ξ, a <= ξ <= b /\
  ∫ a b (λ x, f x*φ x) = φ a * ∫ a ξ f + φ b * ∫ ξ b f.
Definition smooth_weight_19 (φ : R -> R) (a b : R) :=
  ∃ φ', derivative_on φ φ' [a,b] /\ continuous_on φ' [a,b].
Lemma lemma_19_35_a : ∀ f a b, a < b -> continuous_on f [a,b] ->
  (∀ φ, smooth_weight_19 φ a b -> non_increasing_on φ [a,b] -> second_mean_value_19 f φ a b) ->
  ∀ φ, smooth_weight_19 φ a b -> non_decreasing_on φ [a,b] -> second_mean_value_19 f φ a b.
Abort.

Lemma lemma_19_35_b : ∀ f a b, a < b -> continuous_on f [a,b] ->
  (∀ φ, smooth_weight_19 φ a b -> non_increasing_on φ [a,b] -> φ b = 0 -> second_mean_value_19 f φ a b) ->
  ∀ φ, smooth_weight_19 φ a b -> non_increasing_on φ [a,b] -> second_mean_value_19 f φ a b.
Abort.

Lemma lemma_19_35_c : ∀ f φ a b, a < b -> continuous_on f [a,b] ->
  smooth_weight_19 φ a b -> non_increasing_on φ [a,b] -> φ b = 0 ->
  ∃ ξ, a <= ξ <= b /\ ∫ a b (λ x, f x*φ x) = φ a * ∫ a ξ f.
Abort.

Lemma lemma_19_35_d : ∃ f φ, continuous_on f [0,1] /\ smooth_weight_19 φ 0 1 /\
  ~ non_increasing_on φ [0,1] /\ ~ non_decreasing_on φ [0,1] /\
  ~ second_mean_value_19 f φ 0 1.
Abort.
