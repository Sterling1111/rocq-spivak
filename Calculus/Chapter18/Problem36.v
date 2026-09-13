From Calculus.Chapter18 Require Import Prelude.

From Lib Require Import Partition.

Lemma lemma_18_36_a : ∀ a b n (Hab : a < b) (Hn : (0 < n)%nat)
    (bf bg : bounded_function_R a b),
  (∀ x, x ∈ [a,b] -> bounded_f a b bf x > 0) ->
  (∀ x, x ∈ [a,b] -> bounded_f a b bg x = log (bounded_f a b bf x)) ->
  lower_sum a b bg (uniform_partition a b n Hab Hn) / (b-a) <=
    log (lower_sum a b bf (uniform_partition a b n Hab Hn) / (b-a)).
Abort.

Lemma lemma_18_36_b : ∀ f a b,
  a < b -> integrable_on a b f -> integrable_on a b (λ x, log (f x)) ->
  (∀ x, x ∈ [a,b] -> f x > 0) ->
  (∫ a b (λ x, log (f x))) / (b-a) <= log ((∫ a b f) / (b-a)).
Abort.

Lemma lemma_18_36_c : ∀ f a b,
  a < b -> integrable_on a b f -> integrable_on a b (λ x, log (f x)) ->
  (∀ x, x ∈ [a,b] -> f x > 0) ->
  (∫ a b (λ x, log (f x))) / (b-a) <= log ((∫ a b f) / (b-a)).
Abort.

Lemma lemma_18_36_d : ∀ f g a b u v,
  a < b -> u < v -> continuous_on g [u,v] ->
  weakly_convex_on (λ x, - g x) [u,v] ->
  integrable_on a b f -> integrable_on a b (λ x, g (f x)) ->
  (∀ x, x ∈ [a,b] -> u <= f x <= v) ->
  (∫ a b (λ x, g (f x))) / (b-a) <= g ((∫ a b f) / (b-a)).
Abort.
