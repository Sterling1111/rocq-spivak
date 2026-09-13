From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_11_a : ∀ a b (bf : bounded_function_R a b),
  a < b ->
  ((∀ P Q : partition a b, L(bf, P) = U(bf, Q)) <->
   ∃ c, ∀ x, x ∈ [a, b] -> bounded_f a b bf x = c).
Abort.

Lemma lemma_13_11_b : ∀ a b (bf : bounded_function_R a b),
  a < b ->
  ((∃ P Q : partition a b, U(bf, P) = L(bf, Q)) <->
   ∃ c, ∀ x, x ∈ [a, b] -> bounded_f a b bf x = c).
Abort.

Lemma lemma_13_11_c : ∀ a b (bf : bounded_function_R a b),
  a < b -> continuous_on (bounded_f a b bf) [a, b] ->
  ((∀ P Q : partition a b, L(bf, P) = L(bf, Q)) <->
   ∃ c, ∀ x, x ∈ [a, b] -> bounded_f a b bf x = c).
Abort.

Lemma lemma_13_11_d : ∀ a b (bf : bounded_function_R a b),
  a < b -> integrable_on a b (bounded_f a b bf) ->
  ((∀ P Q : partition a b, L(bf, P) = L(bf, Q)) <->
   ∃ c,
     (∀ x, x ∈ [a, b] -> c <= bounded_f a b bf x) /\
     (∀ u v, a <= u < v -> v <= b ->
       ∃ x, u < x < v /\ bounded_f a b bf x = c)).
Abort.
