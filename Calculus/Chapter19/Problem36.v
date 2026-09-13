From Calculus.Chapter19 Require Import Prelude.

From Calculus.Chapter19 Require Import Problem29 Problem35.
Lemma lemma_19_36_a : ∀ (a b : nat -> R) n, (0 < n)%nat ->
  ∑ 1 n (λ i, a i*b i) =
  (sum_first_19 (n-1) (λ i, (∑ 1 i a)*(b i-b (S i)))) + (∑ 1 n a)*b n.
Abort.
(* For a tail beginning at k, the partial-sum bounds also begin at k. *)
Lemma lemma_19_36_b : ∀ (a b : nat -> R) k n m M, (1 <= k <= n)%nat ->
  (∀ i, (k <= i <= n)%nat -> 0 <= b i) ->
  (∀ i, (k <= i < n)%nat -> b (S i) <= b i) ->
  (∀ j, (k <= j <= n)%nat -> m <= ∑ k j a <= M) ->
  b k*m <= ∑ k n (λ i, a i*b i) <= b k*M.
Abort.
Lemma lemma_19_36_c_sums : ∀ f φ a b n t,
  partition_19 a b n t -> non_increasing_on φ [a,b] -> φ b = 0 ->
  ∃ j k, (1 <= j <= n)%nat /\ (1 <= k <= n)%nat /\
  φ a * (∑ 1 j (λ i, f (t (i-1)%nat)*(t i-t (i-1)%nat))) <=
    ∑ 1 n (λ i, f (t (i-1)%nat)*φ (t (i-1)%nat)*(t i-t (i-1)%nat)) <=
  φ a * (∑ 1 k (λ i, f (t (i-1)%nat)*(t i-t (i-1)%nat))).
Abort.
Lemma lemma_19_36_c : ∀ f φ a b, a < b -> integrable_on a b f ->
  non_increasing_on φ [a,b] -> φ b = 0 ->
  ∃ ξ, a <= ξ <= b /\ ∫ a b (λ x, f x*φ x) = φ a * ∫ a ξ f.
Abort.
Lemma lemma_19_36_general : ∀ f φ a b, a < b -> integrable_on a b f ->
  (non_increasing_on φ [a,b] \/ non_decreasing_on φ [a,b]) -> second_mean_value_19 f φ a b.
Abort.
