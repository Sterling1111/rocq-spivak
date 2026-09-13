From Calculus.Chapter19 Require Import Prelude.

(* Length is specified as the least upper bound of polygonal lengths. *)
Definition partition_19 (a b : R) (n : nat) (t : nat -> R) : Prop :=
  (0 < n)%nat /\ t 0%nat = a /\ t n = b /\
  (∀ i, (i < n)%nat -> t i < t (S i)).
Definition polygonal_length_19 (u v : R -> R) (n : nat) (t : nat -> R) :=
  ∑ 1 n (λ i, √((u (t i)-u (t (i-1)%nat))^2 + (v (t i)-v (t (i-1)%nat))^2)).
Definition has_length_19 (u v : R -> R) (a b L : R) : Prop :=
  (∀ n t, partition_19 a b n t -> polygonal_length_19 u v n t <= L) /\
  (∀ M, (∀ n t, partition_19 a b n t -> polygonal_length_19 u v n t <= M) -> L <= M).
Lemma lemma_19_29_a : ∀ u v h a b α β L,
  a < b -> α < β -> continuous_on h [α, β] -> increasing_on h [α, β] ->
  h α = a -> h β = b ->
  (has_length_19 u v a b L <-> has_length_19 (λ t, u (h t)) (λ t, v (h t)) α β L).
Abort.
Lemma lemma_19_29_b : ∀ u v u' v' h h' a b α β,
  a < b -> α < β -> derivative_on u u' [a,b] -> derivative_on v v' [a,b] ->
  continuous_on u' [a,b] -> continuous_on v' [a,b] ->
  derivative_on h h' [α,β] -> continuous_on h' [α,β] ->
  increasing_on h [α,β] -> h α = a -> h β = b ->
  ∫ a b (λ t, √(u' t^2+v' t^2)) =
  ∫ α β (λ t, √((u' (h t)*h' t)^2+(v' (h t)*h' t)^2)).
Abort.
