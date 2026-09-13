From Calculus.Chapter22 Require Import Prelude.

Definition power_tower (a : ℝ) (s : sequence) : Prop :=
  s 0%nat = a /\ ∀ n, s (S n) = a ^^ (s n).

Lemma lemma_22_26_a : ∀ a s L,
  0 < a -> power_tower a s -> ⟦ lim ⟧ s = L ->
  (∃ y, 0 < y /\ a = y ^^ (1 / y)) /\ 0 < a <= e ^^ (1 / e).
Abort.

Lemma lemma_22_26_a_graph :
  increasing_on (λ y, y ^^ (1 / y)) (0, e] /\
  decreasing_on (λ y, y ^^ (1 / y)) [e, ∞) /\
  (⟦ lim 0 ⁺ ⟧ (λ y, y ^^ (1 / y)) = 0) /\
  (⟦ lim ∞ ⟧ (λ y, y ^^ (1 / y)) = 1) /\
  (∀ y, 0 < y -> y ^^ (1 / y) <= e ^^ (1 / e)).
Abort.

Lemma lemma_22_26_b : ∀ a s,
  power_tower a s -> 1 <= a <= e ^^ (1 / e) ->
  nondecreasing s /\ (1 < a -> increasing s) /\
  (∀ n, s n <= e) /\
  ∃ L, ⟦ lim ⟧ s = L /\ L <= e.
Abort.

Lemma lemma_22_26_c : ∀ a s L,
  0 < a -> power_tower a s -> ⟦ lim ⟧ s = L ->
  / e <= L <= e /\ e ^^ (-e) <= a <= e ^^ (1 / e).
Abort.

Lemma lemma_22_26_d : ∀ a,
  e ^^ (-e) <= a < 1 ->
  decreasing_on (λ x, a ^^ x / log x) (0, 1).
Abort.

Lemma lemma_22_26_e : ∀ a b s,
  e ^^ (-e) <= a < 1 ->
  (∀ x, a ^^ x = x <-> x = b) -> power_tower a s ->
  a < b < 1 /\
  (∀ x, 0 < x < b -> x < a ^^ (a ^^ x) < b) /\
  ∃ l, ⟦ lim ⟧ (λ n, s (2*n)%nat) = l /\ a ^^ (a ^^ l) = l.
Abort.

Lemma lemma_22_26_f : ∀ a b s l,
  e ^^ (-e) <= a < 1 ->
  a ^^ b = b -> power_tower a s ->
  ⟦ lim ⟧ (λ n, s (2*n)%nat) = l -> l = b.
Abort.

Lemma lemma_22_26_g : ∀ a b s,
  e ^^ (-e) <= a < 1 ->
  a ^^ b = b -> power_tower a s ->
  ⟦ lim ⟧ (λ n, s (2*n + 1)%nat) = b /\ ⟦ lim ⟧ s = b.
Abort.
