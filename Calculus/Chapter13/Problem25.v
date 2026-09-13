From Calculus.Chapter13 Require Import Prelude.

Definition length_of_polygonal_curve {a b : ℝ} (f : ℝ -> ℝ) (P : partition a b) : ℝ :=
  let l := P.(points a b) in
  ∑ 0 (length l - 2) (λ i, √((l.[i+1] - l.[i])^2 + (f (l.[i+1]) - f (l.[i]))^2)).

Notation "'ℓ(' f ',' P ')'" := (length_of_polygonal_curve f P) (at level 10, f, P at next level).

Definition is_length (a b : ℝ) (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  is_lub (λ y, ∃ P : partition a b, y = ℓ(f, P)) L.

Definition length_or_zero (a b : ℝ) (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  is_length a b f L \/ (~ (∃ L2, is_length a b f L2) /\ L = 0).

Definition length (a b : ℝ) (f : ℝ -> ℝ) : ℝ :=
  epsilon (inhabits 0) (length_or_zero a b f).

Lemma lemma_13_25_a : ∀ a b f m c,
  a < b -> (∀ x, x ∈ [a, b] -> f x = m * x + c) ->
  is_length a b f (√((b-a)^2 + (f b - f a)^2)).
Abort.

Lemma lemma_13_25_b : ∀ a b f,
  a < b -> continuous_on f [a, b] ->
  ~ (∃ m c, ∀ x, x ∈ [a, b] -> f x = m * x + c) ->
  ∃ t (P : partition a b), a < t < b /\
    points a b P = cons a (cons t (cons b nil)) /\
    √((b-a)^2 + (f b - f a)^2) < ℓ(f, P).
Abort.

Lemma lemma_13_25_c : ∀ a b c d f L,
  a < b -> continuous_on f [a, b] -> f a = c -> f b = d ->
  ~ (∀ x, x ∈ [a, b] -> f x = c + (d-c) * (x-a) / (b-a)) ->
  is_length a b f L -> √((b-a)^2 + (d-c)^2) < L.
Abort.

Lemma lemma_13_25_d : ∀ a b f f'
  (bf : bounded_function_R a b) (P : partition a b),
  derivative_on f f' [a, b] -> bounded_on f' [a, b] ->
  bounded_f a b bf = (λ x, √(1 + f' x ^ 2)) ->
  L(bf, P) <= ℓ(f, P) <= U(bf, P).
Abort.

Lemma lemma_13_25_e : ∀ a b f f' (bf : bounded_function_R a b),
  a < b -> derivative_on f f' [a, b] -> bounded_on f' [a, b] ->
  bounded_f a b bf = (λ x, √(1 + f' x ^ 2)) ->
  ∃ L, is_length a b f L /\ largest_lower_sum a b bf <= L.
Abort.

Lemma lemma_13_25_f_bounds : ∀ a b f f' (bf : bounded_function_R a b),
  a < b -> derivative_on f f' [a, b] -> bounded_on f' [a, b] ->
  bounded_f a b bf = (λ x, √(1 + f' x ^ 2)) ->
  ∃ L, is_length a b f L /\ L <= smallest_upper_sum a b bf.
Abort.

Lemma lemma_13_25_f : ∀ a b f f',
  a < b -> derivative_on f f' [a, b] ->
  integrable_on a b (λ x, √(1 + f' x ^ 2)) ->
  is_length a b f (∫ a b (λ x, √(1 + f' x ^ 2))).
Abort.

Lemma lemma_13_25_g : ∀ a b f f',
  a < b -> derivative_on f f' [a, b] ->
  integrable_on a b (λ x, √(1 + f' x ^ 2)) ->
  continuous_at_right f' a ->
  ⟦ lim a ⁺ ⟧ (λ x, length a x f / √((x-a)^2 + (f x - f a)^2)) = 1.
Abort.

Lemma lemma_13_25_h : ∀ f,
  continuous_on f [0, 1] -> f 0 = 0 -> f (1/2) = 0 -> f 1 = 0 ->
  (∀ x, x ∈ [0, 1] -> f (x/2) = f x / 2) ->
  (∃ x, x ∈ (1/2, 1) /\ 0 < f x) ->
  (∃ L, is_length 0 1 f L) ->
  ~ (⟦ lim 0 ⁺ ⟧ (λ x, length 0 x f / √(x^2 + (f x)^2)) = 1).
Abort.
