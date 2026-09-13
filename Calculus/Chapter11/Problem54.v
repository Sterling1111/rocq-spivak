From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_54_a : ∀ f f' g g' a L,
  ⟦ lim a⁺ ⟧ f = 0 ->
  ⟦ lim a⁺ ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> g' x <> 0) ->
  ⟦ lim a⁺ ⟧ (f' / g') = L ->
  ⟦ lim a⁺ ⟧ (f / g) = L.
Proof.
  apply lhopital_right_0_0.
Qed.

Lemma lemma_11_54_a' : ∀ f f' g g' a L,
  ⟦ lim a⁻ ⟧ f = 0 ->
  ⟦ lim a⁻ ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> g' x <> 0) ->
  ⟦ lim a⁻ ⟧ (f' / g') = L ->
  ⟦ lim a⁻ ⟧ (f / g) = L.
Proof.
  apply lhopital_left_0_0.
Qed.

Lemma lemma_11_54_b : ∀ f f' g g' a,
  ⟦ lim a ⟧ f = 0 ->
  ⟦ lim a ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> g' x <> 0) ->
  ⟦ lim a ⟧ (λ x, f' x / g' x) = ∞ ->
  ⟦ lim a ⟧ (λ x, f x / g x) = ∞.
Proof.
  apply lhopital_0_0_pinf.
Qed.

Lemma lemma_11_54_b' : ∀ f f' g g' a,
  ⟦ lim a⁺ ⟧ f = 0 ->
  ⟦ lim a⁺ ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> g' x <> 0) ->
  ⟦ lim a⁺ ⟧ (λ x, f' x / g' x) = ∞ ->
  ⟦ lim a⁺ ⟧ (λ x, f x / g x) = ∞.
Proof.
  apply lhopital_right_0_0_pinf.
Qed.

Lemma lemma_11_54_b'' : ∀ f f' g g' a,
  ⟦ lim a⁻ ⟧ f = 0 ->
  ⟦ lim a⁻ ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> g' x <> 0) ->
  ⟦ lim a⁻ ⟧ (λ x, f' x / g' x) = ∞ ->
  ⟦ lim a⁻ ⟧ (λ x, f x / g x) = ∞.
Proof.
  apply lhopital_left_0_0_pinf.
Qed.

Lemma lemma_11_54_b''' : ∀ f f' g g' a,
  ⟦ lim a ⟧ f = 0 ->
  ⟦ lim a ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> g' x <> 0) ->
  ⟦ lim a ⟧ (λ x, f' x / g' x) = -∞ ->
  ⟦ lim a ⟧ (λ x, f x / g x) = -∞.
Proof.
  apply lhopital_0_0_minf.
Qed.

Lemma lemma_11_54_b'''' : ∀ f f' g g' a,
  ⟦ lim a⁺ ⟧ f = 0 ->
  ⟦ lim a⁺ ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> g' x <> 0) ->
  ⟦ lim a⁺ ⟧ (λ x, f' x / g' x) = -∞ ->
  ⟦ lim a⁺ ⟧ (λ x, f x / g x) = -∞.
Proof.
  apply lhopital_right_0_0_minf.
Qed.

Lemma lemma_11_54_b''''' : ∀ f f' g g' a,
  ⟦ lim a⁻ ⟧ f = 0 ->
  ⟦ lim a⁻ ⟧ g = 0 ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> ⟦ der x ⟧ f = f') ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> ⟦ der x ⟧ g = g') ->
  (∃ δ, δ > 0 /\ ∀ x, a - δ < x < a -> g' x <> 0) ->
  ⟦ lim a⁻ ⟧ (λ x, f' x / g' x) = -∞ ->
  ⟦ lim a⁻ ⟧ (λ x, f x / g x) = -∞.
Proof.
  apply lhopital_left_0_0_minf.
Qed.

Lemma lemma_11_54_c : ∀ f f' g g' L,
  ⟦ lim ∞ ⟧ f = 0 ->
  ⟦ lim ∞ ⟧ g = 0 ->
  (∃ M, ∀ x, x > M -> ⟦ der x ⟧ f = f') ->
  (∃ M, ∀ x, x > M -> ⟦ der x ⟧ g = g') ->
  (∃ M, ∀ x, x > M -> g' x <> 0) ->
  ⟦ lim ∞ ⟧ (λ x, f' x / g' x) = L ->
  ⟦ lim ∞ ⟧ (λ x, f x / g x) = L.
Proof.
  apply lhopital_pinf_0_0.
Qed.

Lemma lemma_11_54_c' : ∀ f f' g g' L,
  ⟦ lim -∞ ⟧ f = 0 ->
  ⟦ lim -∞ ⟧ g = 0 ->
  (∃ M, ∀ x, x < M -> ⟦ der x ⟧ f = f') ->
  (∃ M, ∀ x, x < M -> ⟦ der x ⟧ g = g') ->
  (∃ M, ∀ x, x < M -> g' x <> 0) ->
  ⟦ lim -∞ ⟧ (λ x, f' x / g' x) = L ->
  ⟦ lim -∞ ⟧ (λ x, f x / g x) = L.
Proof.
  apply lhopital_minf_0_0.
Qed.

Lemma lemma_11_54_d : ∀ f f' g g',
  ⟦ lim ∞ ⟧ f = 0 ->
  ⟦ lim ∞ ⟧ g = 0 ->
  (∃ M, ∀ x, x > M -> ⟦ der x ⟧ f = f') ->
  (∃ M, ∀ x, x > M -> ⟦ der x ⟧ g = g') ->
  (∃ M, ∀ x, x > M -> g' x <> 0) ->
  ⟦ lim ∞ ⟧ (λ x, f' x / g' x) = ∞ ->
  ⟦ lim ∞ ⟧ (λ x, f x / g x) = ∞.
Proof.
  apply lhopital_pinf_0_0_pinf.
Qed.