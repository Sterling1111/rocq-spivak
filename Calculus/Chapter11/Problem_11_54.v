From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_54_a : forall f f' g g' a L,
  ⟦ lim a⁺ ⟧ f = 0 ->
  ⟦ lim a⁺ ⟧ g = 0 ->
  (exists δ, δ > 0 /\ forall x, a < x < a + δ -> ⟦ der x ⟧ f = f') ->
  (exists δ, δ > 0 /\ forall x, a < x < a + δ -> ⟦ der x ⟧ g = g') ->
  (exists δ, δ > 0 /\ forall x, a < x < a + δ -> g' x <> 0) ->
  ⟦ lim a⁺ ⟧ (f' / g') = L ->
  ⟦ lim a⁺ ⟧ (f / g) = L.
Proof.
  apply lhopital_right_0_0.
Qed.

Lemma lemma_11_54_b : forall f f' g g' a,
  ⟦ lim a ⟧ f = 0 ->
  ⟦ lim a ⟧ g = 0 ->
  (exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> ⟦ der x ⟧ f = f') ->
  (exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> ⟦ der x ⟧ g = g') ->
  (exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> g' x <> 0) ->
  ⟦ lim a ⟧ (fun x => f' x / g' x) = ∞ ->
  ⟦ lim a ⟧ (fun x => f x / g x) = ∞.
Proof.
  apply lhopital_0_0_pinf.
Qed.

Lemma lemma_11_54_b' : forall f f' g g' a,
  ⟦ lim a⁺ ⟧ f = 0 ->
  ⟦ lim a⁺ ⟧ g = 0 ->
  (exists δ, δ > 0 /\ forall x, a < x < a + δ -> ⟦ der x ⟧ f = f') ->
  (exists δ, δ > 0 /\ forall x, a < x < a + δ -> ⟦ der x ⟧ g = g') ->
  (exists δ, δ > 0 /\ forall x, a < x < a + δ -> g' x <> 0) ->
  ⟦ lim a⁺ ⟧ (fun x => f' x / g' x) = ∞ ->
  ⟦ lim a⁺ ⟧ (fun x => f x / g x) = ∞.
Proof.
  apply lhopital_right_0_0_pinf.
Qed.

Lemma lemma_11_54_c : forall f f' g g' L,
  ⟦ lim ∞ ⟧ f = 0 ->
  ⟦ lim ∞ ⟧ g = 0 ->
  (exists M, forall x, x > M -> ⟦ der x ⟧ f = f') ->
  (exists M, forall x, x > M -> ⟦ der x ⟧ g = g') ->
  (exists M, forall x, x > M -> g' x <> 0) ->
  ⟦ lim ∞ ⟧ (fun x => f' x / g' x) = L ->
  ⟦ lim ∞ ⟧ (fun x => f x / g x) = L.
Proof.
  apply lhopital_pinf_0_0.
Qed.