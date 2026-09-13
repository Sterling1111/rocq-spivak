From Calculus.Chapter17 Require Export Period.
Local Open Scope vector_calculus_scope.
Export SetNotations.
Local Open Scope plane_scope.

Section OnePlanet.
  Context {l u : ℝ} (p : polar_motion l u).
  Variable t₀ : ℝ.
  Hypothesis H1 : t₀ ∈ (l, u).

  Local Notation c := (position p).
  Local Notation "c′" := (velocity p).
  Local Notation "c″" := (acceleration p).
  Local Notation r := (radius p).
  Local Notation "r′" := (radius' p).
  Local Notation "r″" := (radius'' p).
  Local Notation θ := (angle p).
  Local Notation "θ′" := (angle' p).
  Local Notation "θ″" := (angle'' p).
  Local Notation e := radial.
  Local Notation "e′" := transverse.
  Local Notation A := (swept_area c c′ t₀).
  Local Notation M := (momentum p t₀).

  Lemma Position : ∀ t, c t = r t • e (θ t).
  Proof. reflexivity. Qed.

  Lemma Velocity :
    ⟦ der ⟧ c (l, u) = c′ ∧
    ∀ t, c′ t = r′ t • e (θ t) ⊕ (r t * θ′ t) • e′ (θ t).
  Proof. split; [apply position_derivative | reflexivity]. Qed.

  Lemma Acceleration :
    ⟦ der ⟧ c′ (l, u) = c″ ∧
    ∀ t, c″ t = (r″ t - r t * θ′ t ^ 2) • e (θ t)
             ⊕ (2 * r′ t * θ′ t + r t * θ″ t) • e′ (θ t).
  Proof. split; [apply velocity_derivative | reflexivity]. Qed.

  Local Open Scope derivative_scope.

  Lemma AreaDerivative : ∀ t, t ∈ (l, u) →
    ⟦ der t ⟧ A = (λ s, det(c s, c′ s) / 2).
  Proof.
    intros t H2. exact (swept_area_derivative l u c c′ c″ t₀ t
      (position_derivative p) (velocity_derivative p) H1 H2).
  Qed.

  Theorem Theorem1 :
    (∃ k, ∀ t, t ∈ (l, u) → A t = k * (t - t₀)) ↔
    (∀ t, t ∈ (l, u) → c t ∥ c″ t).
  Proof.
    exact (theorem_17_1 l u c c′ c″ t₀
      (position_derivative p) (velocity_derivative p)
      (position_nonzero p) H1).
  Qed.

  Corollary ConservationOfAngularMomentum :
    (∀ t, t ∈ (l, u) → c t ∥ c″ t) →
    ∀ t, t ∈ (l, u) → det(c t, c′ t) = M ∧ r t ^ 2 * θ′ t = M.
  Proof.
    intros H2 t H3.
    pose proof (central_conserves_momentum p t₀ H1 H2 t H3) as H4.
    split; [unfold position, velocity; rewrite polar_momentum |]; exact H4.
  Qed.

  Theorem Theorem2 (μ : ℝ) :
    0 < μ → M ≠ 0 →
    (∀ t, t ∈ (l, u) → c″ t = (-μ / r t ^ 2) • e (θ t)) →
    ∃ β γ, ∀ t, t ∈ (l, u) →
      r t * (1 + β * cos (θ t) + γ * sin (θ t)) = M ^ 2 / μ.
  Proof.
    intros H2 H3 H4. exact (theorem_17_2 p μ t₀ H2 H1 H3 H4).
  Qed.
End OnePlanet.

Section EllipticPlanets.
  Context {I : Type} {l u : ℝ}.
  Variable planets : I → polar_motion l u.
  Variable ellipses : ∀ i, elliptic_revolution (planets i).

  Local Notation c := (λ i, position (planets i)).
  Local Notation "c″" := (λ i, acceleration (planets i)).
  Local Notation r := (λ i, radius (planets i)).
  Local Notation θ := (λ i, angle (planets i)).
  Local Notation a := (λ i, semimajor (ellipses i)).
  Local Notation T := (λ i, period (ellipses i)).
  Local Notation e := radial.

  Theorem Theorem3 (G : ℝ) :
    (∀ i t, t ∈ (l, u) → c i t ∥ c″ i t) →
    ((∀ i t, t ∈ (l, u) → c″ i t = (-G / r i t ^ 2) • e (θ i t)) ↔
     (∀ i, a i ^ 3 / T i ^ 2 = G / (4 * π ^ 2))).
  Proof. exact (theorem_17_3 planets ellipses G). Qed.
End EllipticPlanets.

Section ConicOrbit.
  Context {l u : ℝ} (p : polar_motion l u).
  Variable t₀ : ℝ.
  Hypothesis H1 : t₀ ∈ (l, u).

  Local Notation c := (position p).
  Local Notation "c″" := (acceleration p).
  Local Notation r := (radius p).
  Local Notation θ := (angle p).
  Local Notation e := radial.
  Local Notation M := (momentum p t₀).

  Theorem Theorem4 (ℓ β γ : ℝ) :
    0 < ℓ → M ≠ 0 →
    (∀ t, t ∈ (l, u) → c t ∥ c″ t) →
    (∀ t, t ∈ (l, u) → r t * (1 + β * cos (θ t) + γ * sin (θ t)) = ℓ) →
    0 < M ^ 2 / ℓ ∧
    ∀ t, t ∈ (l, u) → c″ t = (-(M ^ 2 / ℓ) / r t ^ 2) • e (θ t).
  Proof.
    intros H2 H3 H4 H5.
    exact (theorem_17_4 p ℓ β γ t₀ H2 H1 H3 H4 H5).
  Qed.
End ConicOrbit.
