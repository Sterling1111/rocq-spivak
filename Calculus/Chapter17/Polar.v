From Calculus.Chapter17 Require Export Prelude.
Local Open Scope plane_scope.

(** The moving orthonormal frame e, e' used throughout Chapter 17. *)
Definition radial (θ : ℝ) : plane := ⟨cos θ, sin θ⟩.
Definition transverse (θ : ℝ) : plane := ⟨-sin θ, cos θ⟩.

Lemma radial_frame θ :
  radial θ · radial θ = 1 ∧
  transverse θ · transverse θ = 1 ∧
  radial θ · transverse θ = 0 ∧
  det(radial θ, transverse θ) = 1.
Proof.
  pose proof (pythagorean_identity θ) as H1.
  unfold dot, det, vx, vy, radial, transverse, plane_pair. cbn.
  repeat split; nra.
Qed.

(** A twice differentiable polar parameterization avoiding the sun.
    The derivatives are witnesses, rather than arbitrary total derivative values. *)
Record polar_motion (l u : ℝ) := {
  radius : ℝ → ℝ;
  angle : ℝ → ℝ;
  radius' : ℝ → ℝ;
  angle' : ℝ → ℝ;
  radius'' : ℝ → ℝ;
  angle'' : ℝ → ℝ;
  radius_positive : ∀ t, l < t < u → 0 < radius t;
  radius_derivative : (∀ τ, l < τ < u → ⟦ der τ ⟧ radius = radius');
  angle_derivative : (∀ τ, l < τ < u → ⟦ der τ ⟧ angle = angle');
  radius_second_derivative : (∀ τ, l < τ < u → ⟦ der τ ⟧ radius' = radius'');
  angle_second_derivative : (∀ τ, l < τ < u → ⟦ der τ ⟧ angle' = angle'')
}.
Arguments radius {l u} _ _.
Arguments angle {l u} _ _.
Arguments radius' {l u} _ _.
Arguments angle' {l u} _ _.
Arguments radius'' {l u} _ _.
Arguments angle'' {l u} _ _.
Arguments radius_positive {l u} _ _ _.
Arguments radius_derivative {l u} _ _ _.
Arguments angle_derivative {l u} _ _ _.
Arguments radius_second_derivative {l u} _ _ _.
Arguments angle_second_derivative {l u} _ _ _.

Lemma radial_derivative : (⟦ der ⟧ radial = transverse)%vc.
Proof.
  intro t. apply plane_derivative_iff. split; auto_diff.
Qed.

Lemma transverse_derivative :
  (⟦ der ⟧ transverse = (λ t, (-1) • radial t))%vc.
Proof.
  intro t. apply plane_derivative_iff. split.
  - change ((⟦ der t ⟧ (λ x, -sin x) = (λ x, -1 * cos x))).
    auto_diff.
  - change ((⟦ der t ⟧ cos = (λ x, -1 * sin x))).
    auto_diff.
Qed.

Definition polar_curve (r θ : ℝ → ℝ) : vector_function 2 :=
  λ t, r t • radial (θ t).
Definition polar_velocity (r r' θ θ' : ℝ → ℝ) : vector_function 2 :=
  λ t, r' t • radial (θ t) ⊕ (r t * θ' t) • transverse (θ t).
Definition polar_acceleration (r r' r'' θ θ' θ'' : ℝ → ℝ)
    : vector_function 2 :=
  λ t, (r'' t - r t * θ' t ^ 2) • radial (θ t)
    ⊕ (2 * r' t * θ' t + r t * θ'' t) • transverse (θ t).

Ltac polar_coordinates :=
  cbv [polar_curve polar_velocity polar_acceleration radial transverse
    plane_pair vx vy fvector_add fvector_scale fvector_map fvector_map2
    add scale Add_R Scale_R list_function Fin.caseS'].

Lemma polar_curve_derivative r r' θ θ' t :
  (⟦ der t ⟧ r = r') → (⟦ der t ⟧ θ = θ') →
  (⟦ der t ⟧ (polar_curve r θ) = (polar_velocity r r' θ θ'))%vc.
Proof.
  intros H1 H2. apply plane_derivative_iff. split;
    polar_coordinates; orbit_diff; ring.
Qed.

Lemma polar_velocity_derivative r r' r'' θ θ' θ'' t :
  (⟦ der t ⟧ r = r') → (⟦ der t ⟧ r' = r'') →
  (⟦ der t ⟧ θ = θ') → (⟦ der t ⟧ θ' = θ'') →
  (⟦ der t ⟧ (polar_velocity r r' θ θ') =
    (polar_acceleration r r' r'' θ θ' θ''))%vc.
Proof.
  intros H1 H2 H3 H4. apply plane_derivative_iff. split;
    polar_coordinates; orbit_diff; ring.
Qed.

Lemma polar_momentum r r' θ θ' t :
  det(polar_curve r θ t, polar_velocity r r' θ θ' t) =
  r t ^ 2 * θ' t.
Proof.
  unfold polar_curve, polar_velocity.
  rewrite det_add_r, !det_scale_l, !det_scale_r, det_self.
  rewrite (proj2 (proj2 (proj2 (radial_frame (θ t))))). ring.
Qed.

Lemma polar_curve_nonzero r θ t :
  0 < r t → polar_curve r θ t ≠ ⟨0, 0⟩.
Proof.
  intros H1 H2. pose proof (f_equal vx H2) as H3. pose proof (f_equal vy H2) as H4.
  polar_coordinates. unfold polar_curve, radial in H3, H4.
  change (r t * cos (θ t) = 0) in H3.
  change (r t * sin (θ t) = 0) in H4.
  assert (H5 : cos (θ t) = 0 ∧ sin (θ t) = 0) by (split; nra).
  pose proof (pythagorean_identity (θ t)) as H6. destruct H5 as [H7 H8]. nra.
Qed.

Definition position {l u} (p : polar_motion l u) :=
  polar_curve (radius p) (angle p).
Definition velocity {l u} (p : polar_motion l u) :=
  polar_velocity (radius p) (radius' p) (angle p) (angle' p).
Definition acceleration {l u} (p : polar_motion l u) :=
  polar_acceleration (radius p) (radius' p) (radius'' p)
    (angle p) (angle' p) (angle'' p).

Lemma position_derivative {l u} (p : polar_motion l u) :
  (⟦ der ⟧ (position p) (l, u) = (velocity p))%vc.
Proof. intros t H1. apply polar_curve_derivative; [apply radius_derivative | apply angle_derivative]; auto. Qed.
Lemma velocity_derivative {l u} (p : polar_motion l u) :
  (⟦ der ⟧ (velocity p) (l, u) = (acceleration p))%vc.
Proof.
  intros t H1. apply polar_velocity_derivative;
    [apply radius_derivative | apply radius_second_derivative |
     apply angle_derivative | apply angle_second_derivative]; auto.
Qed.

Lemma position_nonzero {l u} (p : polar_motion l u) t :
  l < t < u → position p t ≠ ⟨0, 0⟩.
Proof.
  intro H1. apply polar_curve_nonzero. exact (radius_positive p t H1). 
Qed.
