From Calculus.Chapter17 Require Export Area.
Local Open Scope plane_scope.

(** The focal equation in an arbitrary orientation. The eccentricity vector
    (beta,gamma) avoids choosing an inverse trigonometric branch for a rotation.
    In axes along that vector this is r (1 + e cos theta) = ell. *)
Definition focal_conic {l u} (p : polar_motion l u) ell beta gamma :=
  ∀ t, l < t < u →
    radius p t * (1 + beta * cos (angle p t) + gamma * sin (angle p t)) = ell.
Definition inverse_square_force {l u} (p : polar_motion l u) mu :=
  ∀ t, l < t < u →
    acceleration p t = (-mu / radius p t ^ 2) • radial (angle p t).
Definition momentum {l u} (p : polar_motion l u) t := radius p t ^ 2 * angle' p t.

Lemma momentum_is_determinant {l u} (p : polar_motion l u) t :
  angular_momentum (position p) (velocity p) t = momentum p t.
Proof. apply polar_momentum. Qed.

Lemma inverse_square_is_central {l u} (p : polar_motion l u) mu :
  inverse_square_force p mu → central_force l u (position p) (acceleration p).
Proof.
  intros H1 t H2. exists (-mu / radius p t ^ 3).
  rewrite H1 by exact H2. apply plane_ext;
    unfold position; polar_coordinates;
    field; pose proof (radius_positive p t H2) as H3; lra.
Qed.

Lemma central_conserves_momentum {l u} (p : polar_motion l u) t0 :
  l < t0 < u → central_force l u (position p) (acceleration p) →
  ∀ t, l < t < u → momentum p t = momentum p t0.
Proof.
  intros H1 H2 t H3. rewrite <- !momentum_is_determinant.
  apply (proj1 (central_iff_constant_momentum l u (position p) (velocity p)
    (acceleration p) t0 (position_derivative p) (velocity_derivative p)
    (position_nonzero p) H1)); auto.
Qed.

Section Hodograph.
  Context {l u : ℝ} (p : polar_motion l u).
  Variables mu M : ℝ.
  Hypothesis H1 : M ≠ 0.
  Hypothesis H2 : inverse_square_force p mu.
  Hypothesis H3 : ∀ t, l < t < u → momentum p t = M.

  Definition hodograph_x t := vx (velocity p t) + mu / M * sin (angle p t).
  Definition hodograph_y t := vy (velocity p t) - mu / M * cos (angle p t).

  (** Spivak integrates velocity as a function of angle. Equivalently these
      two expressions have zero time derivative; no inverse-angle choice is needed. *)
  Lemma hodograph_x_constant : (∀ τ, l < τ < u → ⟦ der τ ⟧ hodograph_x = (λ _, 0)).
  Proof.
    intros t H4.
    pose proof (velocity_derivative p t H4 Fin.F1) as H5.
    change ((⟦ der t ⟧ (λ x, vx (velocity p x)) = (λ x, vx (acceleration p x)))) in H5.
    pose proof (angle_derivative p t H4) as H6.
    pose proof (H3 t H4) as H7. unfold momentum in H7.
    pose proof (radius_positive p t H4) as H8.
    unfold hodograph_x. orbit_diff. rewrite H2 by exact H4.
    change (-mu / radius p t ^ 2 * cos (angle p t) +
      (0 * sin (angle p t) + mu / M * (cos (angle p t) * angle' p t)) = 0).
    field_simplify; nra.
  Qed.

  Lemma hodograph_y_constant : (∀ τ, l < τ < u → ⟦ der τ ⟧ hodograph_y = (λ _, 0)).
  Proof.
    intros t H4.
    pose proof (velocity_derivative p t H4 (Fin.FS Fin.F1)) as H5.
    change ((⟦ der t ⟧ (λ x, vy (velocity p x)) = (λ x, vy (acceleration p x)))) in H5.
    pose proof (angle_derivative p t H4) as H6.
    pose proof (H3 t H4) as H7. unfold momentum in H7.
    pose proof (radius_positive p t H4) as H8.
    unfold hodograph_y. orbit_diff. rewrite H2 by exact H4.
    change (-mu / radius p t ^ 2 * sin (angle p t) -
      (0 * cos (angle p t) + mu / M * (-sin (angle p t) * angle' p t)) = 0).
    field_simplify; nra.
  Qed.
End Hodograph.

(** Theorem 2: a nonradial inverse-square orbit lies on a focal conic.
    Radial collision trajectories (M = 0) are deliberately excluded. *)
Theorem theorem_17_2 {l u} (p : polar_motion l u) mu t0 :
  0 < mu → l < t0 < u → momentum p t0 ≠ 0 →
  inverse_square_force p mu →
  ∃ beta gamma, focal_conic p (momentum p t0 ^ 2 / mu) beta gamma.
Proof.
  intros H1 H2 H3 H4.
  set (M := momentum p t0).
  assert (H5 : ∀ t, l < t < u → momentum p t = M).
  { apply central_conserves_momentum; auto. eapply inverse_square_is_central; eauto. }
  set (A := hodograph_x p mu M t0).
  set (B := hodograph_y p mu M t0).
  exists (M * B / mu), (-M * A / mu). intros t H6.
  pose proof (scalar_constant l u _
    (hodograph_x_constant p mu M H3 H4 H5) t t0 H6 H2) as H7.
  pose proof (scalar_constant l u _
    (hodograph_y_constant p mu M H3 H4 H5) t t0 H6 H2) as H8.
  change (vx (velocity p t) + mu / M * sin (angle p t) = A) in H7.
  change (vy (velocity p t) - mu / M * cos (angle p t) = B) in H8.
  pose proof (H5 t H6) as H9.
  rewrite <- momentum_is_determinant in H9.
  unfold angular_momentum, det in H9.
  change (radius p t * cos (angle p t) * vy (velocity p t) -
    radius p t * sin (angle p t) * vx (velocity p t) = M) in H9.
  assert (H10 : vx (velocity p t) = A - mu / M * sin (angle p t)) by lra.
  assert (H11 : vy (velocity p t) = B + mu / M * cos (angle p t)) by lra.
  rewrite H10, H11 in H9.
  pose proof (pythagorean_identity (angle p t)) as H12.
  change (radius p t * (1 + M * B / mu * cos (angle p t) +
    -M * A / mu * sin (angle p t)) = M ^ 2 / mu).
  assert (H13 : radius p t * mu *
    (sin (angle p t)^2 + cos (angle p t)^2) = radius p t * mu).
  { rewrite H12. ring. }
  apply (Rmult_eq_compat_r M) in H9.
  field_simplify in H9; try assumption.
  apply (Rmult_eq_reg_r mu); [|lra].
  field_simplify; nra.
Qed.

(** The focal equation is genuinely geometric: distance from the focus plus
    projection on the eccentricity vector equals the semilatus rectum. *)
Lemma focal_conic_cartesian {l u} (p : polar_motion l u) ell beta gamma :
  focal_conic p ell beta gamma → ∀ t, l < t < u →
  ‖ position p t ‖ + ⟨beta, gamma⟩ · position p t = ell.
Proof.
  intros H1 t H2. specialize (H1 t H2).
  pose proof (radius_positive p t H2) as H3.
  pose proof (pythagorean_identity (angle p t)) as H4.
  assert (H5 : ‖ position p t ‖ = radius p t).
  { unfold norm, dot, position. polar_coordinates.
    replace (radius p t * cos (angle p t) * (radius p t * cos (angle p t)) +
      radius p t * sin (angle p t) * (radius p t * sin (angle p t)))
      with (Rsqr (radius p t)) by (unfold Rsqr; nra).
    apply sqrt_Rsqr. lra. }
  rewrite H5. unfold dot, position. polar_coordinates. nra.
Qed.
