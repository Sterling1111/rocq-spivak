From Calculus.Chapter17 Require Export Conics.
Local Open Scope plane_scope.

Section ConicAcceleration.
  Context {l u : ℝ} (p : polar_motion l u).
  Variables ell beta gamma M : ℝ.
  Hypothesis H1 : 0 < ell.
  Hypothesis H2 : focal_conic p ell beta gamma.
  Hypothesis H3 : ∀ t, l < t < u → momentum p t = M.

  Local Definition F t := 1 + beta * cos (angle p t) + gamma * sin (angle p t).
  Local Definition U t := -beta * sin (angle p t) + gamma * cos (angle p t).

  (** Differentiate r F = ell and use r^2 theta' = M. *)
  Lemma conic_radial_velocity t :
    l < t < u → ell * radius' p t + M * U t = 0.
  Proof.
    intros H4.
    pose proof (radius_derivative p t H4) as H5.
    pose proof (angle_derivative p t H4) as H6.
    assert (H7 : (⟦ der t ⟧ (λ x, radius p x * F x) = (λ x, radius' p x * F x + radius p x * U x * angle' p x))).
    { unfold F, U. orbit_diff. ring. }
    assert (H8 : (⟦ der t ⟧ (λ x, radius p x * F x) = (λ _, 0))).
    { eapply scalar_constant_derivative; [exact H4 | exact H2]. }
    pose proof (derivative_at_unique _ _ _ t H7 H8) as H9. cbn beta in H9.
    pose proof (f_equal (λ z, z * radius p t) H9) as H10.
    pose proof (f_equal (λ z, z * radius' p t) (H2 t H4)) as H11.
    pose proof (f_equal (λ z, z * U t) (H3 t H4)) as H12.
    change (radius p t * F t * radius' p t = ell * radius' p t) in H11.
    unfold momentum in H12. nra.
  Qed.

  (** Differentiate ell r' + M U = 0 once more. *)
  Lemma conic_radial_acceleration t :
    l < t < u →
    ell * radius'' p t - M * (F t - 1) * angle' p t = 0.
  Proof.
    intros H4.
    pose proof (radius_second_derivative p t H4) as H5.
    pose proof (angle_derivative p t H4) as H6.
    assert (H7 : (⟦ der t ⟧ (λ x, ell * radius' p x + M * U x) = (λ x, ell * radius'' p x - M * (F x - 1) * angle' p x))).
    { unfold U, F. orbit_diff. ring. }
    assert (H8 : (⟦ der t ⟧ (λ x, ell * radius' p x + M * U x) = (λ _, 0))).
    { eapply scalar_constant_derivative; [exact H4 | apply conic_radial_velocity]. }
    exact (derivative_at_unique _ _ _ t H7 H8).
  Qed.

  Lemma central_transverse_acceleration t :
    l < t < u → 2 * radius' p t * angle' p t + radius p t * angle'' p t = 0.
  Proof.
    intros H4.
    pose proof (radius_derivative p t H4) as H5.
    pose proof (angle_second_derivative p t H4) as H6.
    assert (H7 : (⟦ der t ⟧ (momentum p) = (λ x, 2 * radius p x * radius' p x * angle' p x +
        radius p x ^ 2 * angle'' p x))).
    { unfold momentum. orbit_diff. cbn. ring. }
    pose proof (scalar_constant_derivative l u (momentum p) M t H4 H3) as H8.
    pose proof (derivative_at_unique _ _ _ t H7 H8) as H9. cbn beta in H9.
    pose proof (radius_positive p t H4) as H10. nra.
  Qed.

  Lemma conic_acceleration : inverse_square_force p (M ^ 2 / ell).
  Proof.
    intros t H4.
    pose proof (radius_positive p t H4) as H5.
    pose proof (H2 t H4) as H6. change (radius p t * F t = ell) in H6.
    pose proof (H3 t H4) as H7. unfold momentum in H7.
    pose proof (conic_radial_acceleration t H4) as H8.
    assert (H9 : F t = ell / radius p t).
    { apply (Rmult_eq_reg_r (radius p t)); [|lra]. field_simplify; nra. }
    assert (H10 : angle' p t = M / radius p t ^ 2).
    { apply (Rmult_eq_reg_r (radius p t ^ 2)); [|nra]. field_simplify; nra. }
    assert (H11 : radius'' p t = M * (F t - 1) * angle' p t / ell).
    { apply (Rmult_eq_reg_r ell); [|lra]. field_simplify; nra. }
    assert (H12 : radius'' p t - radius p t * angle' p t ^ 2 =
      -(M ^ 2 / ell) / radius p t ^ 2).
    { rewrite H11, H9, H10. field. split; lra. }
    unfold acceleration, polar_acceleration.
    rewrite H12, (central_transverse_acceleration t H4).
    apply plane_ext; polar_coordinates; ring.
  Qed.
End ConicAcceleration.

(** Theorem 4: a nonradial central-force orbit on a focal conic obeys an
    attractive inverse-square law, with coefficient M^2 / ell. *)
Theorem theorem_17_4 {l u} (p : polar_motion l u) ell beta gamma t0 :
  0 < ell → l < t0 < u → momentum p t0 ≠ 0 →
  central_force l u (position p) (acceleration p) →
  focal_conic p ell beta gamma →
  0 < momentum p t0 ^ 2 / ell ∧
  inverse_square_force p (momentum p t0 ^ 2 / ell).
Proof.
  intros H1 H2 H3 H4 H5. split.
  - apply Rdiv_lt_0_compat; nra.
  - apply (conic_acceleration p ell beta gamma (momentum p t0)); auto.
    apply central_conserves_momentum; auto.
Qed.
