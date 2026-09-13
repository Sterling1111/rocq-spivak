From Calculus.Chapter17 Require Export Converse.
Local Open Scope plane_scope.

(** An ellipse traversed once counterclockwise. [anomaly] is the usual
    eccentric anomaly, not the polar angle. The two coordinate descriptions
    record the elementary geometry used on page 336. Here a and b are SEMIaxes. *)
Record elliptic_revolution {l u} (p : polar_motion l u) := {
  semimajor : ℝ;
  semiminor : ℝ;
  semilatus : ℝ;
  eccentricity : ℝ;
  epoch : ℝ;
  period : ℝ;
  anomaly : ℝ → ℝ;
  anomaly' : ℝ → ℝ;
  semimajor_positive : 0 < semimajor;
  semiminor_positive : 0 < semiminor;
  semilatus_positive : 0 < semilatus;
  eccentricity_bounds : 0 <= eccentricity < 1;
  ellipse_axes : semiminor ^ 2 = semimajor * semilatus;
  ellipse_focal : focal_conic p semilatus eccentricity 0;
  ellipse_parameterization : ∀ t, l < t < u →
    position p t = ⟨semimajor * (cos (anomaly t) - eccentricity),
                     semiminor * sin (anomaly t)⟩;
  anomaly_derivative : (∀ τ, l < τ < u → ⟦ der τ ⟧ anomaly = anomaly');
  period_positive : 0 < period;
  epoch_inside : l < epoch < u;
  return_inside : l < epoch + period < u;
  one_revolution : anomaly (epoch + period) = anomaly epoch + 2 * π
}.
Arguments semimajor {l u p} _.
Arguments semiminor {l u p} _.
Arguments semilatus {l u p} _.
Arguments eccentricity {l u p} _.
Arguments epoch {l u p} _.
Arguments period {l u p} _.
Arguments anomaly {l u p} _ _.
Arguments anomaly' {l u p} _ _.
Arguments semimajor_positive {l u p} _.
Arguments semiminor_positive {l u p} _.
Arguments semilatus_positive {l u p} _.
Arguments eccentricity_bounds {l u p} _.
Arguments ellipse_axes {l u p} _.
Arguments ellipse_focal {l u p} _.
Arguments ellipse_parameterization {l u p} _ _ _.
Arguments anomaly_derivative {l u p} _ _ _.
Arguments period_positive {l u p} _.
Arguments epoch_inside {l u p} _.
Arguments return_inside {l u p} _.
Arguments one_revolution {l u p} _.

Section EllipseArea.
  Context {l u} {p : polar_motion l u} (E : elliptic_revolution p).
  Local Notation a := (semimajor E).
  Local Notation b := (semiminor E).
  Local Notation e := (eccentricity E).
  Local Notation ψ := (anomaly E).
  Local Notation "ψ′" := (anomaly' E).

  Definition ellipse_area_primitive t := a * b / 2 * (ψ t - e * sin (ψ t)).

  Lemma ellipse_velocity t : l < t < u →
    velocity p t = ⟨-a * sin (ψ t) * ψ′ t, b * cos (ψ t) * ψ′ t⟩.
  Proof.
    intro H1. pose proof (anomaly_derivative E t H1) as H2.
    apply plane_ext.
    - assert (H3 : (⟦ der t ⟧ (λ x, vx (position p x)) = (λ x, -a * sin (ψ x) * ψ′ x))).
      { eapply scalar_local_ext with (f := λ x, a * (cos (ψ x) - e)); eauto.
        - intros x H4. rewrite (ellipse_parameterization E x H4). reflexivity.
        - orbit_diff. ring. }
      exact (derivative_at_unique _ _ _ t (position_derivative p t H1 Fin.F1) H3).
    - assert (H3 : (⟦ der t ⟧ (λ x, vy (position p x)) = (λ x, b * cos (ψ x) * ψ′ x))).
      { eapply scalar_local_ext with (f := λ x, b * sin (ψ x)); eauto.
        - intros x H4. rewrite (ellipse_parameterization E x H4). reflexivity.
        - orbit_diff. ring. }
      exact (derivative_at_unique _ _ _ t (position_derivative p t H1 (Fin.FS Fin.F1)) H3).
  Qed.

  Lemma ellipse_area_primitive_derivative t : l < t < u →
    (⟦ der t ⟧ ellipse_area_primitive = (areal_velocity (position p) (velocity p))).
  Proof.
    intro H1. pose proof (anomaly_derivative E t H1) as H2.
    unfold ellipse_area_primitive. orbit_diff.
    unfold areal_velocity, angular_momentum.
    rewrite (ellipse_parameterization E t H1), (ellipse_velocity t H1).
    unfold det. polar_coordinates.
    pose proof (f_equal (λ z, a * b * ψ′ t * z) (pythagorean_identity (ψ t))) as H3.
    nra.
  Qed.

  Lemma ellipse_swept_area t : l < t < u →
    swept_area (position p) (velocity p) (epoch E) t =
    ellipse_area_primitive t - ellipse_area_primitive (epoch E).
  Proof.
    intro H1.
    assert (H2 : (∀ τ, l < τ < u → ⟦ der τ ⟧ (λ x, swept_area (position p) (velocity p) (epoch E) x -
        ellipse_area_primitive x) = (λ _, 0))).
    { intros x H3.
      pose proof (swept_area_derivative l u (position p) (velocity p) (acceleration p)
        (epoch E) x (position_derivative p) (velocity_derivative p) (epoch_inside E) H3) as H4.
      pose proof (ellipse_area_primitive_derivative x H3) as H5.
      orbit_diff. ring. }
    pose proof (scalar_constant l u _ H2 t (epoch E) H1 (epoch_inside E)) as H6.
    unfold swept_area in *. rewrite integral_n_n in H6. lra.
  Qed.

  (** The ellipse-area formula is proved, not assumed from unfinished Chapter 13. *)
  Theorem ellipse_area_per_revolution :
    swept_area (position p) (velocity p) (epoch E) (epoch E + period E) = π * a * b.
  Proof.
    rewrite ellipse_swept_area by apply return_inside.
    unfold ellipse_area_primitive. rewrite one_revolution, sin_periodic. field.
  Qed.
End EllipseArea.

Lemma period_momentum {l u} {p : polar_motion l u} (E : elliptic_revolution p) :
  central_force l u (position p) (acceleration p) →
  momentum p (epoch E) * period E = 2 * π * semimajor E * semiminor E.
Proof.
  intro H1.
  pose proof (constant_momentum_area l u (position p) (velocity p) (acceleration p)
    (epoch E) (momentum p (epoch E)) (position_derivative p) (velocity_derivative p)
    (epoch_inside E)) as H2.
  assert (H3 : ∀ t, l < t < u →
    angular_momentum (position p) (velocity p) t = momentum p (epoch E)).
  { intros t H4. rewrite momentum_is_determinant. apply central_conserves_momentum; auto.
    apply epoch_inside. }
  specialize (H2 H3 (epoch E + period E) (return_inside E)).
  rewrite (ellipse_area_per_revolution E) in H2. nra.
Qed.

Lemma ellipse_force_coefficient {l u} {p : polar_motion l u} (E : elliptic_revolution p) :
  central_force l u (position p) (acceleration p) →
  inverse_square_force p (4 * π ^ 2 * semimajor E ^ 3 / period E ^ 2).
Proof.
  intro H1.
  pose proof (period_momentum E H1) as H2.
  pose proof (ellipse_axes E) as H3.
  pose proof (period_positive E) as H4.
  pose proof (semilatus_positive E) as H5.
  assert (H6 : momentum p (epoch E) ^ 2 / semilatus E =
    4 * π ^ 2 * semimajor E ^ 3 / period E ^ 2).
  { apply (Rmult_eq_reg_r (semilatus E * period E ^ 2));
      [|apply Rmult_integral_contrapositive; split; nra].
    field_simplify; try nra.
    pose proof (f_equal (λ z, z ^ 2) H2) as H7.
    pose proof (f_equal (λ z, 4 * π ^ 2 * semimajor E ^ 2 * z) H3) as H8.
    nra. }
  rewrite <- H6.
  apply (conic_acceleration p (semilatus E) (eccentricity E) 0 (momentum p (epoch E))).
  - exact H5.
  - apply ellipse_focal.
  - apply central_conserves_momentum; auto. apply epoch_inside.
Qed.

Lemma inverse_square_coefficient_unique {l u} (p : polar_motion l u) μ ν t :
  l < t < u → inverse_square_force p μ → inverse_square_force p ν → μ = ν.
Proof.
  intros H1 H2 H3.
  assert (H4 : (-μ / radius p t ^ 2) • radial (angle p t) =
    (-ν / radius p t ^ 2) • radial (angle p t)).
  { rewrite <- H2, <- H3 by exact H1. reflexivity. }
  apply (f_equal (λ v, det(v, transverse (angle p t)))) in H4.
  rewrite !det_scale_l, (proj2 (proj2 (proj2 (radial_frame (angle p t))))) in H4.
  apply (Rmult_eq_compat_r (radius p t ^ 2)) in H4.
  pose proof (radius_positive p t H1) as H5. field_simplify in H4; nra.
Qed.

(** Theorem 3, with the normalization constant made explicit. *)
Theorem theorem_17_3 {I : Type} {l u} (planets : I → polar_motion l u)
    (ellipses : ∀ i, elliptic_revolution (planets i)) G :
  (∀ i, central_force l u (position (planets i)) (acceleration (planets i))) →
  ((∀ i, inverse_square_force (planets i) G) ↔
   (∀ i, semimajor (ellipses i) ^ 3 / period (ellipses i) ^ 2 = G / (4 * π ^ 2))).
Proof.
  intros H1. split.
  - intros H2 i.
    pose proof (inverse_square_coefficient_unique (planets i) G
      (4 * π ^ 2 * semimajor (ellipses i) ^ 3 / period (ellipses i) ^ 2)
      (epoch (ellipses i)) (epoch_inside (ellipses i)) (H2 i)
      (ellipse_force_coefficient (ellipses i) (H1 i))) as H3.
    rewrite H3. field. pose proof π_pos as H4. pose proof (period_positive (ellipses i)) as H5. split; lra.
  - intros H6 i.
    replace G with (4 * π ^ 2 * semimajor (ellipses i) ^ 3 / period (ellipses i) ^ 2).
    + apply ellipse_force_coefficient. auto.
    + specialize (H6 i). pose proof π_pos as H7. pose proof (period_positive (ellipses i)) as H8.
      apply (Rmult_eq_compat_r (4 * π ^ 2)) in H6.
      field_simplify in H6; nra.
Qed.
