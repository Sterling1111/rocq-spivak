From Calculus.Chapter17 Require Import PlanetaryMotion.
Local Open Scope plane_scope.

(** A circular orbit exercises the complete chain: actual derivative witnesses,
    central force, swept area, a complete ellipse traversal, and the period law. *)
Section CircularOrbit.
  Variables R0 omega : ℝ.
  Hypothesis H1 : 0 < R0.
  Hypothesis H2 : 0 < omega.

  Let T := 2 * π / omega.

  Definition circular_motion : polar_motion (-1) (T + 1).
  Proof.
    refine {| radius := λ _, R0; angle := λ t, omega * t;
      radius' := λ _, 0; angle' := λ _, omega;
      radius'' := λ _, 0; angle'' := λ _, 0 |}.
    - intros t H3. exact H1.
    - intros t H3. apply derivative_at_const.
    - intros t H3. orbit_diff. ring.
    - intros t H3. apply derivative_at_const.
    - intros t H3. apply derivative_at_const.
  Defined.

  Lemma circular_inverse_square :
    inverse_square_force circular_motion (R0 ^ 3 * omega ^ 2).
  Proof.
    intros t H3. unfold acceleration, polar_acceleration. cbn.
    apply plane_ext; polar_coordinates; field; lra.
  Qed.

  Lemma circular_central :
    central_force (-1) (T + 1) (position circular_motion) (acceleration circular_motion).
  Proof. eapply inverse_square_is_central. apply circular_inverse_square. Qed.

  Definition circular_revolution : elliptic_revolution circular_motion.
  Proof.
    assert (H3 : 0 < T) by (unfold T; apply Rdiv_lt_0_compat; [pose proof π_pos as H4; lra | assumption]).
    refine {| semimajor := R0; semiminor := R0; semilatus := R0;
      eccentricity := 0; epoch := 0; period := T;
      anomaly := λ t, omega * t; anomaly' := λ _, omega |}.
    - exact H1.
    - exact H1.
    - exact H1.
    - lra.
    - ring.
    - intros t H5. cbn. ring.
    - intros t H5. unfold position, polar_curve. cbn.
      apply plane_ext; polar_coordinates; ring.
    - intros t H5. orbit_diff. ring.
    - exact H3.
    - lra.
    - lra.
    - unfold T. field. lra.
  Defined.

  Example circular_swept_area :
    swept_area (position circular_motion) (velocity circular_motion) 0 T = π * R0 ^ 2.
  Proof.
    pose proof (ellipse_area_per_revolution circular_revolution) as H3.
    change (swept_area (position circular_motion) (velocity circular_motion) 0 (0 + T) =
      π * R0 * R0) in H3. rewrite Rplus_0_l in H3. nra.
  Qed.

  Example circular_period_law : R0 ^ 3 / T ^ 2 = (R0 ^ 3 * omega ^ 2) / (4 * π ^ 2).
  Proof.
    pose proof (Theorem3 (λ _ : unit, circular_motion)
      (λ _ : unit, circular_revolution) (R0 ^ 3 * omega ^ 2)
      (λ _, circular_central)) as H3.
    exact (proj1 H3 (λ _, circular_inverse_square) tt).
  Qed.
End CircularOrbit.

(** A line through the sun has zero angular momentum. This is why the conic
    theorem's nonzero-momentum hypothesis cannot be dropped. *)
Example radial_trajectory_momentum (r v : ℝ → ℝ) t :
  det(⟨r t, 0⟩, ⟨v t, 0⟩) = 0.
Proof. unfold det, vx, vy, plane_pair. cbn. ring. Qed.
