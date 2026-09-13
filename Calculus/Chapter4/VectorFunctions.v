From Calculus.Chapter4 Require Export Prelude.
Local Open Scope plane_scope.

(** Chapter 4, Appendix 1: a vector is an ordered pair of real numbers;
    a vector function assigns such a pair to each value of its parameter.
    The analytic operations below are the componentwise calculus used in
    Chapter 17 (and described in Spivak's Appendix to Chapter 12). *)

Definition line (p v : plane) : vector_function 2 := λ t, p ⊕ t • v.
Definition graph_curve (f : ℝ → ℝ) : vector_function 2 := λ t, ⟨t, f t⟩.
Definition rotate (theta : ℝ) (v : plane) : plane :=
  ⟨vx v * cos theta - vy v * sin theta,
    vx v * sin theta + vy v * cos theta⟩.

Theorem line_velocity p v : (⟦ der ⟧ (line p v) = (λ _, v))%vc.
Proof.
  intros t i. change ((⟦ der t ⟧ (λ x, p i + x * v i) = (λ _, v i))).
  eapply derivative_at_ext_val.
  - apply derivative_at_plus; [apply derivative_at_const |].
    apply derivative_at_mult; [apply derivative_at_id | apply derivative_at_const].
  - cbn. ring.
Qed.

Theorem graph_velocity f f' t :
  (⟦ der t ⟧ f = f') → (⟦ der t ⟧ (graph_curve f) = (λ x, ⟨1, f' x⟩))%vc.
Proof. intros H1. apply plane_derivative_iff. split; [apply derivative_at_id | exact H1]. Qed.

(** The determinant measures signed area: rotation preserves it. *)
Theorem rotation_preserves_determinant theta v w :
  det(rotate theta v, rotate theta w) = det(v, w).
Proof.
  pose proof (pythagorean_identity theta) as H1.
  pose proof (f_equal (λ z, det(v, w) * z) H1) as H2.
  unfold det in H2. unfold det, rotate, vx, vy, plane_pair. cbn.
  unfold vx, vy in H2. nra.
Qed.

Definition signed_triangle_area (v w : plane) := det(v, w) / 2.

Theorem triangle_area_of_displacement v w :
  signed_triangle_area v (λ i, w i - v i) = signed_triangle_area v w.
Proof. unfold signed_triangle_area, det, vx, vy. cbn. field. Qed.

Example vector_function_components :
  (⟦ der ⟧ (λ t, ⟨t, t * t⟩) = (λ t, ⟨1, 2 * t⟩))%vc.
Proof.
  intro t. apply graph_velocity. eapply derivative_at_ext_val.
  - apply derivative_at_mult; apply derivative_at_id.
  - cbn. ring.
Qed.
