From Calculus.Chapter17 Require Export Polar.
Local Open Scope plane_scope.

Definition angular_momentum (c v : vector_function 2) t := det(c t, v t).
Definition areal_velocity (c v : vector_function 2) t := angular_momentum c v t / 2.
(** Signed swept area; increasing polar angle gives the positive orientation. *)
Definition swept_area (c v : vector_function 2) t0 t :=
  ∫ t0 t (areal_velocity c v).
Definition central_force l u (c acceleration : vector_function 2) :=
  ∀ t, l < t < u → c t ∥ acceleration t.
Definition kepler_second_law l u (c v : vector_function 2) t0 :=
  ∃ rate, ∀ t, l < t < u → swept_area c v t0 t = rate * (t - t0).

Lemma angular_momentum_derivative c v acceleration t :
  (⟦ der t ⟧ c = v)%vc → (⟦ der t ⟧ v = acceleration)%vc →
  (⟦ der t ⟧ (angular_momentum c v) = (λ t, det(c t, acceleration t))).
Proof.
  intros H1 H2. eapply derivative_at_ext_val.
  - exact (vector_derivative_det c v v acceleration t H1 H2).
  - cbn. rewrite det_self. ring.
Qed.

Lemma swept_area_derivative l u c v acceleration t0 t :
  (⟦ der ⟧ c (l, u) = v)%vc → (⟦ der ⟧ v (l, u) = acceleration)%vc →
  l < t0 < u → l < t < u →
  (⟦ der t ⟧ (swept_area c v t0) = (areal_velocity c v)).
Proof.
  intros H1 H2 H3 H4. unfold swept_area. eapply FTC1_at with
    (c := (l + Rmin t0 t) / 2) (d := (Rmax t0 t + u) / 2).
  - destruct (Rle_dec t0 t) as [H5 | H5]; [rewrite Rmin_left | rewrite Rmin_right]; lra.
  - destruct (Rle_dec t0 t) as [H5 | H5]; [rewrite Rmax_right | rewrite Rmax_left]; lra.
  - apply continuous_at_imp_continuous_on. intros x H5.
    assert (H6 : l < x < u).
    { unfold Ensembles.In in H5. cbn in H5.
      destruct (Rle_dec t0 t) as [H6 | H6]; rewrite ?Rmin_left, ?Rmax_right in H5 by lra;
        rewrite ?Rmin_right, ?Rmax_left in H5 by lra; lra. }
    apply differentiable_at_imp_continuous_at.
    pose proof (angular_momentum_derivative c v acceleration x
      (H1 x H6) (H2 x H6)) as H7.
    exists (det(c x, acceleration x) / 2).
    change ((⟦ der x ⟧ (λ t, angular_momentum c v t / 2) = (λ _, det(c x, acceleration x) / 2))).
    orbit_diff. field.
Qed.

(** Theorem 1, conservation form. *)
Theorem central_iff_constant_momentum l u c v acceleration t0 :
  (⟦ der ⟧ c (l, u) = v)%vc → (⟦ der ⟧ v (l, u) = acceleration)%vc →
  (∀ t, l < t < u → c t ≠ ⟨0, 0⟩) → l < t0 < u →
  (central_force l u c acceleration ↔
   ∀ t, l < t < u → angular_momentum c v t = angular_momentum c v t0).
Proof.
  intros H1 H2 H3 H4. split.
  - intros H5.
    assert (H6 : (∀ τ, l < τ < u → ⟦ der τ ⟧ (angular_momentum c v) = (λ _, 0))).
    { intros t H7. eapply derivative_at_ext_val.
      - apply angular_momentum_derivative; auto.
      - cbn. apply (proj2 (det_zero_iff_parallel _ _ (H3 t H7))). auto. }
    intros t H7. exact (scalar_constant l u _ H6 t t0 H7 H4).
  - intros H8 t H7. apply (proj1 (det_zero_iff_parallel _ _ (H3 t H7))).
    pose proof (scalar_constant_derivative l u (angular_momentum c v)
      (angular_momentum c v t0) t H7 H8) as H6.
    exact (derivative_at_unique _ _ _ t
      (angular_momentum_derivative c v acceleration t (H1 t H7) (H2 t H7)) H6).
Qed.

Theorem constant_momentum_area l u c v acceleration t0 M :
  (⟦ der ⟧ c (l, u) = v)%vc → (⟦ der ⟧ v (l, u) = acceleration)%vc →
  l < t0 < u →
  (∀ t, l < t < u → angular_momentum c v t = M) →
  ∀ t, l < t < u → swept_area c v t0 t = M / 2 * (t - t0).
Proof.
  intros H1 H2 H3 H4 t H5.
  assert (H6 : (∀ τ, l < τ < u → ⟦ der τ ⟧ (λ x, swept_area c v t0 x - M / 2 * (x - t0)) = (λ _, 0))).
  { intros x H7.
    pose proof (swept_area_derivative l u c v acceleration t0 x H1 H2 H3 H7) as H8.
    orbit_diff. unfold areal_velocity. rewrite H4 by exact H7. ring. }
  pose proof (scalar_constant l u _ H6 t t0 H5 H3) as H9.
  unfold swept_area in *. rewrite integral_n_n in H9. nra.
Qed.

(** Theorem 1: equal areas in equal times exactly characterize central force. *)
Theorem theorem_17_1 l u c v acceleration t0 :
  (⟦ der ⟧ c (l, u) = v)%vc → (⟦ der ⟧ v (l, u) = acceleration)%vc →
  (∀ t, l < t < u → c t ≠ ⟨0, 0⟩) → l < t0 < u →
  (kepler_second_law l u c v t0 ↔ central_force l u c acceleration).
Proof.
  intros H1 H2 H3 H4. split.
  - intros [rate H5]. apply (proj2 (central_iff_constant_momentum
      l u c v acceleration t0 H1 H2 H3 H4)).
    assert (H6 : ∀ t, l < t < u → angular_momentum c v t = 2 * rate).
    { intros t H7.
      assert (H8 : (⟦ der t ⟧ (swept_area c v t0) = (λ _, rate))).
      { eapply scalar_local_ext with (f := λ x, rate * (x-t0)); eauto.
        - intros x H9. symmetry. auto.
        - orbit_diff. ring. }
      pose proof (derivative_at_unique _ _ _ t
        (swept_area_derivative l u c v acceleration t0 t H1 H2 H4 H7) H8) as H10.
      unfold areal_velocity in H10. lra. }
    intros t H7. rewrite (H6 t H7), (H6 t0 H4). reflexivity.
  - intros H11. exists (angular_momentum c v t0 / 2).
    eapply constant_momentum_area; eauto.
    apply (proj1 (central_iff_constant_momentum l u c v acceleration t0
      H1 H2 H3 H4)). exact H11.
Qed.
