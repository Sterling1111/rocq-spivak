From Lib Require Export FunctionalVector Derivative Integral Trigonometry.
From Lib Require Import Imports Sets Functions Limit Continuity Interval Notations.
Import FunctionNotations LimitNotations DerivativeNotations IntegralNotations
  IntervalNotations FunctionalVectorNotations.
Open Scope R_scope.

(** Real vector-valued functions: all analytic operations are componentwise.
    The dimension is part of the type, so addition cannot truncate coordinates. *)
Definition vector_function (n : nat) := ℝ → fvector ℝ n.
Definition vector_limit {n} (f : vector_function n) a (v : fvector ℝ n) :=
  ∀ i, ⟦ lim a ⟧ (λ t, f t i) = v i.

Definition vector_derivative_at {n} (f f' : vector_function n) a :=
  ∀ i, ⟦ der a ⟧ (λ t, f t i) = (λ t, f' t i).

(** Introduce pointwise notation before defining derivatives on domains. *)
Module VectorCalculusPointNotations.
  Declare Scope vector_calculus_scope.
  Delimit Scope vector_calculus_scope with vc.

  (** Match the scalar grammar exactly; only the scope chooses the meaning. *)
  Notation "⟦ 'lim' a ⟧ f '=' v" := (vector_limit f a v)
    (at level 70, f at level 0, no associativity,
      format "⟦  'lim'  a  ⟧  f  '='  v") : vector_calculus_scope.
  Notation "⟦ 'der' a ⟧ f = g" := (vector_derivative_at f g a)
    (at level 70, f at level 0, no associativity,
      format "⟦  'der'  a  ⟧  f  =  g") : vector_calculus_scope.
End VectorCalculusPointNotations.
Import VectorCalculusPointNotations.

Definition vector_continuous_at {n} (f : vector_function n) a :=
  (⟦ lim a ⟧ f = f a)%vc.

Definition vector_derivative {n} (f f' : vector_function n) :=
  ∀ a, (⟦ der a ⟧ f = f')%vc.
(** Two-sided derivatives at every point of a domain; in Chapter 17 the
    domain is an open interval, so there are no endpoint conventions. *)
Definition vector_derivative_on {n} (f f' : vector_function n) (D : Ensemble ℝ) :=
  ∀ a, D a → (⟦ der a ⟧ f = f')%vc.
Definition vector_integral {n} a b (f : vector_function n) : fvector ℝ n :=
  λ i, ∫ a b (λ t, f t i).

Module VectorCalculusNotations.
  Export VectorCalculusPointNotations.

  Notation "⟦ 'der' ⟧ f = g" := (vector_derivative f g)
    (at level 70, f at level 0, no associativity,
      format "⟦  'der'  ⟧  f  =  g") : vector_calculus_scope.
  Notation "⟦ 'der' ⟧ f D = g" := (vector_derivative_on f g D)
    (at level 70, f at level 0, D at level 0, no associativity,
      format "⟦  'der'  ⟧  f  D  =  g") : vector_calculus_scope.
  Notation "∫ a b f" := (vector_integral a b f)
    (at level 9, f at level 0, a at level 0, b at level 0,
      format "∫  a  b  f") : vector_calculus_scope.
End VectorCalculusNotations.
Import VectorCalculusNotations.

(** Spivak's plane vectors, Chapter 4, Appendix 1. *)
Definition plane := fvector ℝ 2.
Definition plane_pair (x y : ℝ) : plane := list_function [x; y].
Definition vx (v : plane) := v Fin.F1.
Definition vy (v : plane) := v (Fin.FS Fin.F1).
Definition det (v w : plane) := vx v * vy w - vy v * vx w.
Definition dot (v w : plane) := vx v * vx w + vy v * vy w.
Definition norm (v : plane) := √(dot v v).
Definition parallel (v w : plane) := ∃ k : ℝ, w = (k * v)%FV.

Module PlaneNotations.
  Declare Scope plane_scope.
  Delimit Scope plane_scope with plane.
  Notation "'⟨' x ',' y '⟩'" := (plane_pair x y).
  Infix "⊕" := fvector_add (at level 50, left associativity).
  Infix "•" := fvector_scale (at level 40, left associativity).
  Notation "‖ v ‖" := (norm v) (at level 40) : plane_scope.
  Notation "'det(' v ',' w ')'" := (det v w)
    (at level 0, v at level 99, w at level 99) : plane_scope.
  Infix "·" := dot (at level 40, left associativity) : plane_scope.
  Infix "∥" := parallel (at level 70, no associativity) : plane_scope.
End PlaneNotations.
Import PlaneNotations.
Local Open Scope plane_scope.

Lemma vector_limit_unique {n} (f : vector_function n) a v w :
  (⟦ lim a ⟧ f = v)%vc → (⟦ lim a ⟧ f = w)%vc → v = w.
Proof.
  intros H1 H2. apply fvector_ext. intro i. eapply limit_unique; eauto.
Qed.

Lemma vector_limit_add {n} (f g : vector_function n) a v w :
  (⟦ lim a ⟧ f = v)%vc → (⟦ lim a ⟧ g = w)%vc →
  (⟦ lim a ⟧ (λ t, f t ⊕ g t) = v ⊕ w)%vc.
Proof. intros H1 H2 i. apply limit_plus; auto. Qed.

Lemma vector_limit_scale {n} (s : ℝ → ℝ) (f : vector_function n) a k v :
  ⟦ lim a ⟧ s = k → (⟦ lim a ⟧ f = v)%vc →
  (⟦ lim a ⟧ (λ t, s t • f t) = k • v)%vc.
Proof. intros H1 H2 i. apply limit_mult; auto. Qed.

Lemma vector_integral_add {n} a b (f g : vector_function n) :
  a <= b →
  (∀ i, integrable_on a b (λ t, f t i)) →
  (∀ i, integrable_on a b (λ t, g t i)) →
  (∫ a b (λ t, f t ⊕ g t))%vc = (∫ a b f)%vc ⊕ (∫ a b g)%vc.
Proof.
  intros H1 H2 H3. apply fvector_ext. intro i.
  apply (integral_plus (λ t, f t i) (λ t, g t i) a b); auto.
Qed.

Lemma vector_derivative_difference_quotient {n} (f f' : vector_function n) a :
  (⟦ der a ⟧ f = f')%vc ↔
  (⟦ lim 0 ⟧ (λ h i, (f (a + h) i - f a i) / h) = f' a)%vc.
Proof. reflexivity. Qed.

Lemma vector_derivative_unique {n} (f g h : vector_function n) a :
  (⟦ der a ⟧ f = g)%vc → (⟦ der a ⟧ f = h)%vc → g a = h a.
Proof.
  intros H1 H2. apply fvector_ext. intro i.
  exact (derivative_at_unique _ _ _ a (H1 i) (H2 i)).
Qed.

Lemma vector_derivative_continuous {n} (f f' : vector_function n) a :
  (⟦ der a ⟧ f = f')%vc → vector_continuous_at f a.
Proof.
  intros H1 i. apply differentiable_at_imp_continuous_at.
  exists (f' a i). exact (H1 i).
Qed.

Lemma vector_derivative_const {n} (v : fvector ℝ n) a :
  (⟦ der a ⟧ (λ _, v) = (λ _ _, 0))%vc.
Proof. intro i. apply derivative_at_const. Qed.

Lemma vector_derivative_add {n} (f g f' g' : vector_function n) a :
  (⟦ der a ⟧ f = f')%vc → (⟦ der a ⟧ g = g')%vc →
  (⟦ der a ⟧ (λ t, f t ⊕ g t) = (λ t, f' t ⊕ g' t))%vc.
Proof. intros H1 H2 i. apply derivative_at_plus; auto. Qed.

Lemma vector_derivative_scale {n} (s s' : ℝ → ℝ)
    (f f' : vector_function n) a :
  ⟦ der a ⟧ s = s' → (⟦ der a ⟧ f = f')%vc →
  (⟦ der a ⟧ (λ t, s t • f t) =
    (λ t, s' t • f t ⊕ s t • f' t))%vc.
Proof. intros H1 H2 i. apply derivative_at_mult; auto. Qed.

Lemma vector_derivative_comp {n} (s s' : ℝ → ℝ)
    (f f' : vector_function n) a :
  ⟦ der a ⟧ s = s' → (⟦ der (s a) ⟧ f = f')%vc →
  (⟦ der a ⟧ (λ t, f (s t)) =
    (λ t, s' t • f' (s t)))%vc.
Proof.
  intros H1 H2 i. eapply derivative_at_ext_val.
  - exact (derivative_at_comp s (λ t, f t i) s'
      (λ t, f' t i) a H1 (H2 i)).
  - change (f' (s a) i * s' a = s' a * f' (s a) i). ring.
Qed.

Theorem vector_FTC1 {n} (f : vector_function n) a :
  (∀ t, vector_continuous_at f t) →
  (⟦ der ⟧ (λ t, ∫ a t f) = f)%vc.
Proof. intros H1 t i. apply FTC1_global. intro x. exact (H1 x i). Qed.

Theorem vector_FTC2 {n} (f g : vector_function n) a b :
  a < b →
  (∀ i, continuous_on (λ t, f t i) [a, b]) →
  (∀ i, ⟦ der ⟧ (λ t, g t i) [a, b] = (λ t, f t i)) →
  (∫ a b f)%vc = (λ i, g b i - g a i).
Proof. intros H1 H2 H3. apply fvector_ext. intro i. unfold vector_integral. apply (FTC2 a b (λ t, f t i) (λ t, g t i)); auto. Qed.

Lemma plane_ext (v w : plane) : vx v = vx w → vy v = vy w → v = w.
Proof.
  intros H1 H2. apply fvector_list_ext. apply vector_eq.
  cbn [function_to_vector vlist function_list]. unfold vx, vy in *. now rewrite H1, H2.
Qed.

Lemma plane_eta (v : plane) : v = ⟨vx v, vy v⟩.
Proof. apply plane_ext; reflexivity. Qed.

Lemma plane_dot_compat (v w : plane) : v · w = (v · w)%FV.
Proof. change (vx v * vx w + vy v * vy w = vx v * vx w + (vy v * vy w + 0)). ring. Qed.

Lemma plane_norm_compat (v : plane) : ‖ v ‖ = √((v · v)%FV).
Proof. unfold norm. now rewrite plane_dot_compat. Qed.

Lemma plane_norm_bounds (v : plane) :
  |(vx v)| <= ‖ v ‖ ∧ |(vy v)| <= ‖ v ‖ ∧
  ‖ v ‖ <= |(vx v)| + |(vy v)|.
Proof.
  assert (H1 : 0 <= v · v) by (unfold dot; nra).
  pose proof (sqrt_pos (v · v)) as H2.
  pose proof (sqrt_def (v · v) H1) as H3.
  pose proof (Rabs_pos (vx v)) as H4. pose proof (Rabs_pos (vy v)) as H5.
  pose proof (Rsqr_abs (vx v)) as H6. pose proof (Rsqr_abs (vy v)) as H7.
  unfold norm, dot, Rsqr in *. repeat split; nra.
Qed.

(** Componentwise convergence agrees with Euclidean convergence. *)
Theorem plane_limit_iff_norm (f : vector_function 2) a v :
  (⟦ lim a ⟧ f = v)%vc ↔
  ∀ epsilon, 0 < epsilon → ∃ delta, 0 < delta ∧
    ∀ t, 0 < |(t - a)| < delta → ‖ (λ i, f t i - v i) ‖ < epsilon.
Proof.
  split.
  - intros H1 epsilon H2.
    destruct (H1 Fin.F1 (epsilon / 2) ltac:(lra)) as [dx [H3 H4]].
    destruct (H1 (Fin.FS Fin.F1) (epsilon / 2) ltac:(lra)) as [dy [H5 H6]].
    exists (Rmin dx dy). split; [apply Rmin_pos; assumption |].
    intros t H7. pose proof (Rmin_l dx dy) as H8. pose proof (Rmin_r dx dy) as H9.
    specialize (H4 t ltac:(lra)). specialize (H6 t ltac:(lra)).
    pose proof (proj2 (proj2 (plane_norm_bounds (λ i, f t i - v i)))) as H10.
    unfold vx, vy in *. cbn beta in *. lra.
  - intros H1.
    assert (H4 : ⟦ lim a ⟧ (λ t, vx (f t)) = vx v).
    { intros epsilon H2. destruct (H1 epsilon H2) as [d [H11 H12]].
      exists d. split; auto. intros t H7.
      pose proof (proj1 (plane_norm_bounds (λ i, f t i - v i))) as H13.
      specialize (H12 t H7). unfold vx in *. cbn beta in *. lra. }
    assert (H6 : ⟦ lim a ⟧ (λ t, vy (f t)) = vy v).
    { intros epsilon H2. destruct (H1 epsilon H2) as [d [H11 H12]].
      exists d. split; auto. intros t H7.
      pose proof (proj1 (proj2 (plane_norm_bounds (λ i, f t i - v i)))) as H14.
      specialize (H12 t H7). unfold vy in *. cbn beta in *. lra. }
    intro i. refine (Fin.caseS' i (λ j, ⟦ lim a ⟧ (λ t, f t j) = v j) H4 _).
    intro j. refine (Fin.caseS' j
      (λ k, ⟦ lim a ⟧ (λ t, f t (Fin.FS k)) = v (Fin.FS k)) H6 _).
    intro k. inversion k.
Qed.

Lemma det_self (v : plane) : det(v, v) = 0.
Proof. unfold det. ring. Qed.
Lemma det_swap (v w : plane) : det(v, w) = - det(w, v).
Proof. unfold det. ring. Qed.
Lemma det_add_r (u v w : plane) : det(u, v ⊕ w) = det(u, v) + det(u, w).
Proof. cbv [det vx vy fvector_add fvector_scale fvector_map fvector_map2 add scale Add_R Scale_R]. ring. Qed.
Lemma det_add_l (u v w : plane) : det(u ⊕ v, w) = det(u, w) + det(v, w).
Proof. cbv [det vx vy fvector_add fvector_scale fvector_map fvector_map2 add scale Add_R Scale_R]. ring. Qed.
Lemma det_scale_l k (v w : plane) : det(k • v, w) = k * det(v, w).
Proof. cbv [det vx vy fvector_add fvector_scale fvector_map fvector_map2 add scale Add_R Scale_R]. ring. Qed.
Lemma det_scale_r k (v w : plane) : det(v, k • w) = k * det(v, w).
Proof. cbv [det vx vy fvector_add fvector_scale fvector_map fvector_map2 add scale Add_R Scale_R]. ring. Qed.

Lemma det_zero_iff_parallel (v w : plane) :
  v ≠ ⟨0, 0⟩ → (det(v, w) = 0 ↔ v ∥ w).
Proof.
  intros H1. split.
  - intros H2. destruct (Req_dec (vx v) 0) as [H3 | H3].
    + assert (H4 : vy v ≠ 0).
      { intro H4. apply H1. apply plane_ext; assumption. }
      exists (vy w / vy v). apply plane_ext; unfold vx, vy in *; cbn in *; cbv [fvector_scale fvector_map scale Scale_R].
      * unfold det, vx, vy in H2. rewrite H3 in *. nra.
      * field. exact H4.
    + exists (vx w / vx v). apply plane_ext; unfold vx, vy in *; cbn in *; cbv [fvector_scale fvector_map scale Scale_R].
      * field. exact H3.
      * unfold det, vx, vy in H2. apply (Rmult_eq_reg_r (v Fin.F1)); [|exact H3].
        field_simplify; nra.
  - intros [k ->]. rewrite det_scale_r, det_self. ring.
Qed.

Lemma plane_derivative_iff (f f' : vector_function 2) a :
  (⟦ der a ⟧ f = f')%vc ↔
  ⟦ der a ⟧ (λ t, vx (f t)) = (λ t, vx (f' t)) ∧
  ⟦ der a ⟧ (λ t, vy (f t)) = (λ t, vy (f' t)).
Proof.
  split; [intro H1; split; apply H1 | intros [H2 H3] i].
  refine (Fin.caseS' i (λ j,
    ⟦ der a ⟧ (λ t, f t j) = (λ t, f' t j)) H2 _).
  intro j. refine (Fin.caseS' j (λ k,
    ⟦ der a ⟧ (λ t, f t (Fin.FS k)) = (λ t, f' t (Fin.FS k))) H3 _).
  intro k. inversion k.
Qed.

Lemma vector_derivative_det (f g f' g' : vector_function 2) a :
  (⟦ der a ⟧ f = f')%vc → (⟦ der a ⟧ g = g')%vc →
  ⟦ der a ⟧ (λ t, det(f t, g t)) =
    (λ t, det(f' t, g t) + det(f t, g' t)).
Proof.
  intros H1 H2. unfold det, vx, vy. eapply derivative_at_ext_val.
  - apply derivative_at_minus; apply derivative_at_mult; auto.
  - cbn. ring.
Qed.

Lemma vector_derivative_dot (f g f' g' : vector_function 2) a :
  (⟦ der a ⟧ f = f')%vc → (⟦ der a ⟧ g = g')%vc →
  ⟦ der a ⟧ (λ t, f t · g t) =
    (λ t, f' t · g t + f t · g' t).
Proof.
  intros H1 H2. unfold dot, vx, vy. eapply derivative_at_ext_val.
  - apply derivative_at_plus; apply derivative_at_mult; auto.
  - cbn. ring.
Qed.
