From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_10_a : ∀ f : R -> R,
  (∃ g : R -> R, ∀ x, f x = (g x)^2) <-> nonnegative f.
Proof.
  intros f. split.
  - intros [g H1] x. rewrite H1. nra.
  - intros H1. exists (λ x, sqrt (f x)). intro x.
    symmetry. apply pow2_sqrt. specialize (H1 x). lra.
Qed.

Lemma lemma_3_10_b : ∀ f : R -> R,
  (∃ g : R -> R, ∀ x, g x <> 0 /\ f x = 1 / g x) <->
  (∀ x, f x <> 0).
Proof.
  intros f. split.
  - intros [g H1] x. destruct (H1 x) as [H2 H3]. rewrite H3.
    unfold Rdiv. apply Rmult_integral_contrapositive_currified; [lra | apply Rinv_neq_0_compat; lra].
  - intros H1. exists (λ x, 1 / f x). intros x. split.
    + unfold Rdiv. apply Rmult_integral_contrapositive_currified; [lra | apply Rinv_neq_0_compat; apply H1].
    + field. apply H1.
Qed.

Lemma lemma_3_10_c : ∀ b c : R -> R,
  (∃ x : R -> R, ∀ t, (x t)^2 + b t * x t + c t = 0) <->
  (∀ t, (b t)^2 - 4 * c t >= 0).
Proof.
  intros b c. split.
  - intros [x H1] t. specialize (H1 t).
    pose proof (Rle_0_sqr (2 * x t + b t)). unfold Rsqr in *. nra.
  - intros H1. exists (λ t, (- b t + sqrt ((b t)^2 - 4 * c t)) / 2).
    intro t. pose proof (pow2_sqrt ((b t)^2 - 4 * c t) ltac:(specialize (H1 t); lra)). nra.
Qed.

Lemma lemma_3_10_d : ∀ a b : R -> R,
  (∃ x : R -> R, ∀ t, a t * x t + b t = 0) <->
  (∀ t, a t = 0 -> b t = 0).
Proof.
  intros a b. split.
  - intros [x H1] t H2. specialize (H1 t). rewrite H2 in H1. lra.
  - intros H1. exists (λ t, - b t / a t). intro t.
    destruct (Req_EM_T (a t) 0) as [H2 | H2].
    + rewrite H2, (H1 t H2). ring.
    + field. exact H2.
Qed.

Lemma lemma_3_10_d_unique : ∀ a b : R -> R,
  (∃! x : R -> R, ∀ t, a t * x t + b t = 0) <->
  (∀ t, a t <> 0).
Proof.
  intros a b. split.
  - intros [x [H1 H2]] t H3.
    set (y := λ s, if Req_EM_T s t then x s + 1 else x s).
    assert (H4 : ∀ s, a s * y s + b s = 0).
    { intro s. unfold y. destruct (Req_EM_T s t) as [H4 | H4].
      - subst s. specialize (H1 t). rewrite H3 in *. lra.
      - apply H1. }
    pose proof (H2 y H4) as H5.
    apply (f_equal (λ f, f t)) in H5. unfold y in H5.
    destruct (Req_EM_T t t); [lra | contradiction].
  - intros H1. exists (λ t, - b t / a t). split.
    + intro t. field. apply H1.
    + intros x H2. apply functional_extensionality. intro t.
      specialize (H2 t). apply Rmult_eq_reg_l with (r := a t); [|apply H1].
      assert (H3 : a t * (- b t / a t) = - b t) by (field; apply H1). lra.
Qed.

Lemma lemma_3_10_d_infinite : ∀ a b : R -> R,
  (∀ t, a t = 0 -> b t = 0) -> (∃ t, a t = 0) ->
  ∀ l : list (R -> R), ∃ x : R -> R,
    ~ List.In x l /\ (∀ t, a t * x t + b t = 0).
Proof.
  intros a b H1 [t H2] l.
  assert (H3 : ∃ M, ∀ g, List.In g l -> g t < M).
  { induction l as [|g l [M IH]].
    - exists 0. intros g H3. contradiction.
    - exists (Rmax (g t) M + 1). intros h [H3 | H3].
      + subst h. solve_R.
      + specialize (IH h H3). solve_R. }
  destruct H3 as [M H3].
  set (x := λ s, if Req_EM_T s t then M else - b s / a s).
  exists x. split.
  - intro H4. specialize (H3 x H4). unfold x in H3.
    destruct (Req_EM_T t t); [lra | contradiction].
  - intro s. unfold x. destruct (Req_EM_T s t) as [H4 | H4].
    + subst s. rewrite H2, (H1 t H2). ring.
    + destruct (Req_EM_T (a s) 0) as [H5 | H5].
      * rewrite H5, (H1 s H5). ring.
      * field. exact H5.
Qed.
