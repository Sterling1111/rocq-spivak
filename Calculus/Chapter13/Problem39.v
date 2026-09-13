From Calculus.Chapter13 Require Import Prelude.
From Calculus.Chapter13 Require Import Problem38.

Lemma integral_square_difference_13_39 : ∀ f g a b t,
  a < b -> integrable_on a b f -> integrable_on a b g ->
  ∫ a b (λ x, (f x - t * g x)^2) =
    ∫ a b (λ x, f x^2) - 2*t*∫ a b (f ⋅ g) + t^2*∫ a b (λ x, g x^2).
Proof.
  intros f g a b t H1 H2 H3.
  assert (H4 : integrable_on a b (λ x, f x^2)).
  { replace (λ x, f x^2) with (f ⋅ f) by (extensionality x; ring).
    apply lemma_13_38_e; auto. }
  assert (H5 : integrable_on a b (λ x, g x^2)).
  { replace (λ x, g x^2) with (g ⋅ g) by (extensionality x; ring).
    apply lemma_13_38_e; auto. }
  assert (H6 : integrable_on a b (f ⋅ g)) by (apply lemma_13_38_e; auto).
  replace (λ x, (f x - t * g x)^2) with
    (λ x, (f x^2 - (2*t)*(f x*g x)) + t^2*g x^2) by (extensionality x; ring).
  rewrite integral_plus; try lra.
  - rewrite integral_minus; try lra.
    + rewrite !integral_mult_scalar; auto.
    + exact H4.
    + apply integrable_mult_scalar; auto.
  - apply integrable_minus; auto; try lra. apply integrable_mult_scalar; auto.
  - apply integrable_mult_scalar; auto.
Qed.

Lemma lemma_13_39 : ∀ f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (∫ a b (f ⋅ g))^2 <= (∫ a b (λ x, (f x)^2)) * (∫ a b (λ x, (g x)^2)).
Proof.
  intros f g a b H1 H2 H3.
  set (A := ∫ a b (λ x, f x^2)).
  set (B := ∫ a b (λ x, g x^2)).
  set (C := ∫ a b (f ⋅ g)).
  assert (H4 : 0 <= B).
  {
    unfold B. apply integral_nonneg; try lra.
    - intros x H4. nra.
    - replace (λ x, g x^2) with (g ⋅ g) by (extensionality x; ring).
      apply lemma_13_38_e; auto.
  }
  assert (H5 : ∀ t, 0 <= A - 2*t*C + t^2*B).
  {
    intros t. unfold A, B, C. rewrite <- integral_square_difference_13_39; auto.
    apply integral_nonneg; try lra.
    - intros x H5. pose proof Rle_0_sqr (f x - t*g x) as H6. unfold Rsqr in H6. nra.
    - replace (λ x, (f x - t*g x)^2) with
        ((λ x, f x - t*g x) ⋅ (λ x, f x - t*g x)) by (extensionality x; ring).
      apply lemma_13_38_e; auto; apply integrable_minus; auto; try lra;
        apply integrable_mult_scalar; auto.
  }
  change (C^2 <= A*B).
  destruct (Req_dec B 0) as [H6 | H6].
  - destruct (Req_dec C 0) as [H7 | H7]; [rewrite H6, H7; nra |].
    specialize (H5 ((A+1)/(2*C))).
    replace (A - 2*((A+1)/(2*C))*C + ((A+1)/(2*C))^2*B) with (-1) in H5
      by (rewrite H6; field; exact H7). lra.
  - specialize (H5 (C/B)).
    assert (H7 : 0 <= (A - 2*(C/B)*C + (C/B)^2*B)*B)
      by (apply Rmult_le_pos; auto).
    replace ((A - 2*(C/B)*C + (C/B)^2*B)*B) with (A*B-C^2) in H7 by (field; exact H6).
    lra.
Qed.

Lemma lemma_13_39_a : ∀ (n : nat) (a b : nat -> R),
  (∑ 1 n (λ i, a i * b i))^2 <=
  (∑ 1 n (λ i, a i ^ 2)) * (∑ 1 n (λ i, b i ^ 2)).
Abort.

Lemma lemma_13_39_b : ∀ f g a b,
  a < b -> integrable_on a b f -> integrable_on a b g ->
  (∫ a b (f ⋅ g))^2 <= (∫ a b (λ x, f x ^ 2)) * (∫ a b (λ x, g x ^ 2)).
Proof.
  exact lemma_13_39.
Qed.

Lemma lemma_13_39_c_counterexample : ∃ f g : R -> R,
  integrable_on 0 1 f /\ integrable_on 0 1 g /\
  (∫ 0 1 (λ x, g x ^ 2)) > 0 /\
  (∫ 0 1 (f ⋅ g))^2 = (∫ 0 1 (λ x, f x ^ 2)) * (∫ 0 1 (λ x, g x ^ 2)) /\
  ~ (∃ c, ∀ x, x ∈ [0, 1] -> f x = c * g x).
Abort.

Lemma lemma_13_39_c_zero : ∃ f g : R -> R,
  continuous_on f [0, 1] /\ continuous_on g [0, 1] /\
  (∀ x, x ∈ [0, 1] -> g x = 0) /\
  (∫ 0 1 (f ⋅ g))^2 = (∫ 0 1 (λ x, f x ^ 2)) * (∫ 0 1 (λ x, g x ^ 2)) /\
  ~ (∃ c, ∀ x, x ∈ [0, 1] -> f x = c * g x).
Proof.
  exists (λ _, 1), (λ _, 0). repeat split; try auto_cont; auto.
  - assert (H1 : ∫ 0 1 (λ _, 0) = 0) by auto_int.
    replace ((λ _ : R, 1) ⋅ (λ _ : R, 0)) with (λ _ : R, 0)
      by (extensionality x; ring).
    replace (λ _ : R, 0^2) with (λ _ : R, 0) by (extensionality x; ring).
    rewrite H1. ring.
  - intros [c H1]. specialize (H1 0 ltac:(solve_R)). lra.
Qed.

Lemma integral_square_zero_13_39 : ∀ h a b,
  a < b -> continuous_on h [a, b] ->
  ∫ a b (λ x, h x^2) = 0 -> ∀ x, x ∈ [a, b] -> h x = 0.
Proof.
  intros h a b H1 H2 H3 x H4.
  destruct (Req_dec (h x) 0) as [H5 | H5]; auto.
  assert (H6 : 0 < ∫ a b (λ x, h x^2)).
  {
    apply integral_pos'; auto.
    - intros y H6. nra.
    - exists x. split; auto. nra.
    - replace (λ x, h x^2) with (h ⋅ h) by (extensionality y; ring).
      apply continuous_on_mult; auto.
  }
  lra.
Qed.

Lemma lemma_13_39_c : ∀ f g a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] ->
  ((∫ a b (f ⋅ g))^2 = (∫ a b (λ x, f x ^ 2)) * (∫ a b (λ x, g x ^ 2)) <->
   (∀ x, x ∈ [a, b] -> g x = 0) \/
   (∃ c, ∀ x, x ∈ [a, b] -> f x = c * g x)).
Proof.
  intros f g a b H1 H2 H3.
  assert (H4 : integrable_on a b f) by (apply theorem_13_3; auto; lra).
  assert (H5 : integrable_on a b g) by (apply theorem_13_3; auto; lra).
  assert (H6 : integrable_on a b (λ x, g x^2)).
  { replace (λ x, g x^2) with (g ⋅ g) by (extensionality x; ring).
    apply lemma_13_38_e; auto. }
  split.
  - intros H7.
    destruct (Req_dec (∫ a b (λ x, g x^2)) 0) as [H8 | H8].
    + left. apply integral_square_zero_13_39; auto.
    + set (t := (∫ a b (f ⋅ g)) / (∫ a b (λ x, g x^2))).
      assert (H9 : ∫ a b (λ x, (f x - t*g x)^2) = 0).
      {
        rewrite integral_square_difference_13_39; auto. unfold t.
        field_simplify; [rewrite H7; field; exact H8 | exact H8].
      }
      assert (H10 : continuous_on (λ x, f x - t*g x) [a, b]).
      { apply continuous_on_minus; auto. apply continuous_on_mult_const_l; auto. }
      pose proof integral_square_zero_13_39 _ a b H1 H10 H9 as H11.
      right. exists t. intros x H12. specialize (H11 x H12). lra.
  - intros [H7 | [t H7]].
    + assert (H8 : ∫ a b (f ⋅ g) = 0).
      {
        transitivity (∫ a b (λ _, 0)); [|auto_int].
        apply integral_ext; try lra. intros x H8. cbn beta. rewrite H7; auto. ring.
      }
      assert (H9 : ∫ a b (λ x, g x^2) = 0).
      {
        transitivity (∫ a b (λ _, 0)); [|auto_int].
        apply integral_ext; try lra. intros x H9. rewrite H7; auto. ring.
      }
      rewrite H8, H9. ring.
    + assert (H8 : ∫ a b (f ⋅ g) = t * ∫ a b (λ x, g x^2)).
      {
        rewrite <- integral_mult_scalar; auto.
        apply integral_ext; try lra. intros x H8. cbn beta. rewrite H7; auto. ring.
      }
      assert (H9 : ∫ a b (λ x, f x^2) = t^2 * ∫ a b (λ x, g x^2)).
      {
        rewrite <- integral_mult_scalar; auto.
        apply integral_ext; try lra. intros x H9. rewrite H7; auto. ring.
      }
      rewrite H8, H9. ring.
Qed.

Lemma lemma_13_39_d : ∀ f,
  integrable_on 0 1 f -> (∫ 0 1 f)^2 <= ∫ 0 1 (λ x, f x ^ 2).
Proof.
  intros f H1.
  assert (H2 : integrable_on 0 1 (λ _, 1)) by (apply theorem_13_3; [lra | auto_cont]).
  pose proof lemma_13_39 f (λ _, 1) 0 1 ltac:(lra) H1 H2 as H3.
  cbn beta in H3. replace (λ x, f x * 1) with f in H3 by (extensionality x; ring).
  assert (H4 : ∫ 0 1 (λ _ : R, 1^2) = 1) by auto_int.
  cbn beta in H3. rewrite H4 in H3. lra.
Qed.

Lemma lemma_13_39_d_intervals : ∀ a b,
  a < b ->
  ((∀ f, integrable_on a b f -> (∫ a b f)^2 <= ∫ a b (λ x, f x ^ 2)) <->
   b - a <= 1).
Proof.
  intros a b H1.
  assert (H2 : integrable_on a b (λ _, 1)) by (apply theorem_13_3; [lra | auto_cont]).
  assert (H3 : ∫ a b (λ _, 1) = b-a).
  { apply FTC2 with (g := λ x, x); auto; [auto_cont | auto_diff]. }
  assert (H4 : (λ _ : R, 1^2) = (λ _ : R, 1)) by (extensionality x; ring).
  split.
  - intros H5. specialize (H5 (λ _, 1) H2). cbn beta in H5. rewrite H4, H3 in H5. nra.
  - intros H5 f H6.
    pose proof lemma_13_39 f (λ _, 1) a b H1 H6 H2 as H7.
    cbn beta in H7. replace (λ x, f x * 1) with f in H7 by (extensionality x; ring).
    cbn beta in H7. rewrite H4, H3 in H7.
    assert (H8 : 0 <= ∫ a b (λ x, f x^2)).
    {
      apply integral_nonneg; try lra.
      - intros x H8. nra.
      - replace (λ x, f x^2) with (f ⋅ f) by (extensionality x; ring).
        apply lemma_13_38_e; auto.
    }
    nra.
Qed.
