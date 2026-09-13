From Calculus.Chapter22 Require Import Prelude Problem20 Problem22.

Lemma lemma_22_23_a : ∀ f c,
  c < 1 ->
  (∀ x y, |f x - f y| <= c * |x - y|) ->
  continuous f.
Proof.
  intros f c H1 H2 a ε H3. exists ε. split; [lra |].
  intros x H4. specialize (H2 x a). pose proof (Rabs_pos (x-a)). nra.
Qed.

Lemma lemma_22_23_b : ∀ f c,
  c < 1 ->
  (∀ x y, |f x - f y| <= c * |x - y|) ->
  ∀ x y, f x = x -> f y = y -> x = y.
Proof.
  intros f c H1 H2 x y H3 H4.
  specialize (H2 x y). rewrite H3, H4 in H2.
  assert (H5 : |x-y| = 0) by (pose proof (Rabs_pos (x-y)); nra).
  solve_R.
Qed.

Lemma lemma_22_23_c : ∀ f c x,
  c < 1 ->
  (∀ x y, |f x - f y| <= c * |x - y|) ->
  ∃ b L, b 0%nat = x /\ (∀ n, b (S n) = f (b n)) /\ ⟦ lim ⟧ b = L /\ f L = L.
Proof.
  intros f c x H1 H2.
  set (r := (1 + Rmax c 0)/2).
  assert (H3 : 0 < r < 1 /\ c <= r) by (unfold r; solve_R).
  assert (H4 : ∀ x y, Rabs (f x-f y) <= r * Rabs (x-y)).
  { intros y z. specialize (H2 y z). pose proof (Rabs_pos (y-z)). nra. }
  set (b := fix b (n : nat) : R := match n with O => x | S k => f (b k) end).
  assert (H5 : b 0%nat = x) by reflexivity.
  assert (H6 : ∀ n, b (S n) = f (b n)) by reflexivity.
  set (M := Rabs (f x-x)+1).
  assert (H7 : M > 0) by (unfold M; pose proof (Rabs_pos (f x-x)); lra).
  assert (H8 : ∀ n, Rabs (b (S n)-b n) <= r^n*M).
  { intros n. induction n as [| n IH].
    - rewrite H6, H5. unfold M. simpl. lra.
    - change (Rabs (f (b (S n))-f (b n)) <= r^(S n)*M).
      pose proof (H4 (b (S n)) (b n)). simpl pow. nra. }
  assert (H9 : cauchy_sequence (λ n, b n/M)).
  { apply lemma_22_22_c with (c := r); [tauto |].
    intros n. replace (n+1)%nat with (S n) by lia.
    replace (b (S n)/M-b n/M) with ((b (S n)-b n)/M) by (field; lra).
    rewrite Rabs_div, (Rabs_right M ltac:(lra)).
    apply (Rmult_le_reg_r M); [lra |]. field_simplify; [pose proof (H8 n); nra | lra]. }
  assert (H10 : cauchy_sequence b).
  { intros ε H10. destruct (H9 (ε/M) ltac:(apply Rdiv_pos_pos; lra)) as [N H11].
    exists N. intros n m H12 H13. specialize (H11 n m H12 H13).
    replace (b n/M-b m/M) with ((b n-b m)/M) in H11 by (field; lra).
    rewrite Rabs_div, (Rabs_right M ltac:(lra)) in H11.
    apply (Rmult_lt_reg_r (/M)); [apply Rinv_0_lt_compat; lra | exact H11]. }
  apply cauchy_convergence_criterion in H10. destruct H10 as [L H10].
  exists b, L. repeat split; auto.
  apply lemma_22_20 with (x := x).
  - apply lemma_22_23_a with (c := c); auto.
  - exists b. auto.
Qed.
