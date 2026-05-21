From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_29 : forall n f,
  (0 < n)%nat ->
  (forall x, x >= 0 -> f x = x^n) ->
  (forall x, x <= 0 -> f x = 0) ->
  nth_differentiable (n - 1) f /\ ~ nth_differentiable_at n f 0.
Proof.
  intros n f H1 H2 H3.

  assert (H4 : ∀ k x, x > 0 -> (0 <= k <= n - 1)%nat -> ⟦ der ^ k x ⟧ f = λ x, n! / (n - k)! * x^(n - k)).
  {
    intros k x H4 H5.
    apply nth_derivative_at_eq with (f1 := fun y => y ^ n).
    - exists x. split; [solve_R |].
      intros y H6. symmetry. apply H2. solve_R.
    - apply nth_derivative_imp_at.
      apply nth_derivative_pow. lia.
  }
  
  assert (H5 : ∀ k x, x < 0 -> ⟦ der ^ k x ⟧ f = λ _, 0).
  {
    intros k x H5.
    apply nth_derivative_at_eq with (f1 := fun _ => 0).
    - exists (- x). split; [lra |].
      intros y H6. symmetry. apply H3. solve_R.
    - destruct k; [ simpl; lra | apply nth_derivative_at_const; lia ].
  }
Abort.