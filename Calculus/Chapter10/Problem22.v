From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_22_a : ∀ (l : list R),
  ∃ (g : R -> R), ⟦ der ⟧ g = (λ x, polynomial l x).
Proof.
  intros l. induction l as [| h t [g H1]].
  - exists (λ _, 0). replace (polynomial []) with (λ _ : ℝ, 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    auto_diff.
  - exists (λ x, h / (S (length t))%nat * x^(S (length t)) + g x).
    replace (polynomial (h :: t)) with (λ x, h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. }
    apply derivative_plus; auto.
    apply derivative_ext with (f1' := λ x,
      h / (S (length t))%nat * ((S (length t))%nat * x^(S (length t) - 1))).
    + intros x. replace (S (length t) - 1)%nat with (length t) by lia.
      field. apply not_0_INR; lia.
    + apply derivative_mult_const_l. apply derivative_pow.
Qed.

Lemma lemma_10_22_b : ∀ (m : nat) (b : nat -> R),
  (m >= 2)%nat ->
  ∃ (g : R -> R), ∀ x, x <> 0 ->
    ⟦ Der x ⟧ g = ∑ 2 m (λ k, b k / x^k).
Proof.
  intros m b H1.
  exists (λ x, ∑ 2 m (λ (k : ℕ), - b k / (k - 1) / x^(k - 1))).
  intros x H2.
  apply derivative_at_imp_derive_at with (f' := λ x, ∑ 2 m (λ k, b k / x^k)).
  apply derivative_at_sum; auto. intros k H3.
  replace k with (S (S (k - 2))) by lia.
  replace (S (S (k - 2)) - 1)%nat with (S (k - 2)) by lia.
  auto_diff.
  - apply Rmult_integral_contrapositive_currified; auto. apply pow_nonzero; auto.
  - rewrite Nat.sub_0_r.
    change (- (- b (S (S (k - 2))) / ((S (S (k - 2)))%nat - 1) *
      ((S (k - 2))%nat * x^(k - 2))) /
      (x * x^(k - 2) * (x * x^(k - 2))) =
      b (S (S (k - 2))) / (x * (x * x^(k - 2)))).
    rewrite S_INR. replace ((S (k - 2))%nat + 1 - 1) with (((S (k - 2))%nat : ℝ)) by ring.
    field. repeat split; auto using pow_nonzero, not_0_INR.
Qed.

Lemma lemma_10_22_c : ~ ∃ (n m : nat) (a b : nat -> R),
  ∀ x, x <> 0 ->
    ⟦ Der x ⟧ (λ t, ∑ 0 n (λ k, a k * t^k) + ∑ 1 m (λ k, b k / t^k)) = 1 / x.
Proof.
Abort.
