From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_7_a : ∀ k l : ℕ -> ℕ,
  k 0%nat = 1%nat -> l 0%nat = 1%nat ->
  (∀ n, k (S n) = (k n + 2 * l n)%nat) ->
  (∀ n, l (S n) = (k n + l n)%nat) ->
  let a := λ n, k n / l n in
  a 0%nat = 1 /\ ∀ n, a (S n) = 1 + 1 / (1 + a n).
Proof.
  intros k l H1 H2 H3 H4. cbn beta zeta.
  assert (H5 : ∀ n, (0 < l n)%nat).
  { intros n. induction n as [| n IH]; [lia | rewrite H4; lia]. }
  split.
  - rewrite H1, H2. simpl. field.
  - intros n. rewrite H3, H4, plus_INR, plus_INR, mult_INR.
    simpl. pose proof (lt_0_INR _ (H5 n)). pose proof (pos_INR (k n)).
    field. split; lra.
Qed.

Lemma lemma_22_7_b : ∀ a,
  a 0%nat = 1 -> (∀ n, a (S n) = 1 + 1 / (1 + a n)) ->
  ⟦ lim ⟧ a = √ 2.
Abort.

Lemma lemma_22_7_c : ∀ (a b : ℕ) (x : sequence),
  (0 < a)%nat -> (0 < b)%nat ->
  x 0%nat = a ->
  (∀ n, x (S n) = a + b / (a + x n)) ->
  ⟦ lim ⟧ x = √ (a ^ 2 + b).
Abort.
