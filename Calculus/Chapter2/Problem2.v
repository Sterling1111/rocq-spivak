From Calculus.Chapter2 Require Import Prelude.

Lemma lemma_2_2_i : ∀ n : nat,
  (n >= 1)%nat -> ∑ 1 n (λ (i : ℕ), 2 * (i) - 1) = ((n^2)%nat : ℝ).
Proof.
  intros n H. induction n as [| k IH].
  - lia.
  - assert (k = 0 \/ k = 1 \/ k > 1)%nat as [H1 | [H1 | H1]] by lia.
    -- rewrite H1. compute. lra.
    -- rewrite H1. compute. lra.
    -- assert (k >= 1)%nat as H2 by lia. apply IH in H2. rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite H2. replace (S k ^ 2)%nat with (k^2 + 2 * k + 1)%nat. 2 : { simpl. repeat rewrite Nat.mul_1_r. lia. }
       replace (k^2 + 2 * k + 1)%nat with (k^2 + (2 * k + 1))%nat by lia. rewrite plus_INR.
       replace (2 * (S k)%nat - 1) with (((2 * k + 1)%nat : ℝ)).
       2 : { rewrite S_INR. repeat rewrite plus_INR. rewrite mult_INR. simpl. lra. }
       lra.
Qed.

Lemma lemma_2_2_ii : ∀ n : nat,
  (n >= 1)%nat -> ∑ 1 n (λ (i : ℕ), (2 * i - 1)^2) = n * (2 * n + 1) * (2 * n - 1) / 3.
Proof.
  intros n H. induction n as [| k IH].
  - lia.
  - assert (k = 0 \/ k = 1 \/ k > 1)%nat as [H1 | [H1 | H1]] by lia.
    -- rewrite H1. compute. lra.
    -- rewrite H1. compute. lra.
    -- assert (k >= 1)%nat as H2 by lia. apply IH in H2. rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite H2. replace (((S k)%nat : ℝ)) with (k + 1). 2 : { rewrite S_INR. auto. }
       field.
Qed.