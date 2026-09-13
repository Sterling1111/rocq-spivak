From Calculus.Chapter22 Require Import Prelude.

From Calculus.Chapter8 Require Import Problem18.

Definition sequence_limsup (x : sequence) (L : ℝ) : Prop :=
  ∃ y : sequence,
    (∀ n, is_lub (λ r, ∃ k, (n <= k)%nat /\ r = x k) (y n)) /\
    ⟦ lim ⟧ y = L.

Definition sequence_liminf (x : sequence) (L : ℝ) : Prop :=
  ∃ y : sequence,
    (∀ n, is_glb (λ r, ∃ k, (n <= k)%nat /\ r = x k) (y n)) /\
    ⟦ lim ⟧ y = L.

Lemma lemma_22_27_a : ∀ x y,
  bounded x ->
  (∀ n, is_lub (λ r, ∃ k, (k >= n)%nat /\ x k = r) (y n)) ->
  convergent_sequence y.
Proof.
  intros x y [[m H1] [M H2]] H3.
  apply monotone_convergence_nonincreasing.
  - intros n. destruct (H3 (S n)) as [H4 H5].
    apply Rle_ge. apply H5. intros r [k [H6 H7]].
    destruct (H3 n) as [H8 H9]. apply H8. exists k. split; auto; lia.
  - exists m. intros n. apply Rle_trans with (r2 := x n); auto.
    destruct (H3 n) as [H4 H5]. apply H4. exists n. split; auto; lia.
Qed.

Lemma lemma_22_27_b_i : sequence_limsup (λ n, 1 / (S n)) 0.
Proof.
  exists (λ n, 1/(S n)%nat). split.
  - intros n. split.
    + intros r [k [H1 H2]]. subst r.
      pose proof (le_INR _ _ H1). rewrite !S_INR.
      pose proof (pos_INR n). pose proof (pos_INR k). solve_R.
    + intros b H1. apply H1. exists n. split; auto; lia.
  - intros ε H1. exists (1/ε). intros n H2.
    assert (H3 : 1 < ε*n).
    { apply Rmult_gt_compat_r with (r := ε) in H2; auto.
      field_simplify in H2; lra. }
    rewrite S_INR, Rminus_0_r, Rabs_right.
    + apply (Rmult_lt_reg_r (n+1)); [pose proof (pos_INR n); lra |].
      field_simplify; nra.
    + left. apply Rdiv_pos_pos; pose proof (pos_INR n); lra.
Qed.

Lemma lemma_22_27_b_ii : sequence_limsup (λ n, (-1)^(S n) / (S n)) 0.
Abort.

Lemma lemma_22_27_b_iii : sequence_limsup (λ n, (-1)^(S n) * (1 + 1 / (S n))) 1.
Abort.

Lemma lemma_22_27_b_iv : sequence_limsup (λ n, (S n) ^^ (1 / (S n))) 1.
Abort.

Lemma lemma_22_27_c : ∀ x,
  bounded x -> ∃ l u,
    sequence_liminf x l /\ sequence_limsup x u /\ l <= u.
Abort.

Lemma lemma_22_27_d : ∀ x l u,
  bounded x -> sequence_liminf x l -> sequence_limsup x u ->
  (convergent_sequence x <-> l = u) /\
  (∀ L, ⟦ lim ⟧ x = L -> L = l /\ L = u).
Abort.

Lemma lemma_22_27_e : ∀ x L,
  bounded x -> Sets.injective x ->
  (sequence_limsup x L <-> lim_sup (λ r, ∃ n, r = x n) L).
Abort.
