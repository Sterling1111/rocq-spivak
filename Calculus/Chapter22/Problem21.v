From Calculus.Chapter22 Require Import Prelude Problem19.
From Calculus.Chapter7 Require Import Problem11.

Lemma lemma_22_21_limit : ∀ f b L,
  continuous_on f [0,1] -> (∀ n, b n ∈ [0,1]) ->
  ⟦ lim ⟧ b = L -> ⟦ lim ⟧ (λ n, f (b n)) = f L.
Proof.
  intros f b L H1 H2 H3.
  assert (H4 : L ∈ [0,1]).
  { apply lemma_22_19_a with (a := b); auto. }
  intros ε H5. destruct (H1 L H4 ε H5) as [δ [H6 H7]].
  destruct (H3 δ H6) as [N H8]. exists N. intros n H9.
  destruct (Req_dec (b n) L) as [H10 | H10].
  - rewrite H10. solve_R.
  - apply H7; auto. specialize (H8 n H9). solve_R.
Qed.

Lemma lemma_22_21_a : ∀ f x,
  continuous_on f [0, 1] ->
  (∀ y, y ∈ [0, 1] -> f y ∈ [0, 1]) ->
  increasing_on f [0, 1] ->
  x ∈ [0, 1] ->
  ∃ b L, b 0%nat = x /\ (∀ n, b (S n) = f (b n)) /\ ⟦ lim ⟧ b = L /\ f L = L.
Proof.
  intros f x H1 H2 H3 H4.
  set (b := fix b (n : nat) : R := match n with O => x | S k => f (b k) end).
  assert (H5 : b 0%nat = x) by reflexivity.
  assert (H6 : ∀ n, b (S n) = f (b n)) by reflexivity.
  assert (H7 : ∀ n, b n ∈ [0,1]).
  { intros n. induction n as [| n IH]; [rewrite H5; auto | rewrite H6; auto]. }
  assert (H8 : ∀ y z, y ∈ [0,1] -> z ∈ [0,1] -> y <= z -> f y <= f z).
  { intros y z H8 H9 H10. destruct H10 as [H10 | H10].
    - left. apply H3; auto.
    - subst z. lra. }
  assert (H9 : convergent_sequence b).
  { destruct (Rle_dec x (f x)) as [H9 | H9].
    - apply monotone_convergence_nondecreasing.
      + intros n. induction n as [| n IH].
        * rewrite H6, H5. auto.
        * change (f (b n) <= f (b (S n))). apply H8; auto.
      + exists 1. intros n. specialize (H7 n). solve_R.
    - apply monotone_convergence_nonincreasing.
      + intros n. induction n as [| n IH].
        * rewrite H6, H5. lra.
        * change (f (b n) >= f (b (S n))). apply Rle_ge. apply H8; auto; lra.
      + exists 0. intros n. specialize (H7 n). solve_R. }
  destruct H9 as [L H9]. exists b, L. repeat split; auto.
  apply limit_of_sequence_unique with (a := λ n, f (b n)).
  - apply lemma_22_21_limit; auto.
  - intros ε H10. destruct (H9 ε H10) as [N H11]. exists N.
    intros n H12. rewrite <- H6. apply H11. rewrite S_INR. lra.
Qed.

Lemma lemma_22_21_b : ∀ f g,
  continuous_on f [0, 1] -> continuous_on g [0, 1] ->
  (∀ y, y ∈ [0, 1] -> f y ∈ [0, 1]) ->
  (∀ y, y ∈ [0, 1] -> g y ∈ [0, 1]) ->
  (∀ y, y ∈ [0, 1] -> f (g y) = g (f y)) ->
  increasing_on f [0, 1] ->
  ∃ L, L ∈ [0, 1] /\ f L = L /\ g L = L.
Proof.
  intros f g H1 H2 H3 H4 H5 H6.
  destruct (lemma_7_11 g H2 H4) as [x [H7 H8]].
  destruct (lemma_22_21_a f x H1 H3 H6 H7) as [b [L [H9 [H10 [H11 H12]]]]].
  assert (H13 : ∀ n, b n ∈ [0,1]).
  { intros n. induction n as [| n IH]; [rewrite H9; auto | rewrite H10; auto]. }
  assert (H14 : ∀ n, g (b n) = b n).
  { intros n. induction n as [| n IH].
    - rewrite H9. auto.
    - rewrite H10, <- H5; auto. rewrite IH. auto. }
  exists L. split.
  - apply lemma_22_19_a with (a := b); auto.
  - split; auto. apply limit_of_sequence_unique with (a := λ n, g (b n)).
    + apply lemma_22_21_limit; auto.
    + replace (λ n, g (b n)) with b; auto. extensionality n. symmetry. apply H14.
Qed.
