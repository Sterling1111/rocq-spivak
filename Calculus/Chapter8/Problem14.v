From Calculus.Chapter8 Require Import Prelude.
From Calculus.Chapter8 Require Import Problem12.

Lemma lemma_8_14_a : ∀ a b : sequence,
  (∀ n, a n <= a (S n)) ->
  (∀ n, b (S n) <= b n) ->
  (∀ n, a n <= b n) ->
  ∃ x, ∀ n, a n <= x <= b n.
Proof. 
  intros a b H1 H2 H3.

  set (A := λ a_n, ∃ n, a_n = a n).
  set (B := λ b_n, ∃ n, b_n = b n).

  assert (H4 : ∀ n1 n2, (n1 <= n2)%nat -> a n1 <= a n2).
  {
    induction n2 as [| k IH]; intros H4.
    - destruct n1; [lra | lia].
    - assert ((n1 = S k \/ n1 <= k)%nat) as [H5 | H5] by lia.
      + subst. lra.
      + specialize (IH H5). specialize (H1 k). lra.
  }

  assert (H5 : ∀ n1 n2, (n1 <= n2)%nat -> b n2 <= b n1).
  {
    induction n2 as [| k IH]; intros H5.
    - destruct n1; [lra | lia].
    - assert ((n1 = S k \/ n1 <= k)%nat) as [H6 | H6] by lia.
      + subst. lra.
      + specialize (IH H6). specialize (H2 k). lra. 
  }
  
  assert (H6 : has_upper_bound A).
  {
    exists (b 0%nat).
    intros x [n H6].
    subst.
    specialize (H3 n).
    specialize (H5 0%nat n ltac:(lia)).
    lra.
  }

  assert (H7 : A ≠ ⦃⦄).
  { apply not_Empty_In. exists (a 0%nat), 0%nat; auto. }

  assert (H8 : has_lower_bound B).
  {
    exists (a 0%nat).
    intros x [n H8].
    subst.
    specialize (H3 n).
    specialize (H4 0%nat n ltac:(lia)).
    lra.
  }

  assert (H9 : B ≠ ⦃⦄).
  { apply not_Empty_In. exists (b 0%nat), 0%nat; auto. }

  pose proof completeness_upper_bound A H6 H7 as [sup_A H10].
  pose proof completeness_lower_bound B H8 H9 as [inf_B H11].

  assert (H12 : (∀ x y : ℝ, x ∈ A → y ∈ B → x ≤ y)).
  {
    intros x y [n1 H12] [n2 H13].
    subst.
    assert ((n1 <= n2)%nat \/ (n2 <= n1)%nat) as [H12 | H12] by lia.
    - specialize (H4 n1 n2 H12).
      specialize (H3 n2).
      lra.
    - specialize (H5 n2 n1 H12).
      specialize (H3 n1).
      lra.
  }

  pose proof lemma_8_12_b A B sup_A inf_B H7 H9 H12 H10 H11 as H13.

  exists ((sup_A + inf_B) / 2).

  intros n.

  destruct H10 as [H10 _], H11 as [H11 _].

  specialize (H10 (a n) ltac:(exists n; auto)).
  specialize (H11 (b n) ltac:(exists n; auto)).
  
  lra.
Qed.

Lemma lemma_8_14_b :
  ∃ a b : sequence,
    (∀ n, a n <= a (S n)) /\
    (∀ n, b (S n) <= b n) /\
    (∀ n, a n < b n) /\
    ~ (∃ x, ∀ n, a n < x < b n).
Proof. Abort.
