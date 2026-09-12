From Calculus.Chapter8 Require Import Prelude.

Definition norm (f : ℝ -> ℝ) : ℝ :=
  epsilon (inhabits 0) (fun M =>
    (forall x, x ∈ [0, 1] -> |f x| <= M) /\
    (forall M',
      (forall x, x ∈ [0, 1] -> |f x| <= M') ->
      M <= M')).

Notation "‖ f ‖" := (norm f)
  (at level 35, format "‖ f ‖").

Lemma norm_spec_full : forall f,
  bounded_on f [0, 1] ->
  (forall x, x ∈ [0, 1] -> |f x| <= ‖ f ‖) /\
  (forall M,
    (forall x, x ∈ [0, 1] -> |f x| <= M) ->
    ‖ f ‖ <= M).
Proof.
  intros f H1. unfold norm.

  assert (H2 : exists M, forall x, x ∈ [0, 1] -> |f x| <= M).
  {
    destruct H1 as [[M1 H3] [M2 H4]].

    exists (Rmax (|M1|) (|M2|)).
    intros x H5.

    specialize (H3 (f x)
      ltac:(exists x; split; [exact H5 | reflexivity])).
    specialize (H4 (f x)
      ltac:(exists x; split; [exact H5 | reflexivity])).

    solve_R.
  }

  destruct H2 as [M H2].

  set (A := fun y =>
    exists x, x ∈ [0, 1] /\ y = |f x|).

  assert (H3 : has_upper_bound A).
  {
    exists M.
    intros y [x [H4 H5]].
    rewrite H5.
    apply H2.
    exact H4.
  }

  assert (H4 : A ≠ ∅).
  {
    apply not_Empty_In.
    exists (|f 0|).
    exists 0.
    split; [solve_R | reflexivity].
  }

  destruct (completeness_upper_bound A H3 H4)
    as [M' [H5 H6]].

  assert (H7 :
    exists M0,
      (forall x, x ∈ [0, 1] -> |f x| <= M0) /\
      (forall M1,
        (forall x, x ∈ [0, 1] -> |f x| <= M1) ->
        M0 <= M1)).
  {
    exists M'.
    split.

    - intros x H7.
      apply H5.
      exists x.
      split; [exact H7 | reflexivity].

    - intros M0 H7.
      apply H6.
      intros y [x [H8 H9]].
      rewrite H9.
      apply H7.
      exact H8.
  }

  exact (epsilon_spec (inhabits 0) _ H7).
Qed.

Lemma norm_spec : forall f x,
  bounded_on f [0, 1] ->
  x ∈ [0, 1] ->
  |f x| <= ‖ f ‖.
Proof.
  intros f x H1 H2.
  destruct (norm_spec_full f H1) as [H3 _].
  apply H3.
  exact H2.
Qed.

Lemma norm_least : forall f M,
  bounded_on f [0, 1] ->
  (forall x, x ∈ [0, 1] -> |f x| <= M) ->
  ‖ f ‖ <= M.
Proof.
  intros f M H1 H2.
  destruct (norm_spec_full f H1) as [_ H3].
  apply H3.
  exact H2.
Qed.

Lemma norm_nonneg : forall f,
  bounded_on f [0, 1] ->
  0 <= ‖ f ‖.
Proof.
  intros f H1.
  pose proof (norm_spec f 0 H1 ltac:(solve_R)) as H2.
  pose proof (Rabs_pos (f 0)) as H3.
  lra.
Qed.

Lemma lemma_8_9_a : forall f c,
  bounded_on f [0, 1] ->
  ‖ (fun x => c * f x) ‖ = |c| * ‖ f ‖.
Proof.
  intros f c H1. pose proof norm_spec f.
Abort.

Lemma lemma_8_9_b : forall f g,
  bounded_on f [0, 1] ->
  bounded_on g [0, 1] ->
  ‖ (fun x => f x + g x) ‖ <= ‖ f ‖ + ‖ g ‖.
Proof.
Abort.

Lemma lemma_8_9_c : forall h f g,
  bounded_on h [0, 1] ->
  bounded_on f [0, 1] ->
  bounded_on g [0, 1] ->
  ‖ (fun x => h x - f x) ‖ <=
    ‖ (fun x => h x - g x) ‖ +
    ‖ (fun x => g x - f x) ‖.
Proof.
Abort.