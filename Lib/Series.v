From Lib Require Import Imports Sums Sequence Reals_util Notations Integral Sets Interval Derivative Continuity.
Import SequenceNotations SumNotations IntegralNotations SetNotations IntervalNotations DerivativeNotations.

Open Scope R_scope.

Definition partial_sum (a : sequence) (n : nat) := ∑ 0 n a.

Definition series_sum (a : sequence) (L : R) : Prop :=
  ⟦ lim ⟧ (partial_sum a) = L.

Definition series_converges (a : sequence) : Prop :=
  convergent_sequence (partial_sum a).

Definition series_converges_absolutely (a : sequence) : Prop :=
  series_converges (fun n => Rabs (a n)).

Definition series_diverges (a : sequence) : Prop :=
  divergent_sequence (partial_sum a).

Definition series_diverges_pinf (a : sequence) : Prop :=
  limit_s_pinf (partial_sum a).

Definition series_diverges_ninf (a : sequence) : Prop :=
  limit_s_ninf (partial_sum a).

Module SeriesNotations.

  Declare Scope series_scope.
  Delimit Scope series_scope with series.

  Notation "'∑' 0 '∞' a '=' S" := 
    (series_sum a S)
      (at level 45, a at level 0, S at level 0, 
       format "'∑'  0  '∞'  a  '='  S") : series_scope.

  Notation "'∑' 0 '∞' a '=' '∞'" := 
    (series_diverges_pinf a)
      (at level 45, a at level 0, 
       format "'∑'  0  '∞'  a  '='  '∞'") : series_scope.

  Notation "'∑' 0 '∞' a '=' '-∞'" := 
    (series_diverges_ninf a)
      (at level 45, a at level 0, 
       format "'∑'  0  '∞'  a  '='  '-∞'") : series_scope.

  Open Scope series_scope.
       
End SeriesNotations.

Import SeriesNotations.

Section section_35_2.
  Let a : sequence := (fun n => 1).

  Example example_35_2_1 : map (partial_sum a) (seq 0 4) = [1; 2; 3; 4].
  Proof. auto_list. Qed.

  (* From this we can guess that the partial sums are equal to their ending bound + 1.
     We will now prove this by induction. *)

  Lemma nth_term_in_series_sequence_35_2 : forall n, partial_sum a n = (INR n + 1).
  Proof.
    unfold partial_sum, a. induction n as [| k IH].
    - sum_simpl. reflexivity.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. solve_INR.
  Qed.

  Lemma sequence_of_partial_sums_diverges_35_2 : series_diverges a.
  Proof.
    intros L. exists 1; split; try lra.
    intros N. pose proof INR_unbounded (Rmax N L) as [n H1]. exists n. split. solve_max.
    rewrite nth_term_in_series_sequence_35_2. assert (INR n > L) as H2 by solve_max. solve_abs.
  Qed.
End section_35_2.

Section section_35_3.
  Let b : sequence := (fun n => 1 / (INR n + 1) - 1 / (INR n + 2)).

  Example example_35_3_1 : map b (seq 0 4) = [1 / 2; 1 / 6; 1 / 12; 1 / 20].
  Proof. auto_list. Qed.

  Example example_35_3_2 : map (partial_sum b) (seq 0 5) = [1/2; 2/3; 3/4; 4/5; 5/6].
  Proof. auto_list. Qed.

  Lemma nth_term_in_series_sequence_35_3 : forall n, partial_sum b n = 1 - (1 / (INR n + 2)).
  Proof.
    unfold partial_sum, b. induction n as [| k IH].
    - sum_simpl. reflexivity.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. assert (0 <= INR k) by (apply pos_INR). solve_INR.
  Qed.

  Lemma sequence_of_partial_sums_converges_35_3 : series_converges b.
  Proof.
    exists 1. intros ε H1. exists (1 / ε - 2). intros n H2. rewrite nth_term_in_series_sequence_35_3.
    pose proof pos_INR n as H3. assert (-1 / (INR n + 2) < 0) as H4. { apply Rdiv_neg_pos; try lra. }
    replace ((|(1 - 1 / (INR n + 2) - 1)|)) with (1 / (INR n + 2)); solve_abs.
    apply Rplus_gt_compat_r with (r := 2) in H2; apply Rmult_gt_compat_r with (r := ε) in H2;
    apply Rmult_gt_compat_r with (r := / (INR n + 2)) in H2; field_simplify in H2; try lra.
  Qed.
End section_35_3.

Section section_35_5.
  Let a : sequence := (fun n => 1 / 2 ^ n).

  Example example_35_5_1 : map (partial_sum a) (seq 0 4) = [1; 3/2; 7/4; 15/8].
  Proof. auto_list. Qed.

  Lemma nth_term_in_series_sequence_35_5 : forall n, partial_sum a n = (2 - 1 / 2 ^ n).
  Proof.
    unfold partial_sum, a. induction n as [| k IH].
    - sum_simpl. lra.
    - rewrite sum_f_i_Sn_f; try lia. rewrite IH. assert (2^k <> 0) by (clear; induction k; simpl; lra).
      solve_INR.
  Qed.
End section_35_5.

Lemma partial_sum_rec : forall a n,
  (n > 0)%nat -> partial_sum a n = partial_sum a (n - 1) + a n.
Proof.
  intros a n H1. unfold partial_sum. replace n with (S (n - 1)) by lia.
  rewrite sum_f_i_Sn_f; try lia. replace (S (n - 1)) with n by lia. reflexivity.
Qed.

(*
  we can just use solve_abs but this is the reasoning that makes sense to people
  |an|  = |sn − sn−1|
        = |(sn − L) + (L − sn−1)|
        ≤ |sn − L| + |L − sn−1| (by the triangle inequality)
        = |sn − L| + |sn−1 − L|
        < ε/2 + ε/2
        = ε
*)
Theorem theorem_35_6 : forall a : sequence,
  series_converges a -> ⟦ lim ⟧ a = 0.
Proof.
  intros a [L H1] ε H2. specialize (H1 (ε / 2) ltac:(nra)) as [M H4].
  exists (Rmax 1 (M + 1)). intros n H5. apply Rmax_Rgt in H5 as [H5 H6].
  assert (INR (n - 1) > M) as H7. { solve_INR. apply INR_le. solve_INR. }
  specialize (H4 n ltac:(lra)) as H8. specialize (H4 (n - 1)%nat ltac:(auto)) as H9.
  assert (n > 0)%nat as H10. { apply INR_lt. solve_INR. } rewrite partial_sum_rec in H8; try lia.
  solve_abs.
Qed.

Lemma contra_2 : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
    intros P Q H1 H2 H3. apply H2. apply H1. apply H3.
Qed.

Theorem theorem_35_7 : forall a : sequence,
  ~ ⟦ lim ⟧ a = 0 -> series_diverges a.
Proof.
  intros a H1. pose proof theorem_35_6 a as H2. apply contra_2 in H2; auto.
  unfold series_diverges. apply divergent_sequence_iff. intros H3. apply H2.
  unfold series_converges. auto.
Qed.

Example example_35_8 : series_diverges (fun n => INR (n + 3) / INR (2 * n - 21)).
Proof.
  apply theorem_35_7. intros H1. pose proof Proposition_34_19 as H2.
  assert (0 = 1/2) as H3. { apply limit_of_sequence_unique with (a := fun n => INR (n + 3) / INR (2 * n - 21)); auto. }
  lra.
Qed.

Example example_35_9 : series_diverges (fun n => (-1) ^ n).
Proof.
  apply theorem_35_7. intros H1. pose proof proposition_34_16 as H2.
  specialize (H2 0). apply not_limit_of_sequence_iff in H2. tauto.
Qed.

Definition rearrangement (b a : sequence) := 
  exists f : ℕ -> ℕ, 
    (forall n m, f n = f m -> n = m) /\ 
    (forall n, exists m, f m = n) /\ 
    (forall n, b n = a (f n)).

Definition sequence_contains_all_products (c a b : sequence) :=
  exists f : ℕ -> (ℕ * ℕ), 
    (forall n m, f n = f m -> n = m) /\ 
    (forall i j, exists n, f n = pair i j) /\ 
    (forall n, c n = a (fst (f n)) * b (snd (f n))).

Theorem theorem_23_cauchy_criterion : forall a,
  series_converges a <-> cauchy_sequence (partial_sum a).
Proof.
Abort.

Theorem theorem_23_vanishing_condition : forall a,
  series_converges a -> ⟦ lim ⟧ a = 0.
Proof.
Abort.

Theorem theorem_23_boundedness_criterion : forall a,
  (forall n, a n >= 0) -> (series_converges a <-> Sequence.bounded_above (partial_sum a)).
Proof.
Abort.

Theorem theorem_23_1 : forall a b,
  (forall n, 0 <= a n /\ a n <= b n) -> series_converges b -> series_converges a.
Proof.
Abort.

Theorem theorem_23_2 : forall a b c,
  (forall n, a n > 0) -> (forall n, b n > 0) -> c <> 0 ->
  ⟦ lim ⟧ (fun n => a n / b n) = c ->
  (series_converges a <-> series_converges b).
Proof.
Abort.

Theorem theorem_23_3 : forall a r,
  (forall n, a n > 0) -> ⟦ lim ⟧ (fun n => a (S n) / a n) = r ->
  (r < 1 -> series_converges a) /\ (r > 1 -> series_diverges a).
Proof.
Abort.

Theorem theorem_23_4 : forall f a,
  (forall x, f x > 0) -> (forall x y, 1 <= x -> x <= y -> f y <= f x) ->
  (forall n, (n >= 1)%nat -> a n = f n) ->
  (series_converges a <-> exists L, ⟦ lim ⟧ (fun N => ∫ 1 N f) = L).
Proof.
Abort.

Theorem theorem_23_5 : forall a,
  series_converges_absolutely a -> series_converges a.
Proof.
Abort.

Theorem theorem_23_6 : forall a,
  nonincreasing a -> (forall n, a n >= 0) -> ⟦ lim ⟧ a = 0 ->
  series_converges (fun n => (-1)^(n+1) * a n).
Proof.
Abort.

Theorem theorem_23_7 : forall a α,
  series_converges a -> ~ series_converges_absolutely a ->
  exists b, rearrangement b a /\ ∑ 0 ∞ b = α.
Proof.
Abort.

Theorem theorem_23_8 : forall a b L,
  series_converges_absolutely a -> ∑ 0 ∞ a = L -> rearrangement b a ->
  series_converges_absolutely b /\ ∑ 0 ∞ b = L.
Proof.
Abort.

Theorem theorem_23_9 : forall a b c La Lb,
  series_converges_absolutely a -> ∑ 0 ∞ a = La ->
  series_converges_absolutely b -> ∑ 0 ∞ b = Lb ->
  sequence_contains_all_products c a b ->
  ∑ 0 ∞ c = (La * Lb).
Proof.
Abort.

Definition pointwise_limit (fn : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  ∀ x, x ∈ D -> ⟦ lim ⟧ (fun n => fn n x) = f x.

Definition uniform_limit (fn : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ N : ℕ, ∀ n : ℕ, (n > N)%nat -> ∀ x, x ∈ D -> |f x - fn n x| < ε.

Definition uniform_series_limit (fn : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  uniform_limit (fun n x => partial_sum (fun k => fn k x) n) f D.

Theorem theorem_24_1 : forall (fn : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) a b,
  (forall n, integrable_on a b (fn n)) ->
  integrable_on a b f ->
  uniform_limit fn f [a, b] ->
  ⟦ lim ⟧ (fun n => ∫ a b (fn n)) = ∫ a b f.
Proof.
Abort.

Theorem theorem_24_2 : forall (fn : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) a b,
  (forall n, continuous_on (fn n) [a, b]) ->
  uniform_limit fn f [a, b] ->
  continuous_on f [a, b].
Proof.
Abort.

Theorem theorem_24_3 : forall (fn fn' : ℕ -> ℝ -> ℝ) (f g : ℝ -> ℝ) a b,
  (forall n, ⟦ der ⟧ (fn n) [a, b] = fn' n) ->
  (forall n, integrable_on a b (fn' n)) ->
  pointwise_limit fn f [a, b] ->
  continuous_on g [a, b] ->
  uniform_limit fn' g [a, b] ->
  ⟦ der ⟧ f [a, b] = g.
Proof.
Abort.

Corollary corollary_24_1_1 : forall (fn : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) a b,
  (forall n, continuous_on (fn n) [a, b]) ->
  uniform_series_limit fn f [a, b] ->
  continuous_on f [a, b].
Proof.
Abort.

Corollary corollary_24_1_2 : forall (fn : ℕ -> ℝ -> ℝ) (f : ℝ -> ℝ) a b,
  (forall n, integrable_on a b (fn n)) ->
  integrable_on a b f ->
  uniform_series_limit fn f [a, b] ->
  ∑ 0 ∞ (fun n => ∫ a b (fn n)) = ∫ a b f.
Proof.
Abort.

Corollary corollary_24_1_3 : forall (fn fn' : ℕ -> ℝ -> ℝ) (f g : ℝ -> ℝ) a b,
  (forall n, ⟦ der ⟧ (fn n) [a, b] = fn' n) ->
  (forall n, integrable_on a b (fn' n)) ->
  (forall x, x ∈ [a, b] -> ∑ 0 ∞ (fun n => fn n x) = (f x)) ->
  continuous_on g [a, b] ->
  uniform_series_limit fn' g [a, b] ->
  ⟦ der ⟧ f [a, b] = g.
Proof.
Abort.

Theorem theorem_24_4_Weierstrass_M_test : forall (fn : ℕ -> ℝ -> ℝ) (M : sequence) (A : Ensemble ℝ),
  (forall n x, x ∈ A -> |fn n x| <= M n) ->
  series_converges M ->
  exists f : ℝ -> ℝ, 
    uniform_series_limit fn f A /\
    (forall x, x ∈ A -> series_converges_absolutely (fun n => fn n x)).
Proof.
Abort.

Parameter dist_to_nearest_integer : ℝ -> ℝ.

Theorem theorem_24_5 : exists f : ℝ -> ℝ,
  (forall x, ∑ 0 ∞ (fun n => 1 / 10^n * dist_to_nearest_integer (10^n * x)) = (f x)) /\
  continuous f /\ (~ exists f', ⟦ der ⟧ f = f').
Proof.
Abort.

Theorem theorem_24_6 : forall (a : sequence) (x0 c : ℝ),
  x0 <> 0 -> 0 < c < |x0| ->
  series_converges (fun n => a n * x0^n) ->
  (exists f : ℝ -> ℝ, uniform_series_limit (fun n x => a n * x^n) f [-c, c]) /\
  (exists g : ℝ -> ℝ, uniform_series_limit (fun n x => INR n * a n * x^(n-1)%nat) g [-c, c]) /\
  (forall f g : ℝ -> ℝ,
     (forall x, |x| < |x0| -> ∑ 0 ∞ (fun n => a n * x^n) = (f x)) ->
     (forall x, |x| < |x0| -> ∑ 0 ∞ (fun n => INR n * a n * x^(n-1)%nat) = (g x)) ->
     ⟦ der ⟧ f (-|x0|, |x0|) = g).
Proof.
Abort.