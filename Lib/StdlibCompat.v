From Lib Require Import Completeness.
From Lib Require Import Imports Notations Limit Derivative Integral Continuity Reals_util Trigonometry Sets Interval Exponential Sequence Series Sums Partition Sorted_Rlt.
From Coquelicot Require SF_seq RInt.
Import LimitNotations DerivativeNotations SetNotations IntervalNotations SequenceNotations SeriesNotations SumNotations.

Open Scope R_scope.

Lemma limit_compat : forall f a L,
  ⟦ lim a ⟧ f = L <-> limit1_in f (λ x : R, x ≠ a) L a.
Proof.
  split; intros H1 ε H2.
  - unfold limit in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit1_in. unfold limit_in.
    exists δ; split; auto.
    intros x [H5 H6]. simpl in H6.
    apply H4. split; [| auto]. apply Rabs_pos_lt. lra.
  - unfold limit1_in, limit_in in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit. exists δ; split; auto.
    intros x [H5 H6]. apply H4. split; auto.
    intro H7; subst. replace (a - a)%R with 0%R in H5 by lra. rewrite Rabs_R0 in H5; lra.
Qed.

Lemma derivative_compat : forall f f' a,
  ⟦ der a ⟧ f = f' <-> derivable_pt_lim f a (f' a).
Proof.
  split.
  - intros H1 ε H2. unfold derivative_at, limit in H1.
    destruct (H1 ε H2) as [δ [H3 H4]].
    exists (mkposreal δ H3). intros h H5 H6.
    apply H4. split; auto.
    + apply Rabs_pos_lt; lra.
    + replace (h - 0) with h by lra; exact H6.
  - intros H1. unfold derivative_at, limit. intros ε H2.
    destruct (H1 ε H2) as [δ H3].
    exists δ. split. apply cond_pos.
    intros h [H4 H5]. apply H3.
    + intro H6; subst; replace (0 - 0)%R with 0%R in H4 by lra; rewrite Rabs_R0 in H4; lra.
    + replace h with (h - 0)%R by lra; exact H5.
Qed.

Lemma continuous_compat : forall f a,
  continuous_at f a <-> continuity_pt f a.
Proof.
  split; intros H1.
  - unfold continuity_pt, continue_in. unfold D_x, no_cond.
    assert (H2 : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H2. apply limit_compat. apply H1.
  - unfold continuity_pt, continue_in in H1. unfold D_x, no_cond in H1.
    assert (H2 : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H2 in H1. apply limit_compat in H1. apply H1.
Qed.

Lemma right_limit_compat : forall f a L,
  ⟦ lim a⁺ ⟧ f = L <-> limit1_in f (fun x => a < x) L a.
Proof.
  split; intros H1 ε H2.
  - unfold right_limit in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit1_in, limit_in.
    exists δ; split; auto.
    intros x [H5 H6]. apply H4. simpl in H6.
    unfold Rdist in *; rewrite Rabs_pos_eq in H6; lra.
  - unfold limit1_in, limit_in in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold right_limit. exists δ; split; auto.
    intros x H5. apply H4. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_pos_eq; lra.
Qed.

Lemma left_limit_compat : forall f a L,
  ⟦ lim a⁻ ⟧ f = L <-> limit1_in f (fun x => x < a) L a.
Proof.
  split; intros H1 ε H2.
  - unfold left_limit in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit1_in, limit_in.
    exists δ; split; auto.
    intros x [H5 H6]. apply H4. simpl in H6.
    unfold Rdist in *; rewrite Rabs_left in H6; lra.
  - unfold limit1_in, limit_in in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold left_limit. exists δ; split; auto.
    intros x H5. apply H4. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_left; lra.
Qed.

Lemma right_continuous_compat : forall f a,
  continuous_at_right f a <-> continue_in f (fun x => a <= x) a.
Proof.
  split; intros H1.
  - unfold continuous_at_right in H1. unfold continue_in.
    assert (H2 : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H2.
    apply right_limit_compat. apply H1.
  - unfold continuous_at_right. unfold continue_in, D_x in H1.
    assert (H2 : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H2 in H1.
    apply right_limit_compat in H1. apply H1.
Qed.

Lemma left_continuous_compat : forall f a,
  continuous_at_left f a <-> continue_in f (fun x => x <= a) a.
Proof.
  split; intros H1.
  - unfold continuous_at_left in H1. unfold continue_in.
    assert (H2 : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H2.
    apply left_limit_compat. apply H1.
  - unfold continuous_at_left. unfold continue_in, D_x in H1.
    assert (H2 : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H2 in H1.
    apply left_limit_compat in H1. apply H1.
Qed.

Lemma derivative_all_compat : forall f f',
  ⟦ der ⟧ f = f' <-> (forall x, derivable_pt_lim f x (f' x)).
Proof.
  split; intros H1 x; apply derivative_compat; apply H1.
Qed.

Lemma continuous_all_compat : forall f,
  continuous f <-> (forall x, continuity_pt f x).
Proof.
  split; intros H1 x; apply continuous_compat; apply H1.
Qed.

Lemma definite_integral_compat_FTC : forall f F a b pr,
  a < b ->
  (forall x, a <= x <= b -> continuous_at f x) ->
  ⟦ der ⟧ F [a, b] = f ->
  definite_integral a b f = RiemannInt (f:=f) (a:=a) (b:=b) pr.
Proof.
  intros f F a b pr H1 H2 H3.
  assert (H4 : a <= b) by lra.
  assert (H5 : forall x : R, a <= x <= b -> continuity_pt f x).
  { intros x H6. apply continuous_compat. apply H2. apply H6. }
  rewrite (RiemannInt_P20 H4 (FTC_P1 H4 H5) pr).
  apply FTC2.
  - exact H1.
  - apply continuous_on_closed_interval_iff; auto. split; [|split].
    + intros x H6. apply H2. split.
      * left. exact (proj1 H6).
      * left. exact (proj2 H6).
    + apply continuous_at_imp_right_continuous. apply H2. lra.
    + apply continuous_at_imp_left_continuous. apply H2. lra.
  - apply derivative_at_imp_derivative_on.
    + apply differentiable_domain_closed. exact H1.
    + intros x H6. apply derivative_compat. apply RiemannInt_P28. exact H6.
Qed.

Lemma continuous_implies_RiemannInt_compat : forall f a b,
  a <= b -> continuous_on f [a, b] -> Riemann_integrable f a b.
Proof.
  intros f a b H1 H2.
  pose proof (total_order_T a b) as [[H3 | H3] | H3]; [| | lra].
  - set (g := fun t => if Rle_dec t a then f a else if Rle_dec b t then f b else f t).
    apply Riemann_integrable_ext with (f := g).
    + intros x [H4 H5]. unfold g. destruct (Rle_dec x a) as [H6|H6]; destruct (Rle_dec b x) as [H7|H7].
      * unfold Rmin in H4; unfold Rmax in H5; destruct (Rle_dec a b); [assert (x = a) by lra; subst; reflexivity | lra].
      * unfold Rmin in H4; unfold Rmax in H5; destruct (Rle_dec a b); [assert (x = a) by lra; subst; reflexivity | lra].
      * unfold Rmin in H4; unfold Rmax in H5; destruct (Rle_dec a b); [assert (x = b) by lra; subst; reflexivity | lra].
      * reflexivity.
    + apply continuity_implies_RiemannInt; auto.
      intros x H4. apply continuous_compat. unfold continuous_at.
      assert (x < a \/ x > b \/ x = a \/ x = b \/ a < x < b) as H5 by lra.
      destruct H5 as [H6 | [H6 | [H6 | [H6 | H6]]]].
      * assert (g x = f a) as H7. { unfold g. destruct (Rle_dec x a); [|lra]. reflexivity. }
        rewrite H7. apply limit_eq with (f1 := fun _ => f a).
        -- exists (a - x). split; [lra|]. intros y H8. unfold g. destruct (Rle_dec y a); [|solve_abs; lra]. reflexivity.
        -- apply limit_const.
      * assert (g x = f b) as H7. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [|lra]. reflexivity. }
        rewrite H7. apply limit_eq with (f1 := fun _ => f b).
        -- exists (x - b). split; [lra|]. intros y H8. unfold g. destruct (Rle_dec y a); [solve_abs; lra|]. destruct (Rle_dec b y); [|solve_abs; lra]. reflexivity.
        -- apply limit_const.
      * assert (g x = f a) as H7. { unfold g. destruct (Rle_dec x a); [|lra]. reflexivity. }
        rewrite H7. apply limit_iff. split.
        -- apply limit_left_eq with (f1 := fun _ => f a).
           ++ exists 1. split; [lra|]. intros y H8. unfold g. destruct (Rle_dec y a); [|lra]. reflexivity.
           ++ apply limit_left_const.
        -- apply continuous_on_closed_interval_iff in H2 as [H8 [H9 H10]]; auto.
           unfold continuous_at_right in H9.
           apply limit_right_eq with (f1 := f).
           ++ exists (b - a). split; [lra|]. intros y H11. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
           ++ subst; exact H9.
      * assert (g x = f b) as H7. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [|lra]. reflexivity. }
        rewrite H7. apply limit_iff. split.
        -- apply continuous_on_closed_interval_iff in H2 as [H8 [H9 H10]]; auto.
           unfold continuous_at_left in H10.
           apply limit_left_eq with (f1 := f).
           ++ exists (b - a). split; [lra|]. intros y H11. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
           ++ subst; exact H10.
        -- apply limit_right_eq with (f1 := fun _ => f b).
           ++ exists 1. split; [lra|]. intros y H11. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [|lra]. reflexivity.
           ++ subst; apply limit_right_const.
      * assert (g x = f x) as H7. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [lra|]. reflexivity. }
        rewrite H7. apply continuous_on_closed_interval_iff in H2 as [H8 [H9 H10]]; auto.
        specialize (H8 x ltac:(solve_R)). unfold continuous_at in H8.
        apply limit_eq with (f1 := f).
        -- exists (Rmin (x - a) (b - x)). split; [apply Rmin_pos; lra|]. intros y H11. unfold g.
           assert (a < y < b) as H12. { unfold Rmin in H11; destruct (Rle_dec (x - a) (b - x)); solve_abs. }
           destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
        -- apply H8.
  - subst. apply RiemannInt_P7.
Qed.

Local Notation length := List.length.

Local Lemma stdlib_nth : forall (A : Type) (l : list A) d i,
  seq.nth d l i = List.nth i l d.
Proof. intros A l. induction l as [|x l H1]; intros d [|i]; simpl; auto. Qed.

Local Lemma stdlib_size : forall (A : Type) (l : list A), seq.size l = length l.
Proof. intros A l. induction l as [|x l H1]; simpl; auto. Qed.

Local Lemma stdlib_head : forall (l : list R), seq.head 0 l = l.[0].
Proof. intros [|x l]; simpl; [reflexivity|reflexivity]. Qed.

Local Lemma stdlib_last : forall (l : list R) d,
  l <> [] -> seq.last d l = l.[length l-1].
Proof.
  induction l as [|x l H1]; intros d H2; [contradiction|].
  destruct l as [|y l].
  - reflexivity.
  - simpl length. replace (S (S (length l))-1)%nat with (S (length l)) by lia.
    simpl List.nth. change (seq.last x (y::l) = (y::l).[length l]).
    rewrite H1 by discriminate. f_equal. simpl length. lia.
Qed.

Local Lemma stdlib_sorted : forall l, Sorted Rlt l -> SF_seq.sorted Rle l.
Proof.
  intros l H1. induction H1 as [|x l H1 H2 H3]; [exact I|].
  destruct l as [|y l]; [exact I|]. simpl. split; [inversion H3; lra|exact H2].
Qed.

Local Definition stdlib_partition_seq a b (P : partition a b) (v : list R) : @SF_seq.SF_seq R :=
  SF_seq.mkSF_seq ((points a b P).[0]) (combine (tl (points a b P)) v).

Local Lemma stdlib_unzip_combine : forall (l v : list R),
  length l = length v ->
  seq.unzip1 (combine l v) = l /\ seq.unzip2 (combine l v) = v.
Proof.
  induction l as [|x l H1]; intros [|y v] H2; simpl in *; try discriminate; [auto|].
  destruct (H1 v ltac:(lia)) as [H3 H4]. simpl. rewrite H3, H4. auto.
Qed.

Local Lemma stdlib_partition_seq_spec : forall a b (P : partition a b) v,
  length v = (length (points a b P)-1)%nat ->
  SF_seq.SF_lx (stdlib_partition_seq a b P v) = points a b P /\
  SF_seq.SF_ly (stdlib_partition_seq a b P v) = v.
Proof.
  intros a b P v H1. pose proof partition_length a b P as H2.
  assert (H3 : length (tl (points a b P)) = length v).
  { destruct (points a b P); simpl in *; lia. }
  destruct (stdlib_unzip_combine _ _ H3) as [H4 H5].
  unfold SF_seq.SF_lx, SF_seq.SF_ly, stdlib_partition_seq. simpl. rewrite H4, H5.
  split; [destruct (points a b P); simpl in *; [lia|reflexivity]|reflexivity].
Qed.

Local Definition stdlib_partition_stepfun a b (P : partition a b) (v : list R)
  (H1 : length v = (length (points a b P)-1)%nat) : StepFun a b.
Proof.
  refine (@mkStepFun a b (SF_seq.SF_fun (stdlib_partition_seq a b P v) 0) _).
  exists (points a b P), v.
  pose proof SF_seq.ad_SF_compat 0 (stdlib_partition_seq a b P v)
    ltac:(unfold SF_seq.SF_sorted; rewrite (proj1 (stdlib_partition_seq_spec a b P v H1)); apply stdlib_sorted, partition_P2) as H2.
  destruct (stdlib_partition_seq_spec a b P v H1) as [H3 H4]. rewrite H3, H4 in H2.
  rewrite stdlib_head in H2.
  rewrite stdlib_last, partition_first, partition_last in H2; [exact H2|apply partition_not_empty].
Defined.

Local Lemma stdlib_partition_stepfun_value : forall a b (P : partition a b) v H1 x,
  x ∈ [a,b] -> exists i, (i < length v)%nat /\
    (points a b P).[i] <= x <= (points a b P).[i+1] /\
    stdlib_partition_stepfun a b P v H1 x = v.[i].
Proof.
  intros a b P v H1 x H2. pose proof partition_length a b P as H3.
  destruct (stdlib_partition_seq_spec a b P v H1) as [H4 H5].
  assert (H6 : SF_seq.sorted Rle (SF_seq.SF_lx (stdlib_partition_seq a b P v))).
  { rewrite H4. apply stdlib_sorted, partition_P2. }
  assert (H7 : seq.head 0 (SF_seq.SF_lx (stdlib_partition_seq a b P v)) <= x <=
              seq.last 0 (SF_seq.SF_lx (stdlib_partition_seq a b P v))).
  { rewrite H4, stdlib_head.
    rewrite stdlib_last, partition_first, partition_last; [solve_R|apply partition_not_empty]. }
  change (exists i, (i < length v)%nat /\ (points a b P).[i] <= x <= (points a b P).[i+1] /\ SF_seq.SF_fun (stdlib_partition_seq a b P v) 0 x = v.[i]).
  rewrite (SF_seq.SF_fun_incr _ 0 x H6 H7).
  destruct (SF_seq.sorted_dec _ 0 x H6 H7) as [[i [[H8 H9] H10]]|H8].
  - cbn [proj1_sig]. rewrite H4 in H8, H9, H10. rewrite !stdlib_nth in H8, H9. rewrite stdlib_size in H10.
    rewrite H5, stdlib_nth. exists i. split; [lia|]. split; [replace (i+1)%nat with (S i) by lia; lra|reflexivity].
  - rewrite H4, !stdlib_nth, stdlib_size in H8.
    assert (H9 : SF_seq.SF_size (stdlib_partition_seq a b P v) = length v).
    { unfold SF_seq.SF_size, stdlib_partition_seq. simpl SF_seq.SF_t.
      rewrite stdlib_size, length_combine. destruct (points a b P); simpl in *; lia. }
    rewrite H9, H5, stdlib_nth.
    exists (length v-1)%nat. split; [lia|]. split; [rewrite H1; replace (length (points a b P)-1-1+1)%nat with (length (points a b P)-1)%nat by lia; replace (length (points a b P)-1-1)%nat with (length (points a b P)-2)%nat by lia; exact H8|reflexivity].
Qed.

Local Lemma stdlib_Int_SF_sum : forall v l,
  length l = S (length v) ->
  Int_SF v l = ∑ 0 (length v-1) (fun i => v.[i] * (l.[i+1]-l.[i])).
Proof.
  induction v as [|u v H1]; intros l H2.
  - rewrite sum_f_0_0. simpl. ring.
  - destruct l as [|x l]; [simpl in H2; lia|].
    destruct l as [|y l]; [simpl in H2; lia|].
    replace (length (u::v)-1)%nat with (length v) by (simpl; lia).
    destruct v as [|w v].
    + simpl in H2. assert (H3 : l=[]).
      { apply length_zero_iff_nil. simpl in H2. lia. } subst.
      rewrite sum_f_0_0. simpl. ring.
    + rewrite sum_f_Si by (simpl; lia).
      rewrite (sum_f_reindex _ 1 (length (w::v)) 1) by (simpl; lia).
      simpl Nat.sub. replace (length v-0)%nat with (length (w::v)-1)%nat by (simpl; lia).
      change (u*(y-x) + Int_SF (w::v) (y::l) =
        ∑ 0 (length (w::v)-1) (fun i => (u::w::v).[i+1] * ((x::y::l).[i+1+1]-(x::y::l).[i+1])) + u*(y-x)).
      rewrite (H1 (y::l)) by (simpl in *; lia).
      assert (H3 : ∑ 0 (length (w::v)-1) (fun i => (w::v).[i] * ((y::l).[i+1]-(y::l).[i])) =
        ∑ 0 (length (w::v)-1) (fun i => (u::w::v).[i+1] * ((x::y::l).[i+1+1]-(x::y::l).[i+1]))).
      { apply sum_f_equiv; [lia|]. intros i H4. repeat rewrite Nat.add_1_r. reflexivity. }
      rewrite H3. ring.
Qed.

Local Lemma stdlib_partition_stepfun_integral : forall a b (P : partition a b) v H1,
  RiemannInt_SF (stdlib_partition_stepfun a b P v H1) =
  ∑ 0 (length v-1) (fun i => v.[i] * ((points a b P).[i+1]-(points a b P).[i])).
Proof.
  intros a b P v H1. pose proof partition_length a b P as H2.
  unfold RiemannInt_SF. destruct (Rle_dec a b) as [H3|H3]; [|pose proof partition_P1 a b P as H4; lra].
  change (Int_SF v (points a b P) = ∑ 0 (length v-1) (fun i => v.[i] * ((points a b P).[i+1]-(points a b P).[i]))).
  apply stdlib_Int_SF_sum. lia.
Qed.

Local Lemma darboux_to_stdlib_integrable : forall f a b,
  a <= b -> Integral.integrable_on a b f -> Riemann_integrable f a b.
Proof.
  intros f a b H1 H2. destruct (Req_EM_T a b) as [H3|H3]; [subst; apply RiemannInt_P7|].
  assert (H4 : a < b) by lra.
  pose proof integrable_imp_bounded f a b H1 H2 as H5.
  set (bf := mkbounded_function_R a b f H1 H5).
  intros ε.
  destruct (constructive_indefinite_description _ (proj1 (theorem_13_2_a a b bf H4) H2 ε (cond_pos ε))) as [P H6].
  destruct (partition_sublist_elem_has_inf f a b P H5) as [lo [H7 H8]] eqn:H9.
  destruct (partition_sublist_elem_has_sup f a b P H5) as [hi [H10 H11]] eqn:H12.
  set (φ := stdlib_partition_stepfun a b P lo H7).
  set (θ := stdlib_partition_stepfun a b P hi H10).
  exists φ, (mkStepFun (StepFun_P28 (-1) θ φ)). split.
  - intros x H13. assert (H14 : x ∈ [a,b]) by solve_R.
    destruct (stdlib_partition_stepfun_value a b P lo H7 x H14) as [i [H15 [H16 H17]]].
    destruct (stdlib_partition_stepfun_value a b P hi H10 x H14) as [j [H18 [H19 H20]]].
    pose proof glb_le_all_In _ _ (f x) (H8 i H15) ltac:(exists x; split; [exact H16|reflexivity]) as H21.
    pose proof lub_ge_all_In _ _ (f x) (H11 j H18) ltac:(exists x; split; [exact H19|reflexivity]) as H22.
    change (|f x - φ x| <= θ x + -1 * φ x).
    unfold φ, θ. rewrite H17, H20. rewrite Rabs_right by lra. lra.
  - rewrite StepFun_P30.
    unfold φ, θ. rewrite !stdlib_partition_stepfun_integral.
    unfold lower_sum, upper_sum, bf in H6. simpl in H6. rewrite H9, H12 in H6. simpl in H6.
    assert (H13 : L(bf,P) <= U(bf,P)) by apply lower_sum_le_upper_sum.
    unfold lower_sum, upper_sum, bf in H13. simpl in H13. rewrite H9, H12 in H13. simpl in H13.
    rewrite Rabs_right by lra. lra.
Qed.

Local Lemma stdlib_map : forall (A B : Type) (f : A -> B) l,
  seq.map f l = List.map f l.
Proof. intros A B f l. induction l as [|x l H1]; simpl; congruence. Qed.

Local Lemma stdlib_partition_seq_size : forall a b (P : partition a b) v,
  length v = (length (points a b P)-1)%nat ->
  SF_seq.SF_size (stdlib_partition_seq a b P v) = length v.
Proof.
  intros a b P v H1. pose proof partition_length a b P as H2.
  unfold SF_seq.SF_size, stdlib_partition_seq. simpl SF_seq.SF_t.
  rewrite stdlib_size, length_combine. destruct (points a b P); simpl in *; lia.
Qed.

Local Lemma stdlib_partition_seq_pointed : forall a b (P : partition a b) c,
  is_tagging a b P c -> SF_seq.pointed_subdiv (stdlib_partition_seq a b P c).
Proof.
  intros a b P c [H1 H2]. intros i H3.
  rewrite stdlib_partition_seq_size in H3 by exact H1.
  destruct (stdlib_partition_seq_spec a b P c H1) as [H4 H5].
  rewrite H4, H5, !stdlib_nth. replace (S i) with (i+1)%nat by lia. apply H2; exact H3.
Qed.

Local Lemma stdlib_seq_step_lt : forall l δ,
  0 < δ ->
  (forall i, (i < length l-1)%nat -> |l.[i+1]-l.[i]| < δ) -> SF_seq.seq_step l < δ.
Proof.
  induction l as [|x l H1]; intros δ H2 H3; [exact H2|].
  destruct l as [|y l]; [exact H2|].
  change (Rmax (|y-x|) (SF_seq.seq_step (y::l)) < δ).
  apply Rmax_lub_lt.
  - apply (H3 0%nat). simpl; lia.
  - apply H1; [exact H2|]. intros i H4. specialize (H3 (S i) ltac:(simpl in *; lia)).
    replace (S i+1)%nat with (S (i+1)) in H3 by lia. exact H3.
Qed.

Local Lemma stdlib_partition_seq_mesh : forall a b (P : partition a b) c δ,
  is_tagging a b P c -> 0 < δ -> mesh_lt a b P δ ->
  SF_seq.seq_step (SF_seq.SF_lx (stdlib_partition_seq a b P c)) < δ.
Proof.
  intros a b P c δ [H1 H2] H3 H4.
  rewrite (proj1 (stdlib_partition_seq_spec a b P c H1)).
  apply stdlib_seq_step_lt; [exact H3|]. intros i H5.
  rewrite Rabs_right by (pose proof partition_width_pos a b P i H5 as H6; lra). apply H4; exact H5.
Qed.

Local Lemma stdlib_partition_riemann_sum : forall a b f (P : partition a b) c,
  is_tagging a b P c ->
  @SF_seq.Riemann_sum Hierarchy.R_ModuleSpace f (stdlib_partition_seq a b P c) = riemann_sum a b f P c.
Proof.
  intros a b f P c [H1 H2].
  assert (H3 : SF_seq.SF_sorted Rle (stdlib_partition_seq a b P c)).
  { unfold SF_seq.SF_sorted. rewrite (proj1 (stdlib_partition_seq_spec a b P c H1)). apply stdlib_sorted, partition_P2. }
  rewrite (SF_seq.Riemann_sum_compat f _ H3).
  unfold RiemannInt_SF.
  change ((if Rle_dec (seq.head 0 (SF_seq.SF_lx (SF_seq.SF_map f (stdlib_partition_seq a b P c))))
                       (seq.last 0 (SF_seq.SF_lx (SF_seq.SF_map f (stdlib_partition_seq a b P c))))
    then Int_SF (SF_seq.SF_ly (SF_seq.SF_map f (stdlib_partition_seq a b P c)))
                (SF_seq.SF_lx (SF_seq.SF_map f (stdlib_partition_seq a b P c)))
    else -Int_SF (SF_seq.SF_ly (SF_seq.SF_map f (stdlib_partition_seq a b P c)))
                 (SF_seq.SF_lx (SF_seq.SF_map f (stdlib_partition_seq a b P c)))) = riemann_sum a b f P c).
  rewrite SF_seq.SF_map_lx, SF_seq.SF_map_ly.
  destruct (stdlib_partition_seq_spec a b P c H1) as [H4 H5]. rewrite H4, H5, stdlib_map, stdlib_head.
  rewrite stdlib_last, partition_first, partition_last by apply partition_not_empty.
  destruct (Rle_dec a b) as [H6|H6]; [|pose proof partition_P1 a b P as H7; lra].
  rewrite stdlib_Int_SF_sum by (rewrite length_map; pose proof partition_length a b P as H7; lia).
  unfold riemann_sum. rewrite length_map, H1.
  apply sum_f_equiv; [lia|]. intros i H7. rewrite map_nth_in_bounds with (d:=0); [reflexivity|].
  pose proof partition_length a b P as H8. lia.
Qed.

Local Lemma stdlib_to_is_riemann_integral : forall f a b (pr : Riemann_integrable f a b),
  a < b -> is_riemann_integral a b f (RiemannInt pr).
Proof.
  intros f a b pr H1.
  pose proof RInt.ex_RInt_Reals_aux_1 f a b pr as H2.
  intros ε H3. specialize (H2 _ (@Hierarchy.locally_ball Hierarchy.R_UniformSpace (RiemannInt pr) (mkposreal ε H3))).
  unfold SF_seq.Riemann_fine, Hierarchy.within, Hierarchy.locally_dist in H2.
  destruct H2 as [δ H2]. exists δ. split; [apply cond_pos|].
  intros P c H4 H5.
  assert (H6 : SF_seq.pointed_subdiv (stdlib_partition_seq a b P c) /\
    SF_seq.SF_h (stdlib_partition_seq a b P c) = Rmin a b /\
    seq.last (SF_seq.SF_h (stdlib_partition_seq a b P c)) (SF_seq.SF_lx (stdlib_partition_seq a b P c)) = Rmax a b).
  { split; [apply stdlib_partition_seq_pointed; exact H4|]. split.
    - unfold stdlib_partition_seq. simpl SF_seq.SF_h. rewrite partition_first. solve_R.
    - rewrite (proj1 (stdlib_partition_seq_spec a b P c (proj1 H4))).
      rewrite stdlib_last, partition_last by apply partition_not_empty. solve_R. }
  specialize (H2 (stdlib_partition_seq a b P c)
    (stdlib_partition_seq_mesh a b P c δ H4 (cond_pos δ) H5) H6).
  rewrite Rcomplements.sign_eq_1 in H2 by lra.
  change (|1 * @SF_seq.Riemann_sum Hierarchy.R_ModuleSpace f (stdlib_partition_seq a b P c) - RiemannInt pr| < ε) in H2. rewrite Rmult_1_l in H2.
  rewrite stdlib_partition_riemann_sum in H2 by exact H4. exact H2.
Qed.

Lemma is_riemann_integral_stdlib_compat : forall f a b L,
  a < b ->
  (is_riemann_integral a b f L <-> exists pr : Riemann_integrable f a b, L = RiemannInt pr).
Proof.
  intros f a b L H1. split.
  - intros H2.
    pose proof riemann_integral_implies_darboux_integrable a b f L H1 H2 as H3.
    exists (darboux_to_stdlib_integrable f a b ltac:(lra) H3).
    apply is_riemann_integral_unique with (a:=a) (b:=b) (f:=f); [exact H1|exact H2|].
    apply stdlib_to_is_riemann_integral; exact H1.
  - intros [pr H2]. rewrite H2. apply stdlib_to_is_riemann_integral; exact H1.
Qed.

Lemma riemann_integrable_on_stdlib_compat : forall f a b,
  a <= b ->
  (riemann_integrable_on a b f <-> inhabited (Riemann_integrable f a b)).
Proof.
  intros f a b H1. split.
  - intros H2. constructor. apply darboux_to_stdlib_integrable; [exact H1|].
    apply riemann_darboux_integrable_equiv; exact H2.
  - intros [pr]. destruct (Req_EM_T a b) as [H2|H2]; [left; exact H2|].
    right. split; [lra|]. exists (RiemannInt pr). apply stdlib_to_is_riemann_integral; lra.
Qed.

Lemma integrable_on_implies_Riemann_integrable : forall f a b,
  a <= b -> Integral.integrable_on a b f ->
  {pr : Riemann_integrable f a b | True}.
Proof.
  intros f a b H1 H2. exists (darboux_to_stdlib_integrable f a b H1 H2). exact I.
Qed.

Lemma Riemann_integrable_implies_integrable : forall f a b,
  a <= b -> {pr : Riemann_integrable f a b | True} ->
    a <= b -> Integral.integrable_on a b f.
Proof.
  intros f a b H1 [pr H2] H3. apply riemann_darboux_integrable_equiv.
  apply riemann_integrable_on_stdlib_compat; [exact H1|constructor; exact pr].
Qed.

Lemma riemann_integral_compat : forall f a b (pr : Riemann_integrable f a b),
  a <= b -> riemann_integral a b f = RiemannInt pr.
Proof.
  intros f a b pr H1. destruct (Req_EM_T a b) as [H2|H2].
  - subst. rewrite riemann_integral_n_n. symmetry. apply RiemannInt_P9.
  - assert (H3 : a < b) by lra.
    apply is_riemann_integral_unique with (a:=a) (b:=b) (f:=f); [exact H3| |].
    + apply riemann_integral_correct; [exact H3|]. apply riemann_integrable_on_stdlib_compat; [exact H1|constructor; exact pr].
    + apply stdlib_to_is_riemann_integral; exact H3.
Qed.

Lemma definite_integral_compat : forall f a b pr,
  a <= b ->
  Integral.definite_integral a b f = RiemannInt (f:=f) (a:=a) (b:=b) pr.
Proof.
  intros f a b pr H1. rewrite <- riemann_integral_compat by exact H1.
  symmetry. apply riemann_darboux_integral_equiv.
Qed.

Lemma darboux_integrable_stdlib_compat : forall f a b,
  a <= b ->
  (Integral.integrable_on a b f <-> inhabited (Riemann_integrable f a b)).
Proof.
  intros f a b H1. rewrite <- riemann_darboux_integrable_equiv.
  apply riemann_integrable_on_stdlib_compat; exact H1.
Qed.

Lemma riemann_integral_compat_general : forall f a b (pr : Riemann_integrable f a b),
  riemann_integral a b f = RiemannInt pr.
Proof.
  intros f a b pr. destruct (Rle_dec a b) as [H1|H1].
  - apply riemann_integral_compat; exact H1.
  - rewrite riemann_integral_b_a_neg, (RiemannInt_P8 pr (RiemannInt_P1 pr)).
    rewrite (riemann_integral_compat f b a (RiemannInt_P1 pr)) by lra. reflexivity.
Qed.

Lemma definite_integral_compat_general : forall f a b (pr : Riemann_integrable f a b),
  Integral.definite_integral a b f = RiemannInt pr.
Proof.
  intros f a b pr. rewrite <- riemann_integral_compat_general.
  symmetry. apply riemann_darboux_integral_equiv.
Qed.

Lemma darboux_integral_compat : forall f a b (pr : Riemann_integrable f a b),
  darboux_integral a b f = RiemannInt pr.
Proof. intros f a b pr. apply definite_integral_compat_general. Qed.

Definition trig_diff (x : R) := 
  (Trigonometry.cos x - Rtrigo_def.cos x)^2 + (Trigonometry.sin x - Rtrigo_def.sin x)^2.

Lemma Rtrigo_der_sin : ⟦ der ⟧ Rtrigo_def.sin = Rtrigo_def.cos.
Proof.
  apply derivative_all_compat. intros x.
  apply derivable_pt_lim_sin.  
Qed.

Lemma Rtrigo_der_cos : ⟦ der ⟧ Rtrigo_def.cos = (fun x => - Rtrigo_def.sin x).
Proof.
  apply derivative_all_compat. intros x.
  apply derivable_pt_lim_cos.
Qed.

Lemma derivative_trig_diff : ⟦ der ⟧ trig_diff = (λ _, 0).
Proof.
  pose proof Rtrigo_der_sin as H1.
  pose proof Rtrigo_der_cos as H2.
  unfold trig_diff.
  eapply derivative_ext.
  2: {
    eapply derivative_plus.
    - simpl. eapply derivative_mult.
      + eapply derivative_minus.
        * apply derivative_cos.
        * exact H2.
      + eapply derivative_mult.
        * eapply derivative_minus.
          -- apply derivative_cos.
          -- exact H2.
        * apply derivative_const.
    - simpl. eapply derivative_mult.
      + eapply derivative_minus.
        * apply derivative_sin.
        * exact H1.
      + eapply derivative_mult.
        * eapply derivative_minus.
          -- apply derivative_sin.
          -- exact H1.
        * apply derivative_const.
  }
  intros x. lra.
Qed.

Lemma trig_diff_0 : trig_diff 0 = 0.
Proof.
  unfold trig_diff. 
  rewrite cos_0, sin_0.
  assert (H1 : Rtrigo_def.cos 0 = 1) by exact Rtrigo_def.cos_0.
  assert (H2 : Rtrigo_def.sin 0 = 0) by exact Rtrigo_def.sin_0.
  rewrite H1, H2. lra.
Qed.

Lemma trig_diff_const : forall x, trig_diff x = 0.
Proof.
  intros x.
  pose proof (derivative_zero_imp_const trig_diff (Rmin 0 x - 1) (Rmax 0 x + 1)) as [c H1].
  - solve_R.
  - apply derivative_imp_derivative_on_closed.
    + solve_R.
    + apply derivative_trig_diff.
  - assert (H2: 0 ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    assert (H3: x ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    pose proof (H1 0 H2) as H4.
    pose proof (H1 x H3) as H5.
    rewrite <- H4 in H5. rewrite trig_diff_0 in H5. exact H5.
Qed.

Lemma cos_compat_pt : forall x, Trigonometry.cos x = Rtrigo_def.cos x.
Proof.
  intros x.
  pose proof (trig_diff_const x) as H1.
  unfold trig_diff in H1.
  assert (H2 : 0 <= (cos x - Rtrigo_def.cos x)^2) by apply pow2_ge_0.
  assert (H3 : 0 <= (sin x - Rtrigo_def.sin x)^2) by apply pow2_ge_0.
  assert (H4 : (cos x - Rtrigo_def.cos x)^2 <= 0) by lra.
  assert (H5 : (cos x - Rtrigo_def.cos x)^2 = 0) by lra.
  assert (H6 : forall r : R, r^2 = r * r). { intros r. simpl. lra. }
  rewrite H6 in H5.
  apply Rmult_integral in H5. destruct H5; lra.
Qed.

Lemma sin_compat_pt : forall x, Trigonometry.sin x = Rtrigo_def.sin x.
Proof.
  intros x.
  pose proof (trig_diff_const x) as H1.
  unfold trig_diff in H1.
  assert (H2 : 0 <= (cos x - Rtrigo_def.cos x)^2) by apply pow2_ge_0.
  assert (H3 : 0 <= (sin x - Rtrigo_def.sin x)^2) by apply pow2_ge_0.
  assert (H4 : (sin x - Rtrigo_def.sin x)^2 <= 0) by lra.
  assert (H5 : (sin x - Rtrigo_def.sin x)^2 = 0) by lra.
  assert (H6 : forall r : R, r^2 = r * r). { intros r. simpl. lra. }
  rewrite H6 in H5.
  apply Rmult_integral in H5. destruct H5; lra.
Qed.

Lemma cos_compat : Trigonometry.cos = Rtrigo_def.cos.
Proof.
  extensionality x. apply cos_compat_pt.
Qed.

Lemma sin_compat : Trigonometry.sin = Rtrigo_def.sin.
Proof.
  extensionality x. apply sin_compat_pt.
Qed.

Lemma Rtrigo_der_exp : ⟦ der ⟧ Rtrigo_def.exp = Rtrigo_def.exp.
Proof.
  apply derivative_all_compat. intros x.
  apply derivable_pt_lim_exp.  
Qed.

Lemma exp_diff_der_0 : ⟦ der ⟧ (fun x => exp x * Rtrigo_def.exp (-x)) = (fun x => 0).
Proof.
  pose proof Rtrigo_der_exp as H1.
  pose proof theorem_18_2 as H2.
  assert (H_eq : (λ x : R, exp x * Rtrigo_def.exp (- x)) = (λ x : R, exp x * Rtrigo_def.exp (0 - x))).
  { apply functional_extensionality. intro. f_equal. f_equal. lra. }
  rewrite H_eq.
  eapply derivative_ext.
  2: {
    eapply derivative_mult.
    - apply derivative_exp.
    - eapply derivative_comp with (f := fun x => 0 - x).
      + eapply derivative_minus.
        * apply derivative_const.
        * apply derivative_id.
      + exact H1.
  }
  intros x. simpl. unfold "∘". lra.
Qed.

Lemma exp_diff_const : forall x, Exponential.exp x * Rtrigo_def.exp (-x) = 1.
Proof.
  intros x.
  pose proof (derivative_zero_imp_const (fun x => exp x * Rtrigo_def.exp (-x)) (Rmin 0 x - 1) (Rmax 0 x + 1)) as [c H1].
  - solve_R.
  - apply derivative_imp_derivative_on_closed.
    + solve_R.
    + apply exp_diff_der_0.
  - assert (H2: 0 ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    assert (H3: x ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    pose proof (H1 0 H2) as H4.
    pose proof (H1 x H3) as H5.
    rewrite <- H4 in H5. assert (exp 0 * Rtrigo_def.exp (-0) = 1) as H6.
    { rewrite exp_0. replace (-0) with 0 by lra. rewrite Rtrigo_def.exp_0. lra. }
    rewrite H6 in H5. exact H5.
Qed.

Lemma exp_compat_pt : forall x, Exponential.exp x = Rtrigo_def.exp x.
Proof.
  intros x.
  pose proof (exp_diff_const x) as H1. 
  pose proof exp_pos x as H2.
  assert (H3: exp x * Rtrigo_def.exp (-x) * Rtrigo_def.exp x = 1 * Rtrigo_def.exp x) by (f_equal; lra).
  rewrite Rmult_assoc in H3.
  rewrite <- Exp_prop.exp_plus in H3.
  replace (-x + x) with 0 in H3 by lra.
  rewrite Rtrigo_def.exp_0 in H3. lra.
Qed.

Lemma exp_compat : Exponential.exp = Rtrigo_def.exp.
Proof.
  extensionality x. apply exp_compat_pt.
Qed.

Lemma tan_compat : Trigonometry.tan = Rtrigo1.tan.
Proof.
  extensionality x. unfold Trigonometry.tan, Rtrigo1.tan.
  rewrite sin_compat_pt, cos_compat_pt. reflexivity.
Qed.

Lemma log_compat_pt : forall x, Exponential.log x = Stdlib.Reals.Rpower.ln x.
Proof.
  intros x. destruct (Rle_dec x 0) as [H1 | H1].
  - unfold log. destruct (Rle_dec x 0) as [H2 | H2]; [| exfalso; lra].
    unfold Rpower.ln. destruct (Rlt_dec 0 x) as [H3 | H3]; [exfalso; lra | reflexivity].
  - assert (H2: exp (Rpower.ln x) = x).
    { rewrite exp_compat. apply Rpower.exp_ln. lra. }
    rewrite <- H2 at 1. rewrite log_exp. reflexivity.
Qed.

Lemma ln_compat : Exponential.ln = Rpower.ln.
Proof.
  extensionality x.
  rewrite <- log_compat_pt. apply ln_eq_log.
Qed.

Lemma log_compat : Exponential.log = Stdlib.Reals.Rpower.ln.
Proof.
  extensionality x. rewrite <- ln_eq_log, ln_compat. reflexivity.
Qed.

Lemma π_compat : π = PI.
Proof.
  assert (H1: PI / 2 = π / 2).
  {
    destruct (Rlt_or_le (PI / 2) (π / 2)) as [H2 | H2].
    - exfalso.
      pose proof (cos_gt_0_on_open_pi_2 (PI / 2)) as H3.
      assert (0 < PI / 2 < π / 2) as H4.
      { split. apply PI2_RGT_0. lra. }
      specialize (H3 H4). 
      rewrite cos_compat in H3.
      rewrite cos_PI2 in H3. lra.
    - destruct (Rlt_or_le (π / 2) (PI / 2)) as [H3 | H3].
      + exfalso.
        pose proof (Rtrigo1.cos_gt_0 (π / 2)) as H4.
        assert (- (PI / 2) < π / 2 < PI / 2) as H5.
        { pose proof π_pos as H6. split; lra. }
        specialize (H4 (proj1 H5) (proj2 H5)).
        rewrite <- cos_compat in H4.
        rewrite cos_π_over_2 in H4. lra.
      + lra. 
  }
  lra.
Qed.

Lemma arcsin_compat_pt : forall x, -1 <= x <= 1 -> arcsin x = asin x.
Proof.
  intros x H1.
  pose proof (arcsin_spec) as [H2 [H3 [H4 H5]]].
  assert (x ∈ [-1, 1]) as H6 by exact H1.
  specialize (H5 x H6).
  specialize (H3 x H6).
  apply (f_equal asin) in H5.
  rewrite sin_compat in H5.
  rewrite asin_sin in H5.
  - exact H5.
  - assert (- (π / 2) <= arcsin x <= π / 2) as H7.
    { apply H3. }
    rewrite π_compat in H7. lra.
Qed.

Lemma arccos_compat_pt : forall x, -1 <= x <= 1 -> arccos x = acos x.
Proof.
  intros x H1.
  pose proof (arccos_spec) as [H2 [H3 [H4 H5]]].
  assert (x ∈ [-1, 1]) as H6 by exact H1.
  specialize (H5 x H6).
  specialize (H3 x H6).
  apply (f_equal acos) in H5.
  rewrite cos_compat in H5.
  rewrite acos_cos in H5.
  - exact H5.
  - assert (0 <= arccos x <= π) as H7.
    { apply H3. }
    rewrite π_compat in H7. lra.
Qed.

Lemma arctan_compat : arctan = atan.
Proof.
  extensionality x.
  pose proof (arctan_spec) as [H1 [H2 [H3 H4]]].
  assert (x ∈ Full_set R) as H5 by constructor.
  specialize (H4 x H5).
  specialize (H2 x H5).
  apply (f_equal atan) in H4.
  rewrite tan_compat in H4.
  rewrite atan_tan in H4.
  - exact H4.
  - assert (- (π / 2) < arctan x < π / 2) as H6.
    { apply H2. }
    rewrite π_compat in H6. lra.
Qed.

Close Scope limit_scope.
Open Scope sequence_scope.
Open Scope series_scope.

Lemma limit_s_compat : forall a L, ⟦ lim ⟧ a = L <-> Un_cv a L.
Proof.
  split; intros H1 ε H2.
  - destruct (H1 ε H2) as [N H3].
    pose proof (INR_unbounded (Rmax N 0)) as [N_nat H4].
    exists N_nat. intros n H5.
    unfold Rdist. apply H3.
    assert (INR N_nat <= INR n). { apply le_INR. lia. }
    assert (N < INR N_nat). { apply Rmax_Rgt in H4. lra. }
    lra.
  - destruct (H1 ε H2) as [N_nat H3].
    exists (INR N_nat). intros n H4.
    unfold Rdist in H3.
    assert (INR N_nat < INR n) as H5 by lra.
    apply INR_lt in H5.
    assert (n >= N_nat)%nat as H6 by lia.
    apply H3. exact H6.
Qed.

Lemma cauchy_sequence_compat : forall a, cauchy_sequence a <-> Cauchy_crit a.
Proof.
  split; intros H1 ε H2.
  - destruct (H1 ε H2) as [N H3].
    pose proof (INR_unbounded (Rmax N 0)) as [N_nat H4].
    exists N_nat. intros n m H5 H6.
    unfold Rdist. apply H3.
    + assert (INR N_nat <= INR n). { apply le_INR. lia. }
      assert (N < INR N_nat). { apply Rmax_Rgt in H4. lra. }
      lra.
    + assert (INR N_nat <= INR m). { apply le_INR. lia. }
      assert (N < INR N_nat). { apply Rmax_Rgt in H4. lra. }
      lra.
  - destruct (H1 ε H2) as [N_nat H3].
    exists (INR N_nat). intros n m H4 H5.
    unfold Rdist in H3.
    assert (INR N_nat < INR n) as H6 by lra.
    assert (INR N_nat < INR m) as H7 by lra.
    apply INR_lt in H6. apply INR_lt in H7.
    assert (n >= N_nat)%nat as H8 by lia.
    assert (m >= N_nat)%nat as H9 by lia.
    apply H3; auto.
Qed.

Lemma partial_sum_sum_f_R0 : forall a n, partial_sum a n = sum_f_R0 a n.
Proof.
  intros a n. unfold partial_sum. unfold sum_f.
  replace (n - 0)%nat with n by lia.
  induction n.
  - simpl. replace (0 + 0)%nat with 0%nat by lia. reflexivity.
  - simpl. replace (n + 0)%nat with n by lia. rewrite IHn. reflexivity.
Qed.

Lemma series_sum_compat : forall a L, ∑ 0 ∞ a = L <-> infinite_sum a L.
Proof.
  intros a L. unfold series_sum. unfold infinite_sum.
  rewrite limit_s_compat. split; intros H1.
  - apply Un_cv_ext with (un := partial_sum a).
    + intros n. apply partial_sum_sum_f_R0.
    + exact H1.
  - apply Un_cv_ext with (un := sum_f_R0 a).
    + intros n. symmetry. apply partial_sum_sum_f_R0.
    + exact H1.
Qed.

Lemma nondecreasing_compat : forall a, nondecreasing a <-> Un_growing a.
Proof.
  intros a. split; intros H1 n. 
  - apply H1.
  - apply H1.
Qed.

Lemma nonincreasing_compat : forall a, nonincreasing a <-> Un_decreasing a.
Proof.
  intros a. split; intros H1 n.
  - apply Rge_le. apply H1.
  - apply Rle_ge. apply H1.
Qed.

Lemma bounded_above_compat : forall a, bounded_above a <-> bound (EUn a).
Proof.
  intros a. split; intros H1.
  - destruct H1 as [UB H2]. exists UB. intros x H3. destruct H3 as [n H4]; subst. apply Rge_le, H2.
  - destruct H1 as [UB H2]. exists UB. intros n. specialize (H2 (a n) (Un_in_EUn a n)). apply Rle_ge, H2.
Qed.

Lemma bounded_below_compat : forall a, bounded_below a <-> bound (EUn (fun n => - a n)).
Proof.
  intros a. split; intros H1.
  - destruct H1 as [LB H2]. exists (-LB). intros x H3. destruct H3 as [n H4]; subst. 
    specialize (H2 n). lra.
  - destruct H1 as [LB H2]. exists (-LB). intros n. 
    specialize (H2 (- a n) (Un_in_EUn _ n)). lra.
Qed.

Lemma e_compat : e = Rtrigo_def.exp 1.
Proof.
  unfold e. apply exp_compat_pt.
Qed.

Lemma Rpower_compat_pt : forall a x, 0 < a -> Exponential.Rpower a x = Rpower.Rpower a x.
Proof.
  intros. unfold Exponential.Rpower, Rpower.Rpower.
  destruct (Rlt_dec 0 a).
  - rewrite exp_compat, log_compat. reflexivity.
  - exfalso; lra.
Qed.

Lemma Rpower_compat : forall a, 0 < a -> Exponential.Rpower a = Rpower.Rpower a.
Proof.
  intros. extensionality x. apply Rpower_compat_pt; auto.
Qed.

Lemma sinh_compat_pt : forall x, Exponential.sinh x = Rtrigo_def.sinh x.
Proof.
  intros x. unfold sinh, Rtrigo_def.sinh.
  repeat rewrite exp_compat_pt. reflexivity.
Qed.

Lemma cosh_compat_pt : forall x, Exponential.cosh x = Rtrigo_def.cosh x.
Proof.
  intros x. unfold cosh, Rtrigo_def.cosh.
  repeat rewrite exp_compat_pt. reflexivity.
Qed.

Lemma tanh_compat_pt : forall x, Exponential.tanh x = Rtrigo_def.tanh x.
Proof.
  intros x. unfold tanh, Rtrigo_def.tanh.
  rewrite sinh_compat_pt, cosh_compat_pt.
  reflexivity.
Qed.

Lemma sinh_compat : sinh = Rtrigo_def.sinh.
Proof. extensionality x. apply sinh_compat_pt. Qed.

Lemma cosh_compat : cosh = Rtrigo_def.cosh.
Proof. extensionality x. apply cosh_compat_pt. Qed.

Lemma tanh_compat : tanh = Rtrigo_def.tanh.
Proof. extensionality x. apply tanh_compat_pt. Qed.

Lemma continuous_on_closed_compat : forall f a b,
  a < b ->
  (forall x, a <= x <= b -> continuity_pt f x) ->
  continuous_on f [a, b].
Proof.
  intros f a b H1 H2.
  apply continuous_on_closed_interval_iff; auto. split; [|split].
  - intros x H3. apply continuous_compat. apply H2. solve_R.
  - apply continuous_at_imp_right_continuous. apply continuous_compat. apply H2. lra.
  - apply continuous_at_imp_left_continuous. apply continuous_compat. apply H2. lra.
Qed.

Lemma continuous_on_open_compat : forall f a b,
  continuous_on f (a, b) <-> (forall x, a < x < b -> continuity_pt f x).
Proof.
  split; intros H1.
  - intros x H2. apply continuous_compat. unfold continuous_at.
    unfold continuous_on, limit_on in H1.
    specialize (H1 x ltac:(solve_R)).
    intros ε H3. specialize (H1 ε H3) as [δ [H4 H5]].
    exists (Rmin δ (Rmin (b - x) (x - a))); split; [solve_R |].
    intros x2 H6. apply H5. solve_R. solve_R.
  - apply continuous_at_imp_continuous_on.
    intros x H2. apply continuous_compat. apply H1. solve_R.
Qed.