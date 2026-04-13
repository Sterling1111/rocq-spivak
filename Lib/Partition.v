From Lib Require Import Imports Notations Sorted_Rlt Completeness Continuity Sets Reals_util Interval Sums.
Import IntervalNotations SetNotations SumNotations.

Local Notation length := List.length.
Local Notation In := List.In.

Open Scope R_scope.

Record partition (a b : ℝ) : Type := mkpartition
{
  points : list ℝ; 
  partition_P1 : a < b;
  partition_P2 : Sorted Rlt points;
  partition_P3 : List.In a points;
  partition_P4 : List.In b points;
  partition_P5 : forall x, List.In x points -> a <= x <= b
}.

Lemma partition_length : forall a b (P : partition a b),
  (length (P.(points a b)) >= 2)%nat.
Proof.
  intros a b P. destruct P as [l1 H1 H2 H3 H4 H5]. simpl.
  destruct l1 as [| h t]. inversion H3. destruct t as [| h' t'].
  - simpl in *; lra.
  - simpl; lia.
Qed.

Lemma partition_first : forall a b (P : partition a b),
  (points a b P).[0] = a.
Proof.
  intros a b P. pose proof partition_length a b P as H0. destruct P as [l1 H1 H2 H3 H4 H5]. simpl in *.
  pose proof Rtotal_order (l1.[0]) a as [H6 | [H6 | H6]]; auto.
  - assert (List.In (l1.[0]) l1) as H7. { apply nth_In; lia. } 
    specialize (H5 (l1.[0]) H7). simpl in H5. lra.
  - pose proof In_nth l1 a 0 H3 as [n [H7 H8]]. assert (n = 0 \/ n > 0)%nat as [H9 | H9] by lia.
    -- subst. simpl in H6. lra.
    -- pose proof Sorted_Rlt_nth l1 0 n 0 H2 ltac:(lia) as H10. lra.
Qed.

Lemma partition_last : forall a b (P : partition a b),
  (points a b P).[length (points a b P) - 1] = b.
Proof.
  intros a b P. pose proof partition_length a b P as H0. destruct P as [l1 H1 H2 H3 H4 H5]. simpl in *.
  pose proof Rtotal_order (l1.[(length l1 - 1)]) b as [H6 | [H6 | H6]]; auto.
  2 : { assert (List.In (l1.[(length l1 - 1)]) l1) as H7. { apply nth_In; lia. } 
    specialize (H5 (l1.[(length l1 - 1)]) H7). simpl in H5. lra. }
  pose proof In_nth l1 b 0 H4 as [n [H7 H8]]. assert (n = length l1 - 1 \/ n < length l1 - 1)%nat as [H9 | H9] by lia.
  - subst. simpl in H6. lra.
  - pose proof Sorted_Rlt_nth l1 n (length l1 - 1) 0 H2 ltac:(lia) as H10. lra.
Qed.

Lemma partition_in : forall a b (P : partition a b) (x : ℝ) (l : list ℝ),
  P.(points a b) = l ->
  List.In x (points a b P) -> a <= x <= b.
Proof.
  intros a b P x l H1 H2. subst. destruct P. auto.
Qed.

Lemma partition_not_empty : forall a b (P : partition a b),
  let l := P.(points a b) in
  l <> [].
Proof.
  intros a b P l. apply not_empty_In_list with (x := a).
  destruct P; auto.
Qed.

Lemma exists_partition_a_b : forall a b : ℝ,
  a < b -> { P : partition a b | P.(points a b) = [a; b] }.
Proof.
  intros a b H1.
  assert (H2 : Sorted Rlt [a; b]). { apply Sorted_cons. apply Sorted_cons; constructor. constructor; lra. }
  assert (H3 : List.In a [a; b]). { simpl; left; reflexivity. }
  assert (H4 : List.In b [a; b]). { simpl; right; left; reflexivity. }
  assert (H5 : forall x, List.In x [a; b] -> a <= x <= b). { intros x H5. simpl in H5. destruct H5 as [H5 | H5]; lra. }
  exists (mkpartition a b [a; b] H1 H2 H3 H4 H5). simpl. reflexivity.
Qed.

Lemma partition_sublist_elem_has_inf :  forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition a b),
  let l1 := p.(points a b) in
  bounded_on f [a, b] ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_glb (fun y => exists x, x ∈ [l1.[i], l1.[i+1]] /\ y = f x) (l2.[i]) }. 
Proof.
  intros f a b p l1 H1. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
  induction l1 as [| h t IH].
  - exists []; split; simpl; lia.
  - destruct IH as [l2 [IH1 IH2]].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. split; simpl; lia. assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_on f [h, h']) as H7. { apply bounded_on_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_inf h h' f H4 H7 as [inf H8]. exists (inf :: l2). split. simpl. rewrite IH1. simpl. lia. intros i H9.
       assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace ((h :: h' :: t').[i]) with ((h' :: t').[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace ((h :: h' :: t').[(i + 1)]) with ((h' :: t').[i]). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace ((inf :: l2).[i]) with (l2.[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Lemma partition_sublist_elem_has_sup : forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition a b),
  let l1 := p.(points a b) in
  bounded_on f [a, b] ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_lub (fun y => exists x, x ∈ [l1.[i], l1.[i+1]] /\ y = f x) (l2.[i]) }. 
Proof.
  intros f a b p l1 H1. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
  induction l1 as [| h t IH].
  - exists []; split; simpl; lia.
  - destruct IH as [l2 [IH1 IH2]].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. split; simpl; lia. assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_on f [h, h']) as H7. { apply bounded_on_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_sup h h' f H4 H7 as [sup H8]. exists (sup :: l2). split. simpl. rewrite IH1. simpl. lia.
       intros i H9. assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace ((h :: h' :: t').[i]) with ((h' :: t').[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace ((h :: h' :: t').[(i + 1)]) with ((h' :: t').[i]). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace ((sup :: l2).[i]) with (l2.[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Lemma partition_spec : forall (a b : ℝ) (P : partition a b),
  Sorted Rlt (P.(points a b)) /\ a < b /\ List.In a (P.(points a b)) /\ List.In b (P.(points a b)) /\
    (forall x, List.In x (P.(points a b)) -> a <= x <= b) /\ (length (P.(points a b)) >= 2)%nat /\ NoDup (P.(points a b)) /\
      (P.(points a b)).[0] = a /\ (P.(points a b)).[(length (P.(points a b)) - 1)] = b.
Proof.
  intros a b [l1 H1 H2 H3 H4 H5]; simpl. repeat (split; auto).
  - destruct l1 as [| h t]. inversion H3. destruct t as [| h' t']; simpl in *; try lra; try lia.
  - apply Sorted_Rlt_NoDup; auto.
  - destruct l1 as [| h t]. inversion H3. pose proof In_nth (h :: t) a 0 H3 as [n [H6 H7]]. assert (n = 0 \/ n > 0)%nat as [H8 | H8] by lia.
    -- subst. reflexivity.
    -- pose proof Sorted_Rlt_nth (h :: t) 0 n 0 H2 ltac:(simpl in *; lia) as H9. rewrite H7 in H9. simpl in H9.
       specialize (H5 h). simpl in H5. lra.
  - pose proof In_nth l1 b 0 H4 as [n [H6 H7]]. assert (n = (length l1 - 1) \/ n < length l1 - 1)%nat as [H8 | H8] by lia.
    -- subst. reflexivity.
    -- pose proof Sorted_Rlt_nth l1 n (length l1 - 1) 0 H2 ltac:(lia) as H9. specialize (H5 (l1.[(length l1 - 1)])).
       assert (List.In (l1.[(length l1 - 1)]) l1) as H10. { apply nth_In. lia. } specialize (H5 H10). rewrite H7 in H9. lra.
Qed.

Lemma insert_Partition_R_not_first_or_last : forall (a b r : ℝ) (P Q : partition a b) (i : ℕ),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  (i < length l2)%nat -> ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> l2.[i] = r -> (i > 0 /\ i < length l2 - 1)%nat.
Proof.
  intros a b r P Q i l1 l2 H0 H1 H2 H3.
  pose proof partition_spec a b P as H4. pose proof partition_spec a b Q as H5.
  pose proof partition_first a b Q as H6. pose proof partition_last a b Q as H7.
   split.
  - destruct i; try lia. subst. destruct Q as [l]; simpl in *. replace l2 with l in * by auto. rewrite H2 in *.
    exfalso. apply H1. rewrite H6. tauto.
  - assert (i >= length l2 - 1 \/ i < length l2 - 1)%nat as [H8 | H8] by lia; auto. subst. destruct Q as [l]; simpl in *. replace l2 with l in * by auto. rewrite H2 in *.
    exfalso. apply H1. rewrite insert_Sorted_Rlt_length in *. replace (S (length l1) - 1)%nat with (length l1) in * by lia.
    assert (i = length l1 \/ i > length l1)%nat as [H9 | H9] by lia. rewrite H9 in *. rewrite H7. tauto. 
    rewrite nth_overflow. 2 : { rewrite insert_Sorted_Rlt_length in *. lia. } lia. 
Qed.

Lemma partition_eq : forall (a b : ℝ) (P Q : partition a b),
  P = Q <-> P.(points a b) = Q.(points a b).
Proof.
  intros a b P Q. split; intros H1; subst; auto.
  destruct P as [l1]; destruct Q as [l2]; simpl in *. subst; f_equal; apply proof_irrelevance.
Qed.

Lemma exists_list_of_missing_elems : forall (a b : ℝ) (P Q : partition a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  List.incl l1 l2 -> exists (l : list ℝ), add_points_Sorted_Rlt l1 l = l2 /\
    forall r, List.In r l -> ~List.In r l1.
Proof.
  intros a b P Q l1 l2 H1. exists (get_all_points l1 l2).
  split. pose proof get_all_points_spec l1 l2 as H2. apply Sorted_Rlt_eq.
  - apply add_points_Sorted_Rlt_spec. apply get_all_points_NoDup. destruct Q as [l]; simpl in *. apply Sorted_Rlt_NoDup; auto.
    intros r H3. specialize (H2 r). apply H2 in H3; tauto. destruct P as [l]; auto.
  - destruct Q as [l]; auto.
  - intros x. split.
    -- intros H3. unfold incl in H1. pose proof add_points_Sorted_Rlt_In l1 (get_all_points l1 l2) x as H4. rewrite H4 in H3.
       destruct H3 as [H3 | H3]. specialize (H2 x). rewrite H2 in H3; tauto. apply H1; auto.
    -- intros H3. apply (add_points_Sorted_Rlt_In l1 (get_all_points l1 l2) x). pose proof classic (List.In x l1) as [H4 | H4].
       right; auto. left. apply H2. auto.
  - intros r H2 H3. pose proof get_all_points_spec l1 l2 r as H4. apply H4 in H2 as [H2 H5]. apply H5; auto.
Qed.

Lemma exists_partition_includes_both : forall (a b : ℝ) (P Q : partition a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  exists (R : partition a b), List.incl l1 (R.(points a b)) /\ List.incl l2 (R.(points a b)).
Proof.
  intros a b P Q l1 l2. set (l3 := add_points_Sorted_Rlt l2 (get_all_points l2 l1)).
  assert (H1 : a < b). { pose proof partition_spec a b P; tauto. }
  assert (H2 : Sorted Rlt l3).
  {
    apply add_points_Sorted_Rlt_spec. apply get_all_points_NoDup. apply Sorted_Rlt_NoDup. destruct P as [l]; simpl in *; auto.
    intros r H3 H4. pose proof get_all_points_spec l2 l1 r as H5. apply H5 in H3 as [H3 H6]. apply H6; auto.
    destruct Q as [l]; auto.
  }
  assert (H3 : List.In a l3). { apply add_points_Sorted_Rlt_In. right. destruct Q as [l]; simpl in *; auto. }
  assert (H4 : List.In b l3). { apply add_points_Sorted_Rlt_In. right. destruct Q as [l]; simpl in *; auto. }
  assert (H5 : forall x, List.In x l3 -> a <= x <= b). 
  {
    intros x H5. destruct Q as [l]; simpl in *. unfold l3 in H5. apply add_points_Sorted_Rlt_In in H5 as [H5 | H5]; try lra.
    apply get_all_points_spec in H5 as [H5 H6]. destruct P as [l']; simpl in *. apply partition_P15. auto.
    apply partition_P10; auto.
  }
  set (R := mkpartition a b l3 H1 H2 H3 H4 H5). exists R. split.
  - simpl. intros r H7. unfold l3. apply add_points_Sorted_Rlt_In. pose proof classic (List.In r l2) as [H8 | H8].
    -- right; auto.
    -- left. apply get_all_points_spec; auto.
  - intros r H6. replace (points a b R) with l3; auto. unfold l3. apply add_points_Sorted_Rlt_In. pose proof classic (List.In r l2) as [H7 | H7].
    -- right; auto.
    -- left. apply get_all_points_spec; tauto.
Qed.

Lemma partition_telescope : forall (a b : ℝ) (P : partition a b),
  ∑ 0 (length (P.(points a b)) - 2) (fun i => (P.(points a b)).[(i+1)] - (P.(points a b)).[i]) = b - a.
Proof.
  intros a b P.
  rewrite sum_f_list_sub_alt; [| apply partition_length].
  rewrite partition_last, partition_first.
  reflexivity.
Qed.

Definition uniform_points (a b : R) (n : nat) : list R :=
  map (fun i => a + INR i * ((b - a) / INR n)) (seq 0 (n + 1)).

Lemma uniform_is_partition : forall (a b : R) (n : nat),
  a < b -> (n > 0)%nat ->
  Sorted Rlt (uniform_points a b n) /\
  List.In a (uniform_points a b n) /\
  List.In b (uniform_points a b n) /\
  (forall x, List.In x (uniform_points a b n) -> a <= x <= b).
Proof.
  intros a b n H1 H2. unfold uniform_points. split; [| split; [| split]].
  - replace (map (fun i : nat => a + INR i * ((b - a) / INR n)) (seq 0 (n + 1)))
      with (map (fun x : R => ((b - a) / INR n) * x + a) (map INR (seq 0 (n + 1)))).
    2 : { rewrite map_map. apply map_ext. intros i. lra. }
    apply Sorted_Rlt_map_mult_plus.
    + apply Rdiv_pos_pos; [lra | apply lt_0_INR; lia].
    + apply sorted_Rlt_seq.
  - apply in_map_iff. exists 0%nat. split.
    + simpl. lra.
    + apply in_seq. lia.
  - apply in_map_iff. exists n. split.
    + replace (a + INR n * ((b - a) / INR n)) with b.
      2 : { field. apply not_0_INR. lia. }
      reflexivity.
    + apply in_seq. lia.
  - intros x H3. apply in_map_iff in H3 as [i [H4 H5]]. apply in_seq in H5. subst x.
    assert (H6 : 0 <= INR i) by apply pos_INR.
    assert (H7 : INR i <= INR n) by (apply le_INR; lia).
    assert (H8 : 0 < INR n) by (apply lt_0_INR; lia).
    assert (H9 : 0 <= (b - a) / INR n) by (apply Rlt_le; apply Rdiv_pos_pos; lra).
    split.
    + assert (H10 : 0 <= INR i * ((b - a) / INR n)) by (apply Rmult_le_pos; lra). lra.
    + assert (H10 : INR i * ((b - a) / INR n) <= INR n * ((b - a) / INR n)) by (apply Rmult_le_compat_r; lra).
      replace (INR n * ((b - a) / INR n)) with (b - a) in H10.
      2 : { field. apply not_0_INR. lia. }
      lra.
Qed.

Definition uniform_partition (a b : R) (n : nat) (H1 : a < b) (H2 : (n > 0)%nat) : partition a b.
Proof.
  pose proof (uniform_is_partition a b n H1 H2) as [H3 [H4 [H5 H6]]].
  exact (mkpartition a b (uniform_points a b n) H1 H3 H4 H5 H6).
Defined.

Lemma uniform_partition_nth : forall a b n H1 H2 i,
  (i < length (points a b (uniform_partition a b n H1 H2)))%nat ->
  (points a b (uniform_partition a b n H1 H2)).[i] = a + INR i * ((b - a) / INR n).
Proof.
  intros a b n H1 H2 i H3.
  unfold uniform_partition in *.
  destruct (uniform_is_partition a b n H1 H2) as [H4 [H5 [H6 H7]]].
  simpl in *.
  unfold uniform_points in *.
  rewrite nth_indep with (d' := a + INR 0 * ((b - a) / INR n)).
  2: { rewrite length_map, length_seq in *. exact H3. }
  
  change (a + INR 0 * ((b - a) / INR n)) with ((fun i0 : nat => a + INR i0 * ((b - a) / INR n)) 0%nat).
  rewrite map_nth.
  f_equal.
  rewrite seq_nth.
  - simpl. reflexivity.
  - rewrite length_map, length_seq in H3. exact H3.
Qed.

Lemma uniform_partition_width : forall a b n H1 H2 i,
  (i < length (points a b (uniform_partition a b n H1 H2)) - 1)%nat ->
  (points a b (uniform_partition a b n H1 H2)).[(i+1)] - 
  (points a b (uniform_partition a b n H1 H2)).[i] = (b - a) / INR n.
Proof.
  intros a b n H1 H2 i H3.
  assert (H4 : (i < length (points a b (uniform_partition a b n H1 H2)))%nat) by lia.
  assert (H5 : (i + 1 < length (points a b (uniform_partition a b n H1 H2)))%nat) by lia.
  
  rewrite uniform_partition_nth; [| exact H5].
  rewrite uniform_partition_nth; [| exact H4].
  
  replace (INR (i + 1)) with (INR i + 1) by (rewrite plus_INR; reflexivity).
  lra.
Qed.

Definition mesh_lt (a b : R) (P : partition a b) (δ : R) : Prop :=
  forall i, (i < length (P.(points a b)) - 1)%nat ->
    (P.(points a b)).[(i+1)] - (P.(points a b)).[i] < δ.

Definition mesh_le (a b : R) (P : partition a b) (δ : R) : Prop :=
  forall i, (i < length (P.(points a b)) - 1)%nat ->
    (P.(points a b)).[(i+1)] - (P.(points a b)).[i] <= δ.

Lemma uniform_partition_mesh_eq : forall a b n H1 H2,
  forall i, (i < length (points a b (uniform_partition a b n H1 H2)) - 1)%nat ->
  (points a b (uniform_partition a b n H1 H2)).[(i+1)] - 
  (points a b (uniform_partition a b n H1 H2)).[i] = (b - a) / INR n.
Proof.
  intros a b n H1 H2 i H3.
  apply uniform_partition_width; exact H3.
Qed.

Lemma uniform_partition_mesh_lt : forall a b n H1 H2 δ,
  (b - a) / INR n < δ ->
  mesh_lt a b (uniform_partition a b n H1 H2) δ.
Proof.
  intros a b n H1 H2 δ H3 i H4.
  rewrite uniform_partition_mesh_eq; auto.
Qed.

Definition geometric_points (a b : R) (n : nat) : list R :=
  map (fun i => a * Rpower (b / a) (INR i / INR n)) (seq 0 (n + 1)).

Lemma geometric_is_partition : forall (a b : R) (n : nat),
  0 < a -> a < b -> (n > 0)%nat ->
  Sorted Rlt (geometric_points a b n) /\
  List.In a (geometric_points a b n) /\
  List.In b (geometric_points a b n) /\
  (forall x, List.In x (geometric_points a b n) -> a <= x <= b).
Proof.
  intros a b n H1 H2 H3.
  unfold geometric_points.
  set (f := fun i => a * Rpower (b / a) (INR i / INR n)).
  
  assert (H4 : 1 < b / a).
  { apply Rmult_lt_reg_r with (r := a); [lra |].
    replace (1 * a) with a by lra.
    replace (b / a * a) with b by (field; lra).
    lra. }
  assert (H5 : 0 < b / a) by lra.
  
  assert (H6 : forall i, f i < f (S i)).
  {
    intros i. unfold f.
    apply Rmult_lt_compat_l; [lra |].
    apply Rpower_lt; [exact H4 |].
    apply Rmult_lt_compat_r.
    - apply Rinv_pos, lt_0_INR; lia.
    - rewrite S_INR; lra.
  }
  
  assert (H7 : forall k s, Sorted Rlt (map f (seq s k))).
  {
    induction k as [| k IH]; intros s.
    - simpl. constructor.
    - simpl. apply Sorted_cons.
      + apply IH.
      + destruct k as [| k'].
        * constructor.
        * simpl. apply HdRel_cons. apply H6.
  }
  
  assert (H8 : f 0%nat = a).
  {
    unfold f. simpl INR.
    replace (0 / INR n) with 0 by (unfold Rdiv; rewrite Rmult_0_l; reflexivity).
    rewrite Rpower_O; [lra | exact H5].
  }
  
  assert (H9 : f n = b).
  {
    unfold f.
    replace (INR n / INR n) with 1.
    2: { destruct n. lia. field. apply lt_INR in H3. rewrite S_INR in *. simpl in H3. lra. }
    rewrite Rpower_1; [| exact H5].
    field. lra.
  }
  
  split; [| split; [| split]].
  - apply H7.
  - apply in_map_iff. exists 0%nat. split; [exact H8 | apply in_seq; lia].
  - apply in_map_iff. exists n. split; [exact H9 | apply in_seq; lia].
  - apply sorted_first_last_in.
    + exact H2.
    + apply H7.
    + rewrite nth_indep with (d' := f 0%nat).
      2: { rewrite length_map, length_seq. lia. }
      rewrite map_nth.
      rewrite seq_nth; [| lia].
      simpl. exact H8.
    + rewrite length_map, length_seq.
      replace (n + 1 - 1)%nat with n by lia.
      rewrite nth_indep with (d' := f 0%nat).
      2: { rewrite length_map, length_seq. lia. }
      rewrite map_nth.
      rewrite seq_nth; [| lia].
      replace (0 + n)%nat with n by lia.
      exact H9.
Qed.

Definition geometric_partition (a b : R) (n : nat) (H1 : 0 < a) (H2 : a < b) (H3 : (n > 0)%nat) : partition a b.
Proof.
  pose proof (geometric_is_partition a b n H1 H2 H3) as [H4 [H5 [H6 H7]]].
  exact (mkpartition a b (geometric_points a b n) H2 H4 H5 H6 H7).
Defined.

Lemma geometric_partition_nth : forall a b n H1 H2 H3 i,
  (i < length (points a b (geometric_partition a b n H1 H2 H3)))%nat ->
  (points a b (geometric_partition a b n H1 H2 H3)).[i] = a * Rpower (b / a) (INR i / INR n).
Proof.
  intros a b n H1 H2 H3 i H4.
  unfold geometric_partition in *.
  destruct (geometric_is_partition a b n H1 H2 H3) as [H5 [H6 [H7 H8]]].
  simpl in *.
  unfold geometric_points in *.
  rewrite nth_indep with (d' := a * Rpower (b / a) (INR 0 / INR n)).
  2: { rewrite length_map, length_seq in *. exact H4. }
  change (a * Rpower (b / a) (INR 0 / INR n)) 
    with ((fun i0 : nat => a * Rpower (b / a) (INR i0 / INR n)) 0%nat).
  rewrite map_nth.
  f_equal.
  rewrite seq_nth.
  - simpl. reflexivity.
  - rewrite length_map, length_seq in H4. exact H4.
Qed.

Lemma geometric_partition_ratio : forall a b n H1 H2 H3 i,
  (i < length (points a b (geometric_partition a b n H1 H2 H3)) - 1)%nat ->
  (points a b (geometric_partition a b n H1 H2 H3)).[(i+1)] / 
  (points a b (geometric_partition a b n H1 H2 H3)).[i] = Rpower (b / a) (1 / INR n).
Proof.
  intros a b n H1 H2 H3 i H4.
  assert (H5 : (i < length (points a b (geometric_partition a b n H1 H2 H3)))%nat) by lia.
  assert (H6 : (i + 1 < length (points a b (geometric_partition a b n H1 H2 H3)))%nat) by lia.
  rewrite geometric_partition_nth; [| exact H6].
  rewrite geometric_partition_nth; [| exact H5].
  assert (H7 : 0 < b / a).
  { apply Rdiv_pos_pos; lra. }
  assert (H8 : a <> 0) by lra.
  unfold Rpower.
  assert (H9 : exp (INR i / INR n * ln (b / a)) <> 0).
  { apply Rgt_not_eq. apply exp_pos. }
  replace ((a * exp (INR (i + 1) / INR n * ln (b / a))) / (a * exp (INR i / INR n * ln (b / a))))
    with (exp (INR (i + 1) / INR n * ln (b / a)) / exp (INR i / INR n * ln (b / a))).
  2: { field. split; assumption. }
  unfold Rdiv at 1.
  rewrite <- exp_Ropp.
  rewrite <- exp_plus.
  f_equal.
  replace (INR (i + 1)) with (INR i + 1).
  2: { rewrite plus_INR. simpl. lra. }
  field.
  apply not_0_INR; lia.
Qed.

Lemma exists_partition_delta_lt : forall a b ε,
  a < b -> ε > 0 -> exists (P : partition a b), forall i, (i < length (P.(points a b)) - 1)%nat -> 
    ((P.(points a b)).[(i + 1)] - (P.(points a b)).[i]) < ε.
Proof.
  intros a b ε H1 H2.
  pose proof exists_nat_gt_inv_scale a b ε H1 H2 as [n [H3 H4]].
  exists (uniform_partition a b n H1 H3).
  intros i H5.
  rewrite uniform_partition_width; auto.
Qed.

Lemma split_partition_in : forall (a b c : R) (P : partition a b),
  a < c < b ->
  List.In c (points a b P) ->
  exists (Q : (partition a c)) (R : (partition c b)), 
  let l1 := points a b P in
  let l2 := points a c Q in
  let l3 := points c b R in
  (firstn (length l2 - 1) l2) ++ [c] ++ (skipn 1 l3) = l1.
Proof.
  intros a b c P H1 H2.
  set (l := points a b P).
  pose proof in_split' l c H2 as [l' [l'' H3]]. set (l1 := l' ++ [c]). set (l2 := [c] ++ l'').
  destruct H1 as [H0 H1].
  assert (Sorted Rlt l1 /\ Sorted Rlt l2) as [H4 H5].
  {
    assert (H4 : Sorted Rlt ((l' ++ [c]) ++ l'')). { rewrite <- app_assoc, <- H3. destruct P; auto. } split.
    - unfold l1; pose proof (Sorted_Rlt_app (l' ++ [c]) l'' H4) as [H5 H6]; auto.
    - rewrite <- app_assoc in H4. unfold l2; pose proof (Sorted_Rlt_app l' ([c] ++ l'') H4) as [H5 H6]; auto.
  }
  assert (List.In a l1) as H6.
  {
    assert (H6 : List.In a l). { destruct P; auto. }
    assert (H7 : l' <> []). { intros H7. subst. simpl in H3. pose proof partition_first a b P as H7.
      replace (points a b P) with (c :: l'') in * by auto. simpl in H7. lra. }
    unfold l1. apply in_or_app. left. 
    apply list_in_first_app with (l2 := [c] ++ l''); auto. rewrite <- H3.
    apply partition_first.
  }
  assert (List.In c l1) as H7. { apply in_or_app. right. left; auto. }
  assert (forall x, List.In x l1 -> a <= x <= c) as H8.
  {
    intros x H8. apply sorted_first_last_in with (l := l1); auto.
    - pose proof partition_first a b P as H9. replace (points a b P) with l in H9 by auto. 
      rewrite H3 in H9. unfold l1. destruct l'. simpl in H9. lra. rewrite app_nth1 in H9. simpl in *; auto.
      simpl. lia.
    - subst. unfold l1. rewrite length_app. simpl. replace (length l' + 1 - 1)%nat with (length l') by lia.
      rewrite app_nth2; try lia. rewrite Nat.sub_diag. simpl. reflexivity.
  }
  assert (List.In c l2) as H9. { left; auto. }
  assert (List.In b l2) as H10.
  {
    apply list_in_last_app with (l1 := l').
    - replace (l' ++ l2) with l. replace (length l' + length l2 - 1)%nat with (length l - 1)%nat.
      2 : { rewrite H3. unfold l2. repeat rewrite length_app. reflexivity. }
      apply partition_last.
    - intros H10. inversion H10.
  }
  assert (forall x, List.In x l2 -> c <= x <= b) as H11.
  {
    intros x H11. apply sorted_first_last_in with (l := l2); auto.
    pose proof partition_last a b P as H12. replace (points a b P) with l in H12 by auto.
    rewrite H3 in H12. unfold l2. destruct l''. simpl in H12. rewrite length_app in H12. simpl in H12.
    replace (length l' + 1 - 1)%nat with (length l') in H12 by lia. rewrite app_nth2 in H12; try lia.
    rewrite Nat.sub_diag in H12. simpl in H12. lra.
    replace (length (l' ++ [c] ++ r :: l'') - 1)%nat with (length l' + 1 + length l'')%nat in H12. 
      2 : { rewrite length_app. simpl. lia. }
      rewrite app_nth2 in H12; try lia. replace (length l' + 1 + length l'' - length l')%nat with (1 + length l'')%nat in H12 by lia.
      replace (length ([c] ++ r :: l'') - 1)%nat with (1 + length l'')%nat. 
      2 : { rewrite length_app. simpl. lia. } auto.
  }
  set (Q := mkpartition a c l1 H0 H4 H6 H7 H8).
  set (R := mkpartition c b l2 H1 H5 H9 H10 H11).
  exists Q, R. unfold l1, l2 in *. rewrite H3.
  replace (points a c Q) with (l' ++ [c]). 2 : { unfold Q; auto. }
  replace (points c b R) with ([c] ++ l''). 2 : { unfold R; auto. }
  replace (length (l' ++ [c]) - 1)%nat with (length l'). 2 : { rewrite length_app. simpl. lia. }
  rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r.
  reflexivity.
Qed.

Lemma split_partition_insert : forall (a b c : R) (P : partition a b),
  a < c < b ->
  ~ List.In c (points a b P) ->
  exists (Q : (partition a c)) (R : (partition c b)),
  let l1 := insert_Sorted_Rlt c (points a b P) in
  let l2 := points a c Q in
  let l3 := points c b R in
  (firstn (length l2 - 1) l2) ++ [c] ++ (skipn 1 l3) = l1.
Proof.
  intros a b c P H1 H2.
  set (l := points a b P).
  set (l0 := insert_Sorted_Rlt c l).
  assert (H3 : List.In c l0). { apply insert_Sorted_Rlt_in. }
  pose proof in_split' l0 c H3 as [l' [l'' H4]].
  set (l1 := l' ++ [c]).
  set (l2 := [c] ++ l'').
  destruct H1 as [H5 H6].
  assert (Sorted Rlt l1 /\ Sorted Rlt l2) as [H7 H8].
  {
    assert (H7 : Sorted Rlt ((l' ++ [c]) ++ l'')). { rewrite <- app_assoc, <- H4. apply insert_Sorted_Rlt_sorted; destruct P; auto. } split.
    - unfold l1; pose proof (Sorted_Rlt_app (l' ++ [c]) l'' H7) as [H8 H9]; auto.
    - rewrite <- app_assoc in H7. unfold l2; pose proof (Sorted_Rlt_app l' ([c] ++ l'') H7) as [H8 H9]; auto.
  }
  assert (List.In a l1) as H9.
  {
    assert (H9 : List.In a l). { destruct P; auto. }
    assert (H10 : l' <> []).
    {
      intros H10. subst. simpl in H4.
      assert (H10 : l <> []). { apply not_empty_In_list with (x := a); auto. }
      assert (H11 : c > l.[0]).
      { pose proof partition_first a b P as H11. replace (points a b P) with l in * by auto. lra. }
      pose proof insert_Sorted_Rlt_first' c l ltac:(destruct P; auto) H2 H10 H11 as H12.
      replace (insert_Sorted_Rlt c l) with (c :: l'') in * by (rewrite <- H4; auto). simpl in H12. lra.
    }
    unfold l1. apply in_or_app. left.
    apply list_in_first_app with (l2 := [c] ++ l''); auto. rewrite <- H4.
    rewrite <- partition_first with (a := a) (b := b) (P := P); auto. apply insert_Sorted_Rlt_first'; auto.
    - destruct P; auto.
    - apply not_empty_In_list with (x := a); auto.
    - pose proof partition_first a b P as H11. lra.
  }
  assert (List.In c l1) as H10. { apply in_or_app. right. left; auto. }
  assert (forall x, List.In x l1 -> a <= x <= c) as H11.
  {
    intros x H11. apply sorted_first_last_in with (l := l1); auto.
    - pose proof insert_Sorted_Rlt_first' c l ltac:(destruct P; auto) ltac:(auto)
      ltac:(apply not_empty_In_list with (x := a); destruct P; auto) ltac:(unfold l; rewrite partition_first; lra) as H12.
      rewrite <- partition_first with (a := a) (b := b) (P := P); auto. unfold l1. fold l.
      destruct l'. simpl. simpl in H9; lra. simpl. rewrite <- H12. fold l0. rewrite H4. simpl. reflexivity.
    - unfold l1. rewrite app_nth2. 2 : { rewrite length_app. simpl. lia. }
      replace (length (l' ++ [c]) - 1 - length l')%nat with 0%nat.
      reflexivity.
      rewrite length_app. simpl. lia.
  }
  assert (List.In c l2) as H12. { left. reflexivity. }
  assert (List.In b l2) as H13.
  {
    unfold l2. apply in_or_app. right. apply list_in_last_app with (l1 := l' ++ [c]).
    rewrite <- app_assoc. rewrite <- H4. replace (length (l' ++ [c]) + length l'' - 1)%nat with (length l0 - 1)%nat.
    2 : { rewrite H4. repeat rewrite length_app. simpl. lia. }
    unfold l0. rewrite <- (partition_last a b P). rewrite insert_Sorted_Rlt_length. replace (S(length l) - 1)%nat with (length l) by lia.
    apply insert_Sorted_Rlt_last; auto. destruct P; auto. apply not_empty_In_list with (x := a); destruct P; auto.
    rewrite partition_last; lra. intros H13. subst. simpl in H4.
    pose proof insert_Sorted_Rlt_last c l ltac:(destruct P; auto) ltac:(auto) ltac:(apply not_empty_In_list with (x := a); destruct P; auto)
    ltac:(unfold l; rewrite (partition_last a b P); auto) as H13. fold l0 in H13. rewrite H4 in H13.
    replace (length l) with (length l')%nat in H13 at 1.
    2 : { pose proof insert_Sorted_Rlt_length c l as H14. fold l0 in H14. rewrite H4 in H14. rewrite length_app in H14. simpl in H14. lia. }
    rewrite app_nth2 in H13; auto. rewrite Nat.sub_diag in H13. simpl in H13. unfold l in H13. rewrite (partition_last a b P) in H13. lra.
  }
  assert (forall x, List.In x l2 -> c <= x <= b) as H14.
  {
    intros x H14. apply sorted_first_last_in with (l := l2); auto.
    pose proof insert_Sorted_Rlt_last c l ltac:(destruct P; auto) ltac:(auto)
    ltac:(apply not_empty_In_list with (x := a); destruct P; auto) ltac:(unfold l; rewrite partition_last; lra) as H15.
    rewrite <- (partition_last a b P). fold l. unfold l2.
    fold l0 in H15. rewrite H4 in H15. rewrite <- H15. destruct l''.
    simpl in H13. lra.
    rewrite app_nth2. 2 : { simpl. lia. } replace (length ([c] ++ r :: l'') - 1 - length [c])%nat with (length l'').
    2 : { simpl. lia. } 
    replace (length l) with (length (l' ++ [c]) + length (r :: l'') - 1)%nat.
    2 : { rewrite length_app. simpl. pose proof insert_Sorted_Rlt_length c l as H16. fold l0 in H16. rewrite H4 in H16.
          repeat rewrite length_app in H16. simpl in H16. lia. } 
    rewrite app_nth2. rewrite app_nth2. 2 : { rewrite length_app. simpl. lia. }
    2 : { rewrite length_app. simpl. lia. } 
    replace (length (l' ++ [c]) + length (r :: l'') - 1 - length l' - length [c])%nat with (length l'').
    2 : { rewrite length_app. simpl. lia. } reflexivity.
  }
  set (Q := mkpartition a c l1 H5 H7 H9 H10 H11).
  set (R := mkpartition c b l2 H6 H8 H12 H13 H14).
  exists Q, R.
  unfold l1, l2 in *.
  replace (points a c Q) with (l' ++ [c]). 2 : { unfold Q; auto. }
  replace (points c b R) with ([c] ++ l''). 2 : { unfold R; auto. }
  replace (length (l' ++ [c]) - 1)%nat with (length l'). 2 : { rewrite length_app. simpl. lia. }
  rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r.
  rewrite H4. reflexivity.
Qed.

Lemma exists_partition_insert : forall a b c (P : partition a b),
  a < c < b ->
  ~ List.In c (points a b P) ->
  exists (Q : partition a b), 
  Q.(points a b) = insert_Sorted_Rlt c P.(points a b).
Proof.
  intros a b c P H1 H2.
  set (l := insert_Sorted_Rlt c (points a b P)).
  assert (H3 : Sorted Rlt l). { apply insert_Sorted_Rlt_sorted; destruct P; auto. }
  assert (H4 : List.In a l). { apply In_l_In_insert_Sorted_Rlt. destruct P; auto. }
  assert (H5 : List.In b l). { apply In_l_In_insert_Sorted_Rlt. destruct P; auto. }
  assert (H6 : forall x, List.In x l -> a <= x <= b).
  {
    intros x H6. apply sorted_first_last_in with (l := l); auto; try lra.
    - unfold l. rewrite insert_Sorted_Rlt_first'; auto.
      apply partition_first. destruct P; auto. apply partition_not_empty; auto.
      rewrite partition_first; lra.
    - replace (length l - 1)%nat with (length P.(points a b)). 2 : { unfold l. rewrite insert_Sorted_Rlt_length; lia. }
      unfold l. rewrite insert_Sorted_Rlt_last; auto.
      apply partition_last. destruct P; auto. apply partition_not_empty; auto.
      rewrite partition_last; lra.
  }
  assert (H7 : a < b) by lra.
  set (Q := mkpartition a b l H7 H3 H4 H5 H6).
  exists Q. auto.
Qed.

Lemma join_partition : forall (a b c : R) (P1 : partition a c) (P2 : partition c b),
  a < c < b ->
  exists (P : partition a b),
  let l1 := points a c P1 in
  let l2 := points c b P2 in
  let l' := firstn (length l1 - 1) l1 in
  let l'' := skipn 1 l2 in
  points a b P = l' ++ [c] ++ l'' /\ 
  points a c P1 = l' ++ [c] /\
  points c b P2 = [c] ++ l''.
Proof.
  intros a b c P1 P2 H1.
  set (l1 := points a c P1). set (l2 := points c b P2).
  set (l' := firstn (length l1 - 1) l1).
  set (l'' := skipn 1 l2).
  set (l := l' ++ [c] ++ l'').
  assert (H2 : a < b) by lra.
  assert (H3 : l1 = l' ++ [c]).
  { pose proof last_concat l1 c (partition_last a c P1) (partition_not_empty a c P1) as [l3 H3].
    unfold l'. rewrite H3. replace (length (l3 ++ [c]) - 1)%nat with (length l3) by (rewrite length_app; simpl; lia).
    rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. auto. }
  assert (H4 : l2 = [c] ++ l'').
  { pose proof first_concat l2 c (partition_first c b P2) (partition_not_empty c b P2) as [l3 H4].
    unfold l''. rewrite H4. simpl. reflexivity. }
  assert (H5 : Sorted Rlt l).
  { unfold l. apply Sorted_Rlt_glue.
    - rewrite <- H3. destruct P1; auto.
    - rewrite <- H4. destruct P2; auto. }
  assert (H6 : List.In a l).
  { unfold l. rewrite app_assoc. rewrite <- H3. apply in_or_app. left. destruct P1; auto. }
  assert (H7 : List.In b l).
  { unfold l. rewrite <- H4. apply in_or_app. right. destruct P2; auto. }
  assert (H8 : forall x, List.In x l -> a <= x <= b).
  { intros x H8. unfold l in H8. apply in_app_or in H8 as [H8 | H8].
    - assert (List.In x l1). { rewrite H3. apply in_or_app. auto. }
      specialize (partition_P5 a c P1 x H). lra.
    - apply in_app_or in H8 as [H8 | H8].
      + simpl in H8. destruct H8; try contradiction. subst. lra.
      + assert (List.In x l2). { rewrite H4. apply in_or_app. right. auto. }
        specialize (partition_P5 c b P2 x H). lra. }
  exists (mkpartition a b l H2 H5 H6 H7 H8). auto.
Qed.

Lemma bounded_on_add : forall f g a b,
  bounded_on f [a, b] -> bounded_on g [a, b] -> bounded_on (fun x => f x + g x) [a, b].
Proof.
  intros f g a b [[m1 H1] [M1 H2]] [[m2 H3] [M2 H4]]. split.
  - exists (m1 + m2). intros y [x [H5 H6]]. subst y.
    assert (H7 : m1 <= f x). { apply Rge_le, H1. exists x. split; auto. }
    assert (H8 : m2 <= g x). { apply Rge_le, H3. exists x. split; auto. }
    nra.
  - exists (M1 + M2). intros y [x [H5 H6]]. subst y.
    assert (H7 : f x <= M1). { apply H2. exists x. split; auto. }
    assert (H8 : g x <= M2). { apply H4. exists x. split; auto. }
    nra.
Qed.

Lemma partition_insert_spec : forall (a b r : ℝ) (P Q : partition a b),
  ~ In r (points a b P) ->
  points a b Q = insert_Sorted_Rlt r (points a b P) ->
  exists k : ℕ,
    (k < length (points a b P) - 1)%nat /\
    nth k (points a b P) 0 < r /\
    r < nth (k + 1) (points a b P) 0 /\
    (forall i : ℕ, (i <= k)%nat -> nth i (points a b Q) 0 = nth i (points a b P) 0) /\
    nth (k + 1) (points a b Q) 0 = r /\
    (forall i : ℕ, (i > k)%nat -> nth (i + 1) (points a b Q) 0 = nth i (points a b P) 0).
Proof.
  intros a b r P Q H1 H2.
  assert (H3 : Sorted Rlt (points a b P)) by apply partition_P2.
  pose proof (insert_Sorted_Rlt_nth (points a b P) (points a b Q) r H3 H1 H2) as [i [H4 [H5 [H6 H7]]]].
  assert (H8 : (i > 0 /\ i < length (points a b Q) - 1)%nat).
  { eapply insert_Partition_R_not_first_or_last with (a := a) (b := b) (P := P) (Q := Q); eauto. }
  destruct i as [| k].
  { lia. }
  exists k.
  assert (H9 : length (points a b Q) = S (length (points a b P))).
  { rewrite H2. apply insert_Sorted_Rlt_length. }
  assert (H10 : Sorted Rlt (points a b Q)).
  { rewrite H2. apply insert_Sorted_Rlt_sorted; auto. }
  split.
  { lia. }
  split.
  { rewrite <- H5.
    rewrite <- (H6 k) by lia.
    apply Sorted_Rlt_nth with (d := 0); auto. }
  split.
  { rewrite <- H5.
    replace (k + 1)%nat with (S k) by lia.
    rewrite <- (H7 (S k)) by lia.
    replace (S k + 1)%nat with (S (S k)) by lia.
    apply Sorted_Rlt_nth with (d := 0); auto. lia. }
  split.
  { intros j H11. apply H6. lia. }
  split.
  { replace (k + 1)%nat with (S k) by lia. exact H5. }
  { intros j H11. apply H7. lia. }
Qed.

Lemma partition_inf_eq : forall (a b : ℝ) (bf : bounded_function_R a b) (P Q : partition a b) (i j : ℕ),
  let f := bounded_f a b bf in
  let infP := proj1_sig (partition_sublist_elem_has_inf f a b P (bounded_function_R_P2 a b bf)) in
  let infQ := proj1_sig (partition_sublist_elem_has_inf f a b Q (bounded_function_R_P2 a b bf)) in
  let l1 := points a b P in
  let l2 := points a b Q in
  (i < length l1 - 1)%nat ->
  (j < length l2 - 1)%nat ->
  nth i l1 0 = nth j l2 0 ->
  nth (i + 1) l1 0 = nth (j + 1) l2 0 ->
  nth i infP 0 = nth j infQ 0.
Proof.
  intros a b bf P Q i j f infP infQ l1 l2 H1 H2 H3 H4.
  unfold infP, infQ, l1, l2.
  pose proof (proj2_sig (partition_sublist_elem_has_inf f a b P (bounded_function_R_P2 a b bf))) as [H5 H6].
  pose proof (proj2_sig (partition_sublist_elem_has_inf f a b Q (bounded_function_R_P2 a b bf))) as [H7 H8].
  assert (H9 : (i < length (` (partition_sublist_elem_has_inf f a b P (bounded_function_R_P2 a b bf))))%nat).
  { rewrite H5. exact H1. }
  assert (H10 : (j < length (` (partition_sublist_elem_has_inf f a b Q (bounded_function_R_P2 a b bf))))%nat).
  { rewrite H7. exact H2. }
  specialize (H6 i H9).
  specialize (H8 j H10).
  unfold l1, l2 in H3, H4.
  rewrite H3, H4 in H6.
  destruct H6 as [H11 H12].
  destruct H8 as [H13 H14].
  apply Rle_antisym.
  - apply Rge_le, H14. exact H11.
  - apply Rge_le, H12. exact H13.
Qed.

Lemma partition_sup_eq : forall (a b : ℝ) (bf : bounded_function_R a b) (P Q : partition a b) (i j : ℕ),
  let f := bounded_f a b bf in
  let supP := proj1_sig (partition_sublist_elem_has_sup f a b P (bounded_function_R_P2 a b bf)) in
  let supQ := proj1_sig (partition_sublist_elem_has_sup f a b Q (bounded_function_R_P2 a b bf)) in
  let l1 := points a b P in
  let l2 := points a b Q in
  (i < length l1 - 1)%nat ->
  (j < length l2 - 1)%nat ->
  nth i l1 0 = nth j l2 0 ->
  nth (i + 1) l1 0 = nth (j + 1) l2 0 ->
  nth i supP 0 = nth j supQ 0.
Proof.
  intros a b bf P Q i j f supP supQ l1 l2 H1 H2 H3 H4.
  unfold supP, supQ, l1, l2.
  pose proof (proj2_sig (partition_sublist_elem_has_sup f a b P (bounded_function_R_P2 a b bf))) as [H5 H6].
  pose proof (proj2_sig (partition_sublist_elem_has_sup f a b Q (bounded_function_R_P2 a b bf))) as [H7 H8].
  assert (H9 : (i < length (` (partition_sublist_elem_has_sup f a b P (bounded_function_R_P2 a b bf))))%nat).
  { rewrite H5. exact H1. }
  assert (H10 : (j < length (` (partition_sublist_elem_has_sup f a b Q (bounded_function_R_P2 a b bf))))%nat).
  { rewrite H7. exact H2. }
  specialize (H6 i H9).
  specialize (H8 j H10).
  unfold l1, l2 in H3, H4.
  rewrite H3, H4 in H6.
  destruct H6 as [H11 H12].
  destruct H8 as [H13 H14].
  apply Rle_antisym.
  - apply H12. exact H13.
  - apply H14. exact H11.
Qed.
