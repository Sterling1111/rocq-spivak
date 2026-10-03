From Lib Require Import Imports Notations Sets.
Import SetNotations.

Close Scope R_scope.
Open Scope nat_scope.

Definition induction_nat := ∀ P : ℕ → Prop, (P 0 ∧ ∀ k, P k → P (S k)) → ∀ n, P n.

Definition strong_induction_nat := ∀ P : ℕ → Prop, (∀ m, (∀ k, k < m → P k) → P m) → ∀ n, P n.

Definition well_ordering_nat := ∀ E, E ≠ ∅ → (∃ n, n ∈ E ∧ ∀ m, m ∈ E → (n ≤ m)).

Definition well_ordering_principle_contrapositive_nat := ∀ E : nat -> Prop,
  (~(∃ m, E m /\ ∀ k, E k -> m <= k)) -> (~(∃ n, E n)).

Lemma induction_imp_induction_nat : induction_nat.
Proof.
  unfold induction_nat. intros P [H1 H2] n. induction n as [| k IH].
  - apply H1.
  - apply H2. apply IH.
Qed.

Lemma lemma_2_10 : well_ordering_nat -> induction_nat.
Proof.
  unfold well_ordering_nat, induction_nat. intros well_ordering_nat P [Hbase H_inductive] n.
  set (E := fun m => ~ P m).
  specialize (well_ordering_nat E). assert (H1 : forall n : nat, E n -> False).
  - intros x H1. assert (H3 : E ≠ ∅) by (apply not_Empty_In; exists x; auto). apply well_ordering_nat in H3.
    destruct H3 as [least_elem_E H3]. destruct H3 as [H3 H4]. specialize (H_inductive (least_elem_E - 1)).
    destruct least_elem_E as [| least_elem_E'].
    -- apply H3. apply Hbase.
    -- specialize (H4 least_elem_E'). assert (H5 : S least_elem_E' <= least_elem_E' -> False) by lia.
       assert (H6 : ~(E least_elem_E')) by tauto. unfold E in H6. simpl in *. rewrite Nat.sub_0_r in *.
       apply NNPP in H6. apply H_inductive in H6. apply H3. apply H6.
  - specialize (H1 n). unfold E in H1. apply NNPP in H1. apply H1.
Qed.

Lemma lemma_2_11 : induction_nat -> strong_induction_nat.
Proof.
  unfold induction_nat, strong_induction_nat. intros induction_nat P H1 n.
  assert (H2 : forall k, k <= n -> P k).
  {
    set (P2 := fun n => ∀ k, k ≤ n → P k). specialize (induction_nat P2). assert (H3 : P2 0).
    { unfold P2. intros k H2. apply H1. intros k' H3. inversion H2. subst. inversion H3. }
    assert (H4 : (∀ k : ℕ, P2 k → P2 (S k))).
    { unfold P2. intros k H4 k' H5. apply H1. intros k'' H6. apply H4. lia. }
    apply induction_nat; auto.
  }
  apply H2; auto.
Qed.

Lemma strong_induction_nat_imp_well_ordering_contrapositive_nat : strong_induction_nat -> well_ordering_principle_contrapositive_nat.
Proof.
  intros H1 E H2. set (E' := fun n => ~ E n). assert (~ E 0) as H3.
  { intros H3. apply H2. exists 0. split; auto; lia. }
  assert (H4 : forall n, E' n).
  {
    intros n. apply H1. intros m H4. destruct m.
    - unfold E'. intros H5. apply H3. apply H5.
    - assert (E (S m) -> False) as H5.
      { 
        intros H5. apply H2. exists (S m). split; auto. intros k H6.
        specialize (H4 k). assert (E' k -> False) as H7; auto. assert (k < S m -> False) as H8 by auto. lia.
      }
      auto.
  }
  intros [n H5]. apply (H4 n). auto.
Qed.

Lemma strong_induction_nat_imp_well_ordering_nat : strong_induction_nat -> well_ordering_nat.
Proof.
  intros H1. specialize (strong_induction_nat_imp_well_ordering_contrapositive_nat H1) as H2.
  clear H1. rename H2 into H1. intros E H2. 
  assert (H3 : ~(exists m, E m /\ forall k, E k -> m <= k) -> ~(exists n, E n)) by apply H1.
  destruct (classic (exists m, E m /\ forall k, E k -> m <= k)) as [H4 | H4]; auto.
  exfalso. apply H3 in H4. apply H4. apply not_Empty_In; auto.
Qed.

Lemma WI_SO_WO_equiv : (well_ordering_nat <-> strong_induction_nat) /\ (strong_induction_nat <-> induction_nat) /\ (induction_nat <-> well_ordering_nat).
Proof.
  pose proof lemma_2_10 as H1. pose proof lemma_2_11 as H2. pose proof (strong_induction_nat_imp_well_ordering_nat) as H3. tauto.
Qed.

Lemma WI_SI_WO :  induction_nat /\ strong_induction_nat /\ well_ordering_nat.
Proof.
  pose proof WI_SO_WO_equiv as H1. pose proof (induction_imp_induction_nat) as H2. tauto.
Qed. 

Lemma strong_induction_N : strong_induction_nat.
Proof.
  apply lemma_2_11. apply induction_imp_induction_nat.
Qed.

(** Generalize the context so that recursive calls can change parameters and
    dependent hypotheses. Keep the induction variable and any terms needed by
    the induction principle; [revert] also keeps their dependencies in scope.
    In particular, do not use [revert dependent], which could revert [x] itself. *)
Ltac induction_revert_except x keep :=
  repeat match goal with
  | H : _ |- _ =>
      let protected := constr:((x, keep)) in
      lazymatch protected with
      | context[H] => fail
      | _ => revert H
      end
  end.

Ltac induction_prepare x :=
  first [is_var x | intros until x];
  intros.

Ltac strong_induction_nat_named x IH :=
  induction_prepare x;
  (* A local definition must become a variable before abstracting over it. *)
  try clearbody x;
  induction_revert_except x tt;
  apply strong_induction_N with (n := x);
  clear x;
  intros x IH.

Ltac strong_induction_nat n :=
  let IH := fresh "IH" in strong_induction_nat_named n IH.

Close Scope nat_scope.

Open Scope Z_scope.

Lemma Z_ind_pos:
  forall (P: Z -> Prop),
  P 0 ->
  (forall z, z >= 0 -> P z -> P (z + 1)) ->
  forall z, z >= 0 -> P z.
Proof.
  intros P H0 Hstep z Hnonneg.

  (* Convert the problem to induction over natural numbers *)
  remember (Z.to_nat z) as n eqn:Heq.
  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hstep. lia. apply IHn1.
  }

  specialize(Hnneg n). rewrite Heq in Hnneg.
  replace (Z.of_nat (Z.to_nat z)) with (z) in Hnneg. apply Hnneg.
  rewrite Z2Nat.id. lia. lia.
Qed.

Lemma Z_induction_bidirectional :
  forall P : Z -> Prop,
  P 0 ->
  (forall n : Z, P n -> P (n + 1)) ->
  (forall n : Z, P n -> P (n - 1)) ->
  forall n : Z, P n.
Proof.
  intros P H0 Hpos Hneg n.

  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hpos. apply IHn1.
  }

  destruct (Z_lt_le_dec n 0).
  - replace n with (- Z.of_nat (Z.to_nat (- n))) by
      (rewrite Z2Nat.id; lia).
    induction (Z.to_nat (-n)).
    + simpl. apply H0.
    + replace (S n0) with (n0 + 1)%nat by lia. rewrite Nat2Z.inj_add.
      replace (- (Z.of_nat n0 + Z.of_nat 1)) with (-Z.of_nat n0 - 1) by lia. apply Hneg. apply IHn0.
  - apply Z_ind_pos.
    -- apply H0.
    -- intros z H. apply Hpos.
    -- lia.
Qed.

Lemma strong_induction_Z :
  forall P : Z -> Prop,
  (forall m, (forall k : Z, 0 <= k < m -> P k) -> P m) ->
  forall n, 0 <= n -> P n.
Proof.
  intros P H1 n H2. assert (H3: forall k, 0 <= k < n -> P k).
  - apply Z_induction_bidirectional with (n := n).
    -- lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
  - apply H1. intros k Hk. apply H3. lia.
Qed.

(** Strong induction over integers bounded below, including negative bounds. *)
Lemma strong_induction_Z_from : forall (lower : Z) (P : Z -> Prop),
  (forall m, lower <= m ->
    (forall k, lower <= k < m -> P k) -> P m) ->
  forall n, lower <= n -> P n.
Proof.
  intros lower P Hstep n Hn.
  assert (H : forall d : nat, forall m, m - lower = Z.of_nat d -> P m).
  {
    intro d. apply strong_induction_N with (n := d). intros j IH m Hm.
    apply Hstep; [lia |]. intros k Hk.
    apply (IH (Z.to_nat (k - lower))).
    - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
    - rewrite Z2Nat.id by lia. reflexivity.
  }
  apply (H (Z.to_nat (n - lower))). rewrite Z2Nat.id by lia. reflexivity.
Qed.

(** Induct over any type using a natural-number measure (e.g. list length).
    Recursive calls may use any value with a strictly smaller measure. *)
Lemma strong_induction_measure : forall (A : Type) (measure : A -> nat)
  (P : A -> Prop),
  (forall x, (forall y, (measure y < measure x)%nat -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros A measure P Hstep x.
  assert (H : forall n, forall y, measure y = n -> P y).
  {
    intro n. apply strong_induction_N with (n := n). intros k IH y Hy.
    apply Hstep. intros z Hz.
    apply (IH (measure z)); [lia | reflexivity].
  }
  apply (H (measure x)). reflexivity.
Qed.

Ltac strong_induction_Z_pos_named z IH :=
  induction_prepare z;
  let Hnonneg := fresh "Hnonneg" in
  assert (Hnonneg : 0 <= z) by
    first [lia | nia | fail "strong_induction: cannot prove a nonnegative integer; use 'from lower' for another lower bound"];
  try clearbody z;
  induction_revert_except z Hnonneg;
  pattern z;
  lazymatch goal with
  | |- ?P _ => refine (strong_induction_Z_from 0 P _ z Hnonneg)
  end;
  clear Hnonneg; clear z;
  let Hz := fresh IH "_lower" in intros z Hz IH;
  (* Preserve the original integer tactic's introduction of the first
     generalized premise, but also accept goals with no such premise. *)
  let H1 := fresh "H1" in
  lazymatch goal with
  | |- forall _ : _, _ => intro H1
  | _ => idtac
  end.

Ltac strong_induction_Z_pos z :=
  let IH := fresh "IH" in strong_induction_Z_pos_named z IH.

Ltac strong_induction_named x IH :=
  first [is_var x | intros until x];
  let T := type of x in
  let T := eval hnf in T in
  lazymatch T with
  | nat => strong_induction_nat_named x IH
  | Z => strong_induction_Z_pos_named x IH
  | _ => fail "strong_induction expects nat or Z; use 'using measure' for other types"
  end.

Ltac strong_induction x :=
  let IH := fresh "IH" in strong_induction_named x IH.

Ltac strong_induction_from_named z lower IH :=
  induction_prepare z;
  (* Snapshot the bound before generalizing hypotheses, and leave an explicit
     obligation when arithmetic cannot establish it automatically. *)
  let Hbound := fresh "Hbound" in
  assert (Hbound : lower <= z);
  [ first [lia | nia | idtac]
  | try clearbody z;
    induction_revert_except z (lower, Hbound);
    pattern z;
    lazymatch goal with
    | |- ?P _ => refine (strong_induction_Z_from lower P _ z Hbound)
    end;
    clear Hbound; clear z;
    let Hz := fresh IH "_lower" in intros z Hz IH ].

Ltac strong_induction_measure_named target measure IH :=
  induction_prepare target;
  try clearbody target;
  induction_revert_except target measure;
  apply (strong_induction_measure _ measure) with (x := target);
  clear target; intros target IH.

(** Usage:
      strong_induction n [as IH]              -- nat or nonnegative Z
      strong_induction z from lower [as IH]   -- Z, with lower <= z
      strong_induction xs using length [as IH] -- any nat-valued measure

    The variable may still be quantified in the goal. Generalized parameters
    and premises remain quantified in the step goal (the legacy Z form
    introduces its first premise). Integer steps retain their lower bound.
    Unproved bounds in the [from] form are left as separate goals. The default
    IH name is fresh; measures and lower bounds must be independent of the
    induction variable. *)
Tactic Notation "strong_induction" ident(x) :=
  let IH := fresh "IH" in strong_induction_named x IH.
Tactic Notation "strong_induction" ident(x) "as" ident(IH) :=
  strong_induction_named x IH.
Tactic Notation "strong_induction" ident(x) "from" constr(lower) "as" ident(IH) :=
  strong_induction_from_named x lower IH.
Tactic Notation "strong_induction" ident(x) "from" constr(lower) :=
  let IH := fresh "IH" in strong_induction_from_named x lower IH.
Tactic Notation "strong_induction" ident(x) "using" constr(measure) "as" ident(IH) :=
  strong_induction_measure_named x measure IH.
Tactic Notation "strong_induction" ident(x) "using" constr(measure) :=
  let IH := fresh "IH" in strong_induction_measure_named x measure IH.

Lemma well_ordering_principle_contrapositive_Z : forall E : Z -> Prop,
  (forall n : Z, E n -> n >= 0) ->
  (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
    (~(exists n, E n)).
Proof.
  intros E Hnon_neg H.
  set (E' := fun z => ~ E z).
  assert (E 0 -> False).
  { intros H2. apply H. exists 0. split; try split.
    - apply H2.
    - intros k _ H3. specialize (Hnon_neg k). apply Hnon_neg in H3. lia.
  }
  assert (H2: forall z, z >= 0 -> E' z).
  {
    intros z Hz. apply strong_induction_Z. intros m H2. destruct (Z_le_dec m 0).
    - unfold E'. unfold not. apply Z_le_lt_eq_dec in l. destruct l.
      -- specialize (Hnon_neg m). intros H3. apply Hnon_neg in H3. lia.
      -- rewrite e. apply H0.
    - assert (E m -> False).
      { intros H3. apply H. exists m. split; try split.
        - apply H3.
        - intros k H4 H5. specialize (H2 k). assert (E' k -> False). unfold E'.
          unfold not. intros H6. apply H6. apply H5. assert (0 <= k < m -> False) by auto.
          lia.
      }
      unfold E'. unfold not. apply H1.
    - lia.
  }
  unfold E' in H2. unfold not in H2. unfold not. intros H3. destruct H3 as [n H3].
  specialize (H2 n). apply H2. apply Hnon_neg in H3. apply H3. apply H3.
Qed.

Theorem well_ordering_Z : forall E : Z -> Prop,
  (forall z, E z -> z >= 0) ->
  (exists x, E x) ->
  (exists n, E n /\ forall m, m >= 0 -> E m -> (n <= m)).
Proof.
  intros E Hnon_neg [x Ex].
  assert (H :
    (forall n : Z, E n -> n >= 0) ->
      (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
      (~(exists n, E n))).
    { apply well_ordering_principle_contrapositive_Z. }

  destruct (classic (exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) as [C1|C2].
  - apply C1.
  - exfalso. apply H in C2. apply C2. exists x. apply Ex. apply Hnon_neg.
Qed.
