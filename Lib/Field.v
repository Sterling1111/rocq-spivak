Require Import Imports Sets Notations Complex Interval Reals_util.
Import SetNotations IntervalNotations.

Class Field (F : Type) := {
  add : F -> F -> F;
  mul : F -> F -> F;
  zero : F;
  one : F;
  opp : F -> F;
  inv : F -> F;
  H1 : ∀ a b c, add (add a b) c = add a (add b c);
  H2 : ∀ a, add a zero = a;
  H3 : ∀ a, add a (opp a) = zero;
  H4 : ∀ a b, add a b = add b a;
  H5 : ∀ a b c, mul (mul a b) c = mul a (mul b c);
  H6 : one <> zero;
  H7 : ∀ a, mul a one = a;
  H8 : ∀ a, a <> zero -> mul a (inv a) = one;
  H9 : ∀ a b, mul a b = mul b a;
  H10 : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
}.

Definition one_and_only_one_3 (P1 P2 P3 : Prop) : Prop :=
  (P1 /\ ~ P2 /\ ~ P3) \/ (~ P1 /\ P2 /\ ~ P3) \/ (~ P1 /\ ~ P2 /\ P3).

Class OrderedField (F : Type) {H : Field F} := {
  P : Ensemble F;
  H11 : ∀ a, one_and_only_one_3 (a = zero) (a ∈ P) (opp a ∈ P);
  H12 : ∀ a b, a ∈ P -> b ∈ P -> (add a b) ∈ P;
  H13 : ∀ a b, a ∈ P -> b ∈ P -> (mul a b) ∈ P
}.

Definition gt {F : Type} {H1 : Field F} {H2 : OrderedField F} (a b : F) : Prop :=
  (add a (opp b)) ∈ P.

Definition lt {F : Type} {H1 : Field F} {H2 : OrderedField F} (a b : F) : Prop :=
  gt b a.

Definition le {F : Type} {H1 : Field F} {H2 : OrderedField F} (a b : F) : Prop :=
  lt a b \/ a = b.

Definition ge {F : Type} {H1 : Field F} {H2 : OrderedField F} (a b : F) : Prop :=
  gt a b \/ a = b.

Definition is_upper_bound {F : Type} {H1 : Field F} {H2 : OrderedField F} (A : Ensemble F) (x : F) : Prop :=
  ∀ a, a ∈ A -> ge x a.

Definition bounded_above {F : Type} {H1 : Field F} {H2 : OrderedField F} (A : Ensemble F) : Prop :=
  ∃ x, is_upper_bound A x.

Definition is_least_upper_bound {F : Type} {H1 : Field F} {H2 : OrderedField F} (A : Ensemble F) (x : F) : Prop :=
  is_upper_bound A x /\ ∀ y, is_upper_bound A y -> le x y.

Class CompleteOrderedField (F : Type) {H1 : Field F} {H2 : OrderedField F} := {
  H14 : ∀ A : Ensemble F, (∃ a, a ∈ A) -> bounded_above A -> ∃ x, is_least_upper_bound A x
}.

Instance Field_R : Field ℝ.
Proof.
  apply (Build_Field R Rplus Rmult 0%R 1%R Ropp Rinv).
  - exact Rplus_assoc.
  - exact Rplus_0_r.
  - exact Rplus_opp_r.
  - exact Rplus_comm.
  - exact Rmult_assoc.
  - exact R1_neq_R0.
  - exact Rmult_1_r.
  - exact Rinv_r.
  - exact Rmult_comm.
  - exact Rmult_plus_distr_l.
Defined.

Instance Field_C : Field ℂ.
Proof.
  apply (Build_Field ℂ Cplus Cmult 0 1 Copp Cinv).
  - exact Cplus_assoc.
  - exact Cplus_0_r.
  - exact Cplus_opp_r.
  - exact Cplus_comm.
  - exact Cmult_assoc.
  - exact C1_neq_C0.
  - exact Cmult_1_r.
  - exact Cinv_r.
  - exact Cmult_comm.
  - exact Cmult_plus_distr_l.
Qed.

Instance OrderedField_R : OrderedField ℝ.
Proof.
  apply (Build_OrderedField R Field_R (0, ∞)).
  - intros a. unfold one_and_only_one_3. unfold Ensembles.In. simpl.
    destruct (total_order_T a 0) as [[H1 | H2] | H3].
    + right. right. split. 
      * intros H4. rewrite H4 in H1. exact (Rlt_irrefl 0 H1).
      * split.
        -- intros H4. exfalso. apply (Rlt_asym a 0 H1 H4).
        -- apply Ropp_0_gt_lt_contravar. exact H1.
    + left. split. exact H2. split.
      * rewrite H2. apply Rlt_irrefl.
      * rewrite H2. rewrite Ropp_0. apply Rlt_irrefl.
    + right. left. split.
      * intros H4. rewrite H4 in H3. exact (Rlt_irrefl 0 H3).
      * split. 
        -- exact H3.
        -- intros H4. apply (Rplus_lt_compat_r a) in H4. 
           rewrite Rplus_0_l in H4. rewrite Rplus_opp_l in H4.
           exfalso. apply (Rlt_asym 0 a H3 H4).
  - intros a b. unfold Ensembles.In. simpl. intros H1 H2. apply Rplus_lt_0_compat; assumption.
  - intros a b. unfold Ensembles.In. simpl. intros H1 H2. apply Rmult_lt_0_compat; assumption.
Defined.

Instance CompleteOrderedField_R : CompleteOrderedField ℝ.
Proof.
  apply (Build_CompleteOrderedField R Field_R OrderedField_R).
  intros A H1 H2.
  assert (H3 : bound A).
  { destruct H2 as [u H2]. exists u. intros x H3.
    apply H2 in H3. unfold ge, gt, add, opp, Ensembles.In in H3. simpl in H3.
    destruct H3 as [H3 | H3].
    - apply (Rplus_lt_compat_r x) in H3. rewrite Rplus_0_l in H3.
      rewrite Rplus_assoc in H3. rewrite Rplus_opp_l in H3. rewrite Rplus_0_r in H3.
      apply Rlt_le. exact H3.
    - rewrite H3. apply Rle_refl. }
  pose proof (completeness A H3 H1) as [m [H4 H5]].
  exists m. split.
  - intros a H6. apply H4 in H6. unfold ge, gt, add, opp, Ensembles.In. simpl.
    destruct (total_order_T m a) as [[H7 | H7] | H7].
    + apply Rle_not_lt in H6. contradiction.
    + right. exact H7.
    + left. apply (Rplus_lt_compat_r (-a)) in H7. rewrite Rplus_opp_r in H7.
      exact H7.
  - intros y H6. unfold le, lt, gt, add, opp, Ensembles.In. simpl.
    destruct (total_order_T m y) as [[H7 | H7] | H7].
    + left. apply (Rplus_lt_compat_r (-m)) in H7. rewrite Rplus_opp_r in H7.
      exact H7.
    + right. exact H7.
    + assert (H8 : Raxioms.is_upper_bound A y).
      { intros x H8. apply H6 in H8. unfold ge, gt, add, opp, Ensembles.In in H8. simpl in H8.
        destruct H8 as [H8 | H8].
        - apply (Rplus_lt_compat_r x) in H8. rewrite Rplus_0_l in H8.
          rewrite Rplus_assoc in H8. rewrite Rplus_opp_l in H8. rewrite Rplus_0_r in H8.
          apply Rlt_le. exact H8.
        - rewrite H8. apply Rle_refl. }
      apply H5 in H8. exfalso. apply (Rle_not_lt y m H8 H7).
Qed.
