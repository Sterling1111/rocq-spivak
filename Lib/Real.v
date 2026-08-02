Require Import Imports Notations Sets Field WI_SI_WO.
From Stdlib Require Import Lqa.
Import SetNotations.

Open Scope Q_scope.

Record Real := {
  alpha : Ensemble ℚ;
  Real_P1 : ∀ x y : ℚ, x ∈ alpha -> y < x -> y ∈ alpha;
  Real_P2 : alpha ≠ ∅;
  Real_P3 : alpha ≠ ℚ;
  Real_P4 : ∀ x : ℚ, x ∈ alpha -> ∃ y : ℚ, y ∈ alpha /\ y > x 
}.

Lemma Real_equiv : ∀ α β : Real,
  alpha α = alpha β -> α = β.
Proof.
  intros [α H1 H2 H3 H4] [β H5 H6 H7 H8] H9.
  simpl in H9.
  subst.
  f_equal;
  apply proof_irrelevance.
Qed.

Declare Scope Real_scope.

Open Scope Real_scope.

Definition Rlt (α β : Real) : Prop :=
  α.(alpha) ⊆ β.(alpha) /\ α.(alpha) ≠ β.(alpha).

Definition Rle (α β : Real) : Prop := 
  α.(alpha) ⊆ β.(alpha).

Definition Rgt (α β : Real) : Prop := 
  Rlt β α.

Definition Rge (α β : Real) : Prop := 
  Rle β α.

Infix "<" := Rlt : Real_scope.
Infix "<=" := Rle : Real_scope.
Infix ">" := Rgt : Real_scope.
Infix ">=" := Rge : Real_scope.

Definition is_upper_bound (A : Ensemble Real) (ub : Real) : Prop :=
  ∀ x, x ∈ A -> x <= ub.

Definition bounded_above (A : Ensemble Real) : Prop :=
  ∃ ub, is_upper_bound A ub.

Definition least_upper_bound (A : Ensemble Real) (lub : Real) : Prop :=
  is_upper_bound A lub /\ ∀ ub, is_upper_bound A ub -> lub <= ub.

Theorem theorem_29_1 : ∀ A,
  A ≠ ∅ -> bounded_above A -> ∃ lub, least_upper_bound A lub.
Proof.
  intros A H1 H2.
  pose (β := λ x, ∃ α, α ∈ A /\ x ∈ α.(alpha)).
  
  assert (H3 : ∀ x y, x ∈ β -> (y < x)%Q -> y ∈ β).
  {
    intros x y [α [H7 H8]] H9.
    exists α. split; auto. apply (Real_P1 α x); auto. 
  }
    
  assert (H4 : β ≠ ⦃⦄).
  {
    apply not_Empty_In in H1 as [α H7].
    pose proof (Real_P2 α) as H8.
    apply not_Empty_In in H8 as [x H9].
    apply not_Empty_In. exists x, α. split; auto. 
  }
    
  assert (H5 : β ≠ Full_set ℚ).
  {
    destruct H2 as [γ H7].
    pose proof (Real_P3 γ) as H8.
    intros H9.
    apply H8.
    apply Extensionality_Ensembles.
    split; intros x H10; [apply Full_intro |].
    assert (H11 : x ∈ β).
    { rewrite H9. apply Full_intro. }
    destruct H11 as [α [H12 H13]].
    apply H7 in H12.
    apply H12. apply H13.
  }
    
  assert (H6 : ∀ x, x ∈ β -> ∃ y, y ∈ β /\ (x < y)%Q).
  {
    intros x [α [H7 H8]].
    pose proof (Real_P4 α x H8) as [y [H9 H10]].
    exists y. split; auto. exists α. split; auto.
  }
    
  set (lub := {| alpha := β; Real_P1 := H3; Real_P2 := H4; Real_P3 := H5; Real_P4 := H6 |}).
  exists lub. split.
  - intros α H7 x H8.
    exists α. split; auto.
  - intros γ H7 x [α [H8 H9]].
    apply H7 in H8.
    apply H8. apply H9.
Qed.

Definition Rplus_set (α β : Real) : Ensemble ℚ :=
  λ z, ∃ x y : ℚ, x ∈ α.(alpha) /\ y ∈ β.(alpha) /\ (z == x + y)%Q.

Theorem theorem_29_2 : ∀ α β : Real, 
  ∃ γ : Real, γ.(alpha) = Rplus_set α β.
Proof.
  intros α β.
  pose (S := Rplus_set α β).

  assert (H1 : ∀ x y, x ∈ S -> (y < x)%Q -> y ∈ S).
  {
    intros x y [x1 [y1 [H5 [H6 H7]]]] H8.
    unfold S, Rplus_set. exists (y - y1)%Q, y1.
    split.
    - apply (Real_P1 α x1); auto. rewrite H7 in H8. apply Qplus_lt_l with (z:=y1). ring_simplify. rewrite Qplus_comm. exact H8.
    - split; auto. ring.
  }

  assert (H2 : S ≠ ∅).
  {
    pose proof (Real_P2 α) as H5. apply not_Empty_In in H5 as [x1 H6].
    pose proof (Real_P2 β) as H7. apply not_Empty_In in H7 as [y1 H8].
    apply not_Empty_In. exists (x1 + y1)%Q.
    unfold S, Rplus_set. exists x1, y1. split; auto. split; auto. reflexivity.
  }

  assert (H3 : S ≠ ℚ).
  {
    intros H5.
    pose proof (Real_P3 α) as H6.
    assert (H7 : exists x, x ∉ alpha α).
    {
      apply not_all_ex_not. intros H8. apply H6. apply Extensionality_Ensembles.
      split; intros x H9. apply Full_intro. apply H8.
    }
    destruct H7 as [ub_a H10].
    pose proof (Real_P3 β) as H11.
    assert (H12 : exists x, x ∉ alpha β).
    {
      apply not_all_ex_not. intros H13. apply H11. apply Extensionality_Ensembles.
      split; intros x H14. apply Full_intro. apply H13.
    }
    destruct H12 as [ub_b H15].
    assert (H16 : (ub_a + ub_b)%Q ∈ S).
    { rewrite H5. apply Full_intro. }
    unfold S, Rplus_set in H16.
    destruct H16 as [x [y [H17 [H18 H19]]]].
    assert (H20 : (x < ub_a)%Q).
    {
      destruct (Q_dec x ub_a) as [[H21 | H22] | H23].
      - exact H21.
      - apply (Real_P1 α x) in H22; auto. contradiction.
      - pose proof (Real_P4 α x H17) as [z [H24 H25]].
        assert (H26 : (ub_a < z)%Q).
        { rewrite <- H23. exact H25. }
        apply (Real_P1 α z) in H26; auto. contradiction.
    }
    assert (H27 : (y < ub_b)%Q).
    {
      destruct (Q_dec y ub_b) as [[H28 | H29] | H30].
      - exact H28.
      - apply (Real_P1 β y) in H29; auto. contradiction.
      - pose proof (Real_P4 β y H18) as [z [H31 H32]].
        assert (H33 : (ub_b < z)%Q).
        { rewrite <- H30. exact H32. }
        apply (Real_P1 β z) in H33; auto. contradiction.
    }
    assert (H34 : (ub_a + ub_b < ub_a + ub_b)%Q).
    { rewrite H19 at 1. apply Qplus_lt_compat; auto. }
    apply Qlt_irrefl in H34. contradiction.
  }

  assert (H4 : ∀ x : ℚ, x ∈ S -> ∃ y : ℚ, y ∈ S /\ (x < y)%Q).
  {
    intros x [x1 [y1 [H5 [H6 H7]]]].
    pose proof (Real_P4 α x1 H5) as [x2 [H8 H9]].
    pose proof (Real_P4 β y1 H6) as [y2 [H10 H11]].
    unfold S, Rplus_set. exists (x2 + y2)%Q.
    split.
    - exists x2, y2. split; auto. split; auto. reflexivity.
    - rewrite H7. apply Qplus_lt_compat; auto.
  }

  set (lub := {| alpha := S; Real_P1 := H1; Real_P2 := H2; Real_P3 := H3; Real_P4 := H4 |}).
  exists lub. simpl. reflexivity.
Qed.

Definition Rplus (α β : Real) : Real :=
  proj1_sig (constructive_indefinite_description _ (theorem_29_2 α β)).

Infix "+" := Rplus : Real_scope.

Theorem theorem_29_3 : ∀ α β γ : Real, 
  (α + β) + γ = α + (β + γ).
Proof.
  intros α β γ.
  apply Real_equiv.
  unfold Rplus.
  destruct (constructive_indefinite_description _ (theorem_29_2 α β)) as [α_β H2]; simpl.
  destruct (constructive_indefinite_description _ (theorem_29_2 α_β γ)) as [αβ_γ H3]; simpl.
  destruct (constructive_indefinite_description _ (theorem_29_2 β γ)) as [β_γ H4]; simpl.
  destruct (constructive_indefinite_description _ (theorem_29_2 α β_γ)) as [α_βγ H5]; simpl.
  rewrite H3, H5.
  unfold Rplus_set.
  apply Extensionality_Ensembles.
  split; intros x H6.
  - destruct H6 as [x_ab [x_c [H7 [H8 H9]]]].
    rewrite H2 in H7.
    destruct H7 as [x_a [x_b [H10 [H11 H12]]]].
    exists x_a, (x_b + x_c)%Q.
    split; auto.
    split.
    + rewrite H4. exists x_b, x_c. split; auto. split; auto. reflexivity.
    + rewrite H9, H12. ring.
  - destruct H6 as [x_a [x_bc [H7 [H8 H9]]]].
    rewrite H4 in H8.
    destruct H8 as [x_b [x_c [H10 [H11 H12]]]].
    exists (x_a + x_b)%Q, x_c.
    split.
    + rewrite H2. exists x_a, x_b. repeat split; auto.
    + split; auto.
      rewrite H9, H12. ring.
Qed.

Theorem theorem_29_4 : ∀ α β : Real,
  α + β = β + α.
Proof.
  intros α β.
  apply Real_equiv.
  unfold Rplus.
  destruct (constructive_indefinite_description _ (theorem_29_2 α β)) as [α_β H2]; simpl.
  destruct (constructive_indefinite_description _ (theorem_29_2 β α)) as [β_α H3]; simpl.
  rewrite H2, H3.
  unfold Rplus_set.
  apply Extensionality_Ensembles.
  split; intros x H4.
  - destruct H4 as [x_a [x_b [H5 [H6 H7]]]].
    exists x_b, x_a.
    split; auto.
    split; auto.
    rewrite H7. ring.
  - destruct H4 as [x_b [x_a [H5 [H6 H7]]]].
    exists x_a, x_b.
    split; auto.
    split; auto.
    rewrite H7. ring.
Qed.

Definition Rzero_set : Ensemble ℚ :=
  λ x : ℚ, (x < 0)%Q.

Theorem theorem_29_5 :
  ∃ α : Real,
    α.(alpha) = Rzero_set.
Proof.
  assert (H1 : ∀ x y : ℚ, x ∈ Rzero_set -> (y < x)%Q -> y ∈ Rzero_set).
  {
    intros x y Hx Hlt. unfold Ensembles.In, Rzero_set in *. eapply Qlt_trans; eauto.
  }
  assert (H2 : Rzero_set ≠ ∅).
  {
    apply not_Empty_In. exists (-1)%Q. unfold Ensembles.In, Rzero_set. reflexivity.
  }
  assert (H3 : Rzero_set ≠ ℚ).
  {
    intros H_eq.
    assert (H_0 : (0 ∈ ℚ)%type). { apply Full_intro. }
    rewrite <- H_eq in H_0. unfold Ensembles.In, Rzero_set in H_0. apply Qlt_irrefl in H_0. contradiction.
  }
  assert (H4 : ∀ x : ℚ, x ∈ Rzero_set -> ∃ y : ℚ, y ∈ Rzero_set /\ (x < y)%Q).
  {
    intros [n d] Hx. unfold Ensembles.In, Rzero_set in *.
    exists (n # (d * 2)).
    unfold Ensembles.In, Rzero_set.
    unfold Qlt in *. simpl in *.
    rewrite Pos2Z.inj_mul.
    split.
    - nia.
    - assert (Hd : (0 < Z.pos d)%Z) by reflexivity. nia.
  }
  exists {| alpha := Rzero_set; Real_P1 := H1; Real_P2 := H2; Real_P3 := H3; Real_P4 := H4 |}.
  simpl. reflexivity.
Qed.

Definition Rzero : Real :=
  proj1_sig (constructive_indefinite_description _ theorem_29_5).

Notation "0" := Rzero : Real_scope.

Theorem theorem_29_6 : ∀ α : Real,
  α + 0 = α.
Proof.
  intros α.
  apply Real_equiv.
  unfold Rplus.
  destruct (constructive_indefinite_description _ (theorem_29_2 α Rzero)) as [α_Rzero H2]; simpl.
  rewrite H2.
  unfold Rplus_set.
  apply Extensionality_Ensembles.
  split; intros x H3.
  - destruct H3 as [x_a [x_zero [H4 [H5 H6]]]].
    assert (H7 : alpha Rzero = Rzero_set).
    { apply (proj2_sig (constructive_indefinite_description _ theorem_29_5)). }
    rewrite H7 in H5.
    unfold Ensembles.In, Rzero_set in H5.
    assert (H8 : (x < x_a)%Q).
    { rewrite H6. rewrite Qplus_comm. apply Qplus_lt_l with (z:=x_a) (x:=x_zero) (y:=0%Q) in H5. ring_simplify in H5. exact H5. }
    apply (Real_P1 α x_a); auto.
  - pose proof (Real_P4 α x H3) as [y [H4 H5]].
    exists y, (x - y)%Q.
    split; auto.
    split.
    + assert (H7 : alpha Rzero = Rzero_set).
      { exact (proj2_sig (constructive_indefinite_description _ theorem_29_5)). }
      rewrite H7. unfold Ensembles.In, Rzero_set. 
      assert (H6 : (x - y < 0)%Q). { apply Qplus_lt_l with (z:=y) (x:=(x-y)%Q) (y:=0%Q). ring_simplify. exact H5. }
      exact H6.
    + ring.
Qed.

Definition Ropp_set (α : Real) : Ensemble ℚ :=
  λ x : ℚ, ∃ y : ℚ, y ∉ α.(alpha) /\ (y < -x)%Q.

Theorem theorem_29_7 : ∀ α : Real, 
  ∃ β : Real, β.(alpha) = Ropp_set α.
Proof.
  intros α.
  pose (S := Ropp_set α).
  assert (H1 : ∀ x y : ℚ, x ∈ S -> (y < x)%Q -> y ∈ S).
  { intros x y [r [H1 H2]] H3. exists r; split; auto; lra. }
  assert (H2 : S ≠ ∅).
  {
    pose proof (Real_P3 α) as H3.
    assert (exists x, x ∉ alpha α) as [r H4].
    { 
      apply not_all_ex_not. intros H4. apply H3. apply Extensionality_Ensembles.
      split; intros x _. apply Full_intro. apply H4. 
    }
    apply not_Empty_In. exists (-r - 1)%Q, r. split; auto; lra.
  }
  assert (H3 : S ≠ ℚ).
  {
    intros H3.
    pose proof (Real_P2 α) as H4.
    apply not_Empty_In in H4 as [x H5].
    assert (H6 : (-x)%Q ∈ S).
    { rewrite H3. apply Full_intro. }
    destruct H6 as [y [H6 H7]].
    apply H6.
    apply (Real_P1 α x y H5).
    lra.
  }
  assert (H4 : ∀ x : ℚ, x ∈ S -> ∃ y : ℚ, y ∈ S /\ (x < y)%Q).
  {
    intros x [y [H4 H5]].
    exists ((x + -y) * (1#2))%Q.
    split; [ exists y; split; auto; lra | lra].
  }
  exists {| alpha := S; Real_P1 := H1; Real_P2 := H2; Real_P3 := H3; Real_P4 := H4 |}.
  reflexivity.
Qed.

Definition Ropp (α : Real) : Real :=
  proj1_sig (constructive_indefinite_description _ (theorem_29_7 α)).

Notation "- α" := (Ropp α) : Real_scope.

Definition Rminus (α β : Real) : Real := α + (- β).
Infix "-" := Rminus : Real_scope.

Definition nat_to_Q (n : nat) : ℚ := (Z.of_nat n # 1).

Lemma nat_to_Q_S : forall n, nat_to_Q (S n) == nat_to_Q n + 1.
Proof.
  intros. unfold nat_to_Q. unfold Qeq, Qplus. simpl.
  nia.
Qed.

Lemma archimedean_Q : forall (q : ℚ), exists n : nat, (q < nat_to_Q n)%Q.
Proof.
  intros [n d].
  exists (Z.to_nat (Z.abs n + 1)).
  unfold nat_to_Q, Qlt. simpl.
  pose proof (Pos2Z.is_pos d).
  nia.
Qed.

Lemma lemma_29_1 : ∀ (α : Real) (z : ℚ),
  (0 < z)%Q ->
  ∃ x y : ℚ,
    x ∈ α.(alpha) /\
    y ∉ α.(alpha) /\
    (y - x == z)%Q /\
    (∃ w : ℚ, w ∉ α.(alpha) /\ (w < y)%Q).
Proof.
  intros α z H1.
  pose proof (Real_P2 α) as H2.
  apply not_Empty_In in H2 as [a H3].
  pose proof (Real_P3 α) as H4.
  assert (exists b, b ∉ alpha α) as [b H5].
  {
    apply not_all_ex_not. intros H6. apply H4. apply Extensionality_Ensembles.
    split; intros p _. apply Full_intro. apply H6. 
  }
  pose proof (archimedean_Q ((b - a) * / z)%Q) as [M H6].
  assert (H7 : (b < a + nat_to_Q M * z)%Q).
  {
    apply Qmult_lt_r with (z:=z) in H6; auto.
    assert (H8 : (/z * z == 1)%Q) by (rewrite Qmult_comm; apply Qmult_inv_r; lra).
    assert (H9 : ((b - a) * / z * z == b - a)%Q).
    { rewrite <- Qmult_assoc. rewrite H8. ring. }
    rewrite H9 in H6. lra. 
  }
  assert (H8 : (a + nat_to_Q M * z)%Q ∉ alpha α).
  { intros H9. apply H5. apply (Real_P1 α (a + nat_to_Q M * z)%Q b); auto. }
  assert (H9 : forall x y, (x == y)%Q -> x ∈ alpha α -> y ∈ alpha α).
  {
    intros p q H10 H11. pose proof (Real_P4 α p H11) as [p' [H12 H13]].
    apply (Real_P1 α p' q); auto. lra. 
  }
  assert (H10 : forall n : nat,
    (a + nat_to_Q n * z)%Q ∉ alpha α ->
    exists k : nat,
      (a + nat_to_Q k * z)%Q ∈ alpha α /\
      (a + nat_to_Q (S k) * z)%Q ∉ alpha α).
  {
    induction n as [|n H11].
    - intros H12. exfalso. apply H12. apply (H9 a).
      + unfold nat_to_Q; simpl. ring.
      + exact H3.
    - intros H12. destruct (excluded_middle_informative ((a + nat_to_Q n * z)%Q ∈ alpha α)) as [H13 | H14].
      + exists n. split; auto.
      + apply H11. exact H14. 
  }
  pose proof (H10 M H8) as [k [H11 H12]].
  pose proof (Real_P4 α _ H11) as [x [H13 H14]].
  exists x, (x + z)%Q.
  split; auto.
  split.
  - intros H15. apply H12. apply (Real_P1 α (x + z)%Q); auto.
    rewrite nat_to_Q_S. lra.
  - split; [ring |].
    exists (a + nat_to_Q (S k) * z)%Q.
    split; auto.
    rewrite nat_to_Q_S. lra.
Qed.

Theorem theorem_29_8 : ∀ α : Real,
  α + (- α) = 0.
Proof.
  intros α.
  apply Real_equiv.
  unfold Rplus.
  destruct (constructive_indefinite_description _ (theorem_29_2 α (- α))) as [α_opp H1]; simpl.
  rewrite H1.
  assert (H2 : alpha 0 = Rzero_set).
  { apply (proj2_sig (constructive_indefinite_description _ theorem_29_5)). }
  rewrite H2.
  apply Extensionality_Ensembles.
  split; intros z H3.
  - destruct H3 as [x [y [H4 [H5 H6]]]].
    unfold Ensembles.In, Rzero_set.
    assert (H7 : alpha (- α) = Ropp_set α).
    { apply (proj2_sig (constructive_indefinite_description _ (theorem_29_7 α))). }
    rewrite H7 in H5.
    unfold Ropp_set, Ensembles.In in H5.
    destruct H5 as [w [H8 H9]].
    assert (H10 : (x < w)%Q).
    {
      destruct (Q_dec x w) as [[H11 | H12] | H13].
      - exact H11.
      - apply (Real_P1 α x w) in H12; auto. contradiction.
      - pose proof (Real_P4 α x H4) as [x' [Hx1 Hx2]].
        assert (H14 : (w < x')%Q) by lra.
        apply (Real_P1 α x' w Hx1) in H14.
        contradiction.
    }
    rewrite H6. lra.
  - unfold Ensembles.In, Rzero_set in H3.
    assert (H4 : (0 < -z)%Q) by lra.
    pose proof (lemma_29_1 α (-z)%Q H4) as [x [y [H5 [H6 [H7 [w [H8 H9]]]]]]].
    exists x, (-y)%Q.
    split; auto.
    split.
    + assert (H10 : alpha (- α) = Ropp_set α).
      { apply (proj2_sig (constructive_indefinite_description _ (theorem_29_7 α))). }
      rewrite H10.
      unfold Ropp_set, Ensembles.In.
      exists w. split; auto.
      assert (H11 : (- - y == y)%Q) by ring.
      rewrite H11. exact H9.
    + lra.
Qed.

Definition P := λ α, α > 0.

Lemma lemma_29_2 : ∀ α β,
  α ∈ P -> β ∈ P -> (α + β) ∈ P.
Proof.
  intros α β H1 H2.
  unfold P, Rgt, Rlt in *.
  destruct H1 as [H3 H4].
  destruct H2 as [H5 H6].

  assert (H7 : alpha (α + β) = Rplus_set α β).
  {
    unfold Rplus.
    apply (proj2_sig
      (constructive_indefinite_description _ (theorem_29_2 α β))).
  }

  assert (H8 : alpha 0 = Rzero_set).
  {
    apply (proj2_sig
      (constructive_indefinite_description _ theorem_29_5)).
  }

  assert (∃ a : ℚ, a ∈ alpha α /\ a ∉ alpha 0) as [a [H9 H10]].
  {
    apply NNPP.
    intros H11.
    apply H4.
    apply Extensionality_Ensembles.
    split.
    - exact H3.
    - intros x H12.
      apply NNPP.
      intros H13.
      apply H11.
      exists x.
      split; auto.
  }

  rewrite H8 in H10.
  unfold Ensembles.In, Rzero_set in H10.

  pose proof (Real_P4 α a H9) as [a' [H11 H12]].

  split.
  - intros x H13.
    rewrite H7.
    unfold Rplus_set.

    rewrite H8 in H13.
    unfold Ensembles.In, Rzero_set in H13.

    exists a', (x - a')%Q.
    split.
    + exact H11.
    + split.
      * apply H5.
        rewrite H8.
        unfold Ensembles.In, Rzero_set.
        lra.
      * ring.
  - intros H13.
    apply H6.
    apply Extensionality_Ensembles.
    split.
    + exact H5.
    + intros x H14.
      rewrite H13.
      rewrite H7.
      unfold Rplus_set.

      exists a', (x - a')%Q.
      split.
      * exact H11.
      * split.
        -- apply (Real_P1 β x); auto.
           lra.
        -- ring.
Qed.

Theorem theorem_29_9 : ∀ α,
  one_and_only_one_3 (α = 0) (α ∈ P) (-α ∈ P).
Proof.
  intros α.

  assert (H1 : alpha 0 = Rzero_set).
  {
    apply (proj2_sig
      (constructive_indefinite_description _ theorem_29_5)).
  }

  unfold one_and_only_one_3.
  destruct (excluded_middle_informative (α = 0)) as [H2 | H2].
  - left.
    split.
    + exact H2.
    + split.
      * intros H3.
        subst α.
        unfold P, Rgt, Rlt in H3.
        destruct H3 as [H3 H4].
        apply H4.
        reflexivity.
      * intros H3.
        assert (H4 : -0 = 0).
        {
          pose proof (theorem_29_8 0) as H4.
          rewrite theorem_29_4 in H4.
          rewrite theorem_29_6 in H4.
          exact H4.
        }
        subst α.
        rewrite H4 in H3.
        unfold P, Rgt, Rlt in H3.
        destruct H3 as [H3 H5].
        apply H5.
        reflexivity.

  - destruct (excluded_middle_informative (α ∈ P)) as [H3 | H3].
    + right.
      left.
      split.
      * exact H2.
      * split.
        -- exact H3.
        -- intros H4.
           pose proof (lemma_29_2 α (-α) H3 H4) as H5.
           rewrite theorem_29_8 in H5.
           unfold P, Rgt, Rlt in H5.
           destruct H5 as [H5 H6].
           apply H6.
           reflexivity.

    + right.
      right.
      split.
      * exact H2.
      * split.
        -- exact H3.
        -- unfold P, Rgt, Rlt.

           assert (H4 : alpha α ⊆ alpha 0).
           {
             intros x H4.
             apply NNPP.
             intros H5.
             apply H3.
             unfold P, Rgt, Rlt.
             split.
             - intros y H6.
               rewrite H1 in H6.
               unfold Ensembles.In, Rzero_set in H6.

               assert (H7 : ~ (x < 0)%Q).
               {
                 intros H7.
                 apply H5.
                 rewrite H1.
                 unfold Ensembles.In, Rzero_set.
                 exact H7.
               }

               apply (Real_P1 α x y H4).
               lra.
             - intros H6.
               apply H2.
               apply Real_equiv.
               symmetry.
               exact H6.
           }

           assert (H5 : alpha α ≠ alpha 0).
           {
             intros H5.
             apply H2.
             apply Real_equiv.
             exact H5.
           }

           assert (∃ y : ℚ, y ∈ alpha 0 /\ y ∉ alpha α)
             as [y [H6 H7]].
           {
             apply NNPP.
             intros H6.
             apply H5.
             apply Extensionality_Ensembles.
             split.
             - exact H4.
             - intros x H7.
               apply NNPP.
               intros H8.
               apply H6.
               exists x.
               split; auto.
           }

           assert (H8 : (y < 0)%Q).
           {
             rewrite H1 in H6.
             unfold Ensembles.In, Rzero_set in H6.
             exact H6.
           }

           assert (H9 : alpha (-α) = Ropp_set α).
           {
             apply (proj2_sig
               (constructive_indefinite_description _
                 (theorem_29_7 α))).
           }

           split.
           ++ intros x H10.
              rewrite H9.
              unfold Ropp_set, Ensembles.In.
              exists y.
              split.
              ** exact H7.
              ** rewrite H1 in H10.
                 unfold Ensembles.In, Rzero_set in H10.
                 lra.
           ++ intros H10.
              assert (H11 : (-y * (1#2))%Q ∈ alpha (-α)).
              {
                rewrite H9.
                unfold Ropp_set, Ensembles.In.
                exists y.
                split; auto.
                lra.
              }
              rewrite <- H10 in H11.
              rewrite H1 in H11.
              unfold Ensembles.In, Rzero_set in H11.
              lra.
Qed.

Theorem theorem_29_10 : ∀ α β γ,
  α > β -> α + γ > β + γ.
Proof.
  intros α β γ H1.
  unfold Rgt, Rlt in *.
  destruct H1 as [H1 H2].
  split.
  - intros x H3.

    assert (H4 : alpha (β + γ) = Rplus_set β γ).
    {
      unfold Rplus.
      apply (proj2_sig
        (constructive_indefinite_description _ (theorem_29_2 β γ))).
    }

    assert (H5 : alpha (α + γ) = Rplus_set α γ).
    {
      unfold Rplus.
      apply (proj2_sig
        (constructive_indefinite_description _ (theorem_29_2 α γ))).
    }

    rewrite H4 in H3.
    rewrite H5.
    unfold Rplus_set in *.
    destruct H3 as [y [z [H6 [H7 H8]]]].
    exists y, z.
    split.
    + apply H1.
      exact H6.
    + split; auto.

  - intros H3.
    apply H2.

    assert (H4 : β + γ = α + γ).
    {
      apply Real_equiv.
      exact H3.
    }

    assert (H5 : β = α).
    {
      transitivity ((β + γ) + (-γ)).
      - rewrite theorem_29_3.
        rewrite theorem_29_8.
        rewrite theorem_29_6.
        reflexivity.
      - rewrite H4.
        rewrite theorem_29_3.
        rewrite theorem_29_8.
        rewrite theorem_29_6.
        reflexivity.
    }

    rewrite H5.
    reflexivity.
Qed.

Lemma Rtotal_order_dec : ∀ α β : Real,
  {α < β} + {α = β} + {α > β}.
Proof.
  intros α β.
  destruct (excluded_middle_informative (α < β)) as [H1 | H1].
  - exact (inleft (left H1)).
  - destruct (excluded_middle_informative (α = β)) as [H2 | H2].
    + exact (inleft (right H2)).
    + right.
      unfold Rgt, Rlt in *.
      split.
      * intros x Hx. apply NNPP. intros Hnot.
        assert (H_subset : α.(alpha) ⊆ β.(alpha)).
        { intros y Hy.
          destruct (Q_dec y x) as [[H_lt | H_gt] | H_eq].
          - apply (Real_P1 β x y); auto.
          - apply (Real_P1 α y x) in H_gt; auto. contradiction.
          - pose proof (Real_P4 β x Hx) as [z [Hz1 Hz2]].
            assert (Hyz : (y < z)%Q) by lra.
            apply (Real_P1 β z y Hz1 Hyz). }
        assert (H_neq : α.(alpha) <> β.(alpha)).
        { intros Heq. apply H2. apply Real_equiv. auto. }
        apply H1. split; auto.
      * intros Heq. apply H2. apply Real_equiv. symmetry. exact Heq.
Qed.

Lemma Rlt_dec : ∀ α β : Real, {α < β} + {~ (α < β)}.
Proof.
  intros α β. apply excluded_middle_informative.
Qed.

Lemma Rle_dec : ∀ α β : Real, {α <= β} + {~ (α <= β)}.
Proof.
  intros α β. apply excluded_middle_informative.
Qed.

Lemma Rgt_dec : ∀ α β : Real, {α > β} + {~ (α > β)}.
Proof.
  intros α β. apply excluded_middle_informative.
Qed.

Lemma Rge_dec : ∀ α β : Real, {α >= β} + {~ (α >= β)}.
Proof.
  intros α β. apply excluded_middle_informative.
Qed.

Definition Rabs (α : Real) : Real :=
  match Rle_dec 0 α with
  | left _ => α
  | right _ => -α
  end.

Notation "| α |" := (Rabs α)
  (at level 35, α at level 0, format "| α |", no associativity) : Real_scope.

Definition Rmult_set_pos (α β : Real) : Ensemble ℚ :=
  fun z =>
    (z < 0)%Q \/
    ∃ x y,
      x ∈ α.(alpha) /\
      y ∈ β.(alpha) /\
      (0 < x)%Q /\
      (0 < y)%Q /\
      (z < x * y)%Q.

Theorem theorem_29_11 : ∀ α β : Real,
  ∃ γ : Real, γ.(alpha) = Rmult_set_pos α β.
Proof.
  intros α β.
  pose (S := Rmult_set_pos α β).

  assert (H1 : ∀ x y : ℚ, x ∈ S -> (y < x)%Q -> y ∈ S).
  {
    intros x y H5 H6.
    unfold S, Rmult_set_pos in *.
    destruct H5 as [H5 | H5].
    - left.
      lra.
    - right.
      destruct H5 as [a [b [H7 [H8 [H9 [H10 H11]]]]]].
      exists a, b.
      repeat split; auto.
      lra.
  }

  assert (H2 : S ≠ ∅).
  {
    apply not_Empty_In.
    exists (-1)%Q.
    unfold S, Rmult_set_pos.
    left.
    lra.
  }

  assert (H3 : S ≠ ℚ).
  {
    pose proof (Real_P3 α) as H5.
    pose proof (Real_P3 β) as H6.

    assert (∃ a : ℚ, a ∉ alpha α) as [a H7].
    {
      apply NNPP.
      intros H7.
      apply H5.
      apply Extensionality_Ensembles.
      split.
      - intros x H8.
        apply Full_intro.
      - intros x H8.
        apply NNPP.
        intros H9.
        apply H7.
        exists x.
        exact H9.
    }

    assert (∃ b : ℚ, b ∉ alpha β) as [b H8].
    {
      apply NNPP.
      intros H8.
      apply H6.
      apply Extensionality_Ensembles.
      split.
      - intros x H9.
        apply Full_intro.
      - intros x H9.
        apply NNPP.
        intros H10.
        apply H8.
        exists x.
        exact H10.
    }

    set (A := (a * a + 1)%Q).
    set (B := (b * b + 1)%Q).

    intros H9.

    assert ((A * B)%Q ∈ S) as H10.
    {
      rewrite H9.
      apply Full_intro.
    }

    unfold S, Rmult_set_pos in H10.
    destruct H10 as [H10 | H10].
    - unfold A, B in H10.
      nra.
    - destruct H10 as
        [x [y [H11 [H12 [H13 [H14 H15]]]]]].

      assert (H16 : (x < a)%Q).
      {
        destruct (Q_dec x a) as [[H16 | H16] | H16].
        - exact H16.
        - exfalso.
          apply H7.
          apply (Real_P1 α x a H11 H16).
        - exfalso.
          pose proof (Real_P4 α x H11) as [r [H17 H18]].
          apply H7.
          apply (Real_P1 α r a H17).
          setoid_rewrite <- H16.
          exact H18.
      }

      assert (H17 : (y < b)%Q).
      {
        destruct (Q_dec y b) as [[H17 | H17] | H17].
        - exact H17.
        - exfalso.
          apply H8.
          apply (Real_P1 β y b H12 H17).
        - exfalso.
          pose proof (Real_P4 β y H12) as [r [H18 H19]].
          apply H8.
          apply (Real_P1 β r b H18).
          setoid_rewrite <- H17.
          exact H19.
      }

      unfold A, B in H15.
      assert (H18 : (x < a * a + 1)%Q) by nra.
      assert (H19 : (y < b * b + 1)%Q) by nra.
      nra.
  }

  assert (
    H4 :
      ∀ x : ℚ,
        x ∈ S ->
        ∃ y : ℚ, y ∈ S /\ (x < y)%Q
  ).
  {
    intros x H5.
    unfold S, Rmult_set_pos in *.
    destruct H5 as [H5 | H5].
    - destruct (
        excluded_middle_informative
          (∃ a b : ℚ,
            a ∈ alpha α /\
            b ∈ alpha β /\
            (0 < a)%Q /\
            (0 < b)%Q)
      ) as [H6 | H6].
      + destruct H6 as [a [b [H7 [H8 [H9 H10]]]]].
        exists ((x + a * b) * (1#2))%Q.
        split.
        * right.
          exists a, b.
          repeat split; auto.
          nra.
        * nra.
      + exists (x * (1#2))%Q.
        split.
        * left.
          lra.
        * lra.

    - destruct H5 as [a [b [H6 [H7 [H8 [H9 H10]]]]]].
      exists ((x + a * b) * (1#2))%Q.
      split.
      + right.
        exists a, b.
        repeat split; auto.
        nra.
      + nra.
  }

  exists {|
    alpha := S;
    Real_P1 := H1;
    Real_P2 := H2;
    Real_P3 := H3;
    Real_P4 := H4
  |}.
  reflexivity.
Qed.

Definition Rmult_pos (α β : Real) : Real :=
  proj1_sig (constructive_indefinite_description _ (theorem_29_11 α β)).

Definition Rmult (α β : Real) : Real :=
  match Rle_dec 0 α, Rle_dec 0 β with
  | left _, left _ => Rmult_pos α β
  | left _, right _ => - (Rmult_pos α (Rabs β))
  | right _, left _ => - (Rmult_pos (Rabs α) β)
  | right _, right _ => Rmult_pos (Rabs α) (Rabs β)
  end.

Infix "*" := Rmult : Real_scope.

Theorem theorem_29_12 : ∀ α β : Real,
  α * β = β * α.
Proof.
Admitted.

Theorem theorem_29_13 : ∀ α β γ : Real,
  α * (β * γ) = (α * β) * γ.
Proof.
Admitted.

Definition Rone_set : Ensemble ℚ :=
  λ x, (x < 1)%Q.

Theorem theorem_29_15 : 
  ∃ α : Real, α.(alpha) = Rone_set.
Proof.
Admitted.

Definition Rone : Real := 
  proj1_sig (constructive_indefinite_description _ (theorem_29_15)).

Notation "1" := (Rone) : Real_scope.

Lemma theorem_29_14 : ∀ α : Real,
  α * 1 = α.
Proof.
Admitted.

Definition Rinv_set_pos (α : Real) : Ensemble ℚ :=
  fun z => (z < 0)%Q \/ (α > 0 /\ ∃ r : ℚ, (r > 0)%Q /\ r ∉ α.(alpha) /\ (z < / r)%Q).

Theorem theorem_29_16 : ∀ α : Real,
  ∃ γ : Real, γ.(alpha) = Rinv_set_pos α.
Proof.
Admitted.

Definition Rinv_pos (α : Real) : Real :=
  proj1_sig (constructive_indefinite_description _ (theorem_29_16 α)).

Definition Rinv (α : Real) : Real :=
  match Rtotal_order_dec α 0 with
  | inleft (left _) => - (Rinv_pos (-α))
  | inleft (right _) => 0  
  | inright _ => Rinv_pos α
  end.

Notation "/ α" := (Rinv α) : Real_scope.

Definition Rdiv (α β : Real) : Real :=
  α * (/ β).

Infix "/" := Rdiv : Real_scope.

Theorem theorem_29_17 : ∀ α : Real,
  α ≠ 0 -> α * (/ α) = 1.
Proof.
Admitted.

Theorem theorem_29_18 : ∀ α β γ : Real,
  α * (β + γ) = (α * β) + (α * γ).
Proof.
Admitted.

Lemma Rone_neq_Rzero : Rone <> Rzero.
Proof.
Admitted.

Lemma theorem_29_13_sym : ∀ α β γ : Real,
  (α * β) * γ = α * (β * γ).
Proof.
  intros. symmetry. apply theorem_29_13.
Qed.

Instance Field_Real : Field Real.
Proof.
  apply (Build_Field Real Rplus Rmult Rzero Rone Ropp Rinv).
  - exact theorem_29_3.
  - exact theorem_29_6.
  - exact theorem_29_8.
  - exact theorem_29_4.
  - intros a b c. rewrite theorem_29_13 . reflexivity.
  - exact Rone_neq_Rzero.
  - exact theorem_29_14.
  - exact theorem_29_17.
  - exact theorem_29_12.
  - exact theorem_29_18.
Defined.

Theorem theorem_29_19 : ∀ α β : Real,
  α ∈ P -> β ∈ P -> (α * β) ∈ P.
Proof.
Admitted.

Instance OrderedField_Real : OrderedField Real.
Proof.
  apply (Build_OrderedField Real Field_Real P).
  - exact theorem_29_9.
  - exact lemma_29_2.
  - exact theorem_29_19.
Defined.

Theorem theorem_29_20 : ∀ A : Ensemble Real,
  (∃ a, a ∈ A) -> Field.bounded_above A -> ∃ x, Field.is_least_upper_bound A x.
Proof.
Admitted.

Instance CompleteOrderedField_Real : CompleteOrderedField Real.
Proof.
  apply (Build_CompleteOrderedField Real Field_Real OrderedField_Real).
  - exact theorem_29_20.
Defined.

From Stdlib Require Import Ring Field Lra Zify ZifyClasses.

Lemma Real_plus_0_l : ∀ α : Real, 0 + α = α.
Proof.
  intros α. rewrite theorem_29_4. apply theorem_29_6.
Qed.

Lemma Real_mult_1_l : ∀ α : Real, 1 * α = α.
Proof.
  intros α. rewrite theorem_29_12. apply theorem_29_14.
Qed.

Lemma Real_plus_assoc_sym : ∀ α β γ : Real, α + (β + γ) = (α + β) + γ.
Proof.
  intros α β γ. symmetry. apply theorem_29_3.
Qed.

Lemma Real_mult_assoc_sym : ∀ α β γ : Real, α * (β * γ) = (α * β) * γ.
Proof.
  intros α β γ. apply theorem_29_13.
Qed.

Lemma Real_distr_r : ∀ α β γ : Real, (α + β) * γ = (α * γ) + (β * γ).
Proof.
  intros α β γ. rewrite theorem_29_12. rewrite theorem_29_18. f_equal; apply theorem_29_12.
Qed.

Lemma Real_sub_def : ∀ α β : Real, α - β = α + - β.
Proof.
  intros α β. reflexivity.
Qed.

Lemma Real_opp_def : ∀ α : Real, α + - α = 0.
Proof.
  intros α. apply theorem_29_8.
Qed.

Lemma Real_ring_theory : ring_theory 0 1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  - exact Real_plus_0_l.
  - exact theorem_29_4.
  - exact Real_plus_assoc_sym.
  - exact Real_mult_1_l.
  - exact theorem_29_12.
  - exact Real_mult_assoc_sym.
  - exact Real_distr_r.
  - exact Real_sub_def.
  - exact Real_opp_def.
Qed.

Add Ring Real_ring : Real_ring_theory.

Lemma Real_div_def : ∀ α β : Real, α / β = α * / β.
Proof.
  intros α β. reflexivity.
Qed.

Lemma Real_inv_l : ∀ α : Real, α <> 0 -> / α * α = 1.
Proof.
  intros α H1. rewrite theorem_29_12. apply theorem_29_17. exact H1.
Qed.

Lemma Real_field_theory : field_theory 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof.
  constructor.
  - exact Real_ring_theory.
  - exact Rone_neq_Rzero.
  - exact Real_div_def.
  - exact Real_inv_l.
Qed.

Add Field Real_field : Real_field_theory.