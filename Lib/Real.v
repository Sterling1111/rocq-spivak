Require Import Imports Notations Sets.
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
  λ x : ℚ, (-x)%Q ∉ α.(alpha) /\ ∃ y : ℚ, y ∉ α.(alpha) /\ (y < -x)%Q.