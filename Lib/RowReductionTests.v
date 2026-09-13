From Lib Require Import Imports RowReduction.
Import VectorNotations MatrixNotations.
Local Open Scope Qc_scope.
Local Open Scope V_Scope.
Local Open Scope M_Scope.

Definition fractional_example : matrix Qc 2 3 :=
  ⟨⟨2, 1, 3⟩, ⟨0, 3, 1⟩⟩.

Example fractional_ref : matrix_ref fractional_example =
  ⟨⟨1, 1/2, 3/2⟩, ⟨0, 1, 1/3⟩⟩.
Proof. qc_mat_compute. Qed.

Example fractional_rref : matrix_rref fractional_example =
  ⟨⟨1, 0, 4/3⟩, ⟨0, 1, 1/3⟩⟩.
Proof. qc_mat_compute. Qed.

Definition swap_example : matrix Qc 2 3 := ⟨⟨0, 2, 4⟩, ⟨1, 3, 5⟩⟩.
Example swap_ref : matrix_ref swap_example = ⟨⟨1, 3, 5⟩, ⟨0, 1, 2⟩⟩.
Proof. qc_mat_compute. Qed.
Example swap_rref : matrix_rref swap_example = ⟨⟨1, 0, -1⟩, ⟨0, 1, 2⟩⟩.
Proof. qc_mat_compute. Qed.

Example dependent_rows :
  matrix_rref (⟨⟨1, 2, 3⟩, ⟨2, 4, 6⟩, ⟨0, 0, 0⟩⟩ : matrix Qc 3 3) =
  ⟨⟨1, 2, 3⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩.
Proof. qc_mat_compute. Qed.

Definition skipped_columns : matrix Qc 3 4 :=
  ⟨⟨0, 1, 2, 3⟩, ⟨0, 2, 4, 7⟩, ⟨0, 0, 0, 0⟩⟩.
Example skipped_columns_rref : matrix_rref skipped_columns =
  ⟨⟨0, 1, 2, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩.
Proof. qc_mat_compute. Qed.
Example skipped_columns_pivots : matrix_pivots skipped_columns = [1%nat; 3%nat].
Proof. vm_compute. reflexivity. Qed.

Example tall_matrix :
  matrix_rref (⟨⟨1, 2⟩, ⟨0, 1⟩, ⟨3, 4⟩⟩ : matrix Qc 3 2) =
  ⟨⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩.
Proof. qc_mat_compute. Qed.

Example rational_input :
  matrix_rref (⟨⟨1/2, 1/3, 1⟩, ⟨0, 2/5, 3/7⟩⟩ : matrix Qc 2 3) =
  ⟨⟨1, 0, 9/7⟩, ⟨0, 1, 15/14⟩⟩.
Proof. qc_mat_compute. Qed.

Example negative_pivot :
  matrix_rref (⟨⟨-2, 4⟩⟩ : matrix Qc 1 2) = ⟨⟨1, -2⟩⟩.
Proof. qc_mat_compute. Qed.

Example zero_matrix :
  matrix_rref (⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩ : matrix Qc 2 3) =
  ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩.
Proof. qc_mat_compute. Qed.
Example zero_rows : matrix_rref (⟨⟩ : matrix Qc 0 3) = ⟨⟩.
Proof. qc_mat_compute. Qed.
Example zero_columns : matrix_rref (⟨⟨⟩, ⟨⟩⟩ : matrix Qc 2 0) = ⟨⟨⟩, ⟨⟩⟩.
Proof. qc_mat_compute. Qed.
Example zero_by_zero : matrix_rref (⟨⟩ : matrix Qc 0 0) = ⟨⟩.
Proof. qc_mat_compute. Qed.

Example rref_idempotent_example :
  matrix_rref (matrix_rref skipped_columns) = matrix_rref skipped_columns.
Proof. qc_mat_compute. Qed.

(** The same computation certifies a result over the ordinary real numbers. *)
Example fractional_real_rref :
  is_rref (matrix_Qc_to_R (⟨⟨1, 0, 4/3⟩, ⟨0, 1, 1/3⟩⟩ : matrix Qc 2 3)).
Proof.
  rewrite <- fractional_rref. exact (proj2 (matrix_rref_real_correct fractional_example)).
Qed.

Example fractional_real_equivalence :
  row_equivalent (matrix_Qc_to_R fractional_example)
    (matrix_Qc_to_R (⟨⟨1, 0, 4/3⟩, ⟨0, 1, 1/3⟩⟩ : matrix Qc 2 3)).
Proof.
  rewrite <- fractional_rref. exact (proj1 (matrix_rref_real_correct fractional_example)).
Qed.

(** Negative checks also ensure the computation tactic restores a failed goal. *)
Goal matrix_rref fractional_example = ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩⟩.
  Fail qc_mat_compute.
Abort.

Example wrong_result_rejected :
  matrix_rref fractional_example <> ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩⟩.
Proof.
  intro Heq.
  assert (Hfalse : matrix_Qc_eqb (matrix_rref fractional_example)
    ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩⟩ = false) by (vm_compute; reflexivity).
  apply (proj2 (matrix_Qc_eqb_eq _ _)) in Heq. congruence.
Qed.

Example exact_decimals :
  matrix_rref (⟨⟨1.5, 2.0⟩, ⟨0.5, 3.5⟩⟩ : matrix Qc 2 2) =
  ⟨⟨1, 0⟩, ⟨0, 1⟩⟩.
Proof. qc_mat_compute. Qed.

Example four_pivots :
  matrix_rref (⟨⟨2, 1, 0, 0, 1⟩, ⟨1, 2, 1, 0, 0⟩,
                ⟨0, 1, 2, 1, 0⟩, ⟨0, 0, 1, 2, 0⟩⟩ : matrix Qc 4 5) =
  ⟨⟨1, 0, 0, 0, 4/5⟩, ⟨0, 1, 0, 0, -3/5⟩,
    ⟨0, 0, 1, 0, 2/5⟩, ⟨0, 0, 0, 1, -1/5⟩⟩.
Proof. qc_mat_compute. Qed.

Example zero_rows_move_to_bottom :
  matrix_rref (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 3⟩⟩ : matrix Qc 3 2) =
  ⟨⟨1, 1.5⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩.
Proof. qc_mat_compute. Qed.

(** Regression: overloaded zero and one must not be assigned other entries
    while unifying the dimensions of different rows. *)
Example rational_literal_values : matrix_Qc_entries fractional_example =
  [[2%Q; 1%Q; 3%Q]; [0%Q; 3%Q; 1%Q]].
Proof. vm_compute. reflexivity. Qed.

Example display_fractional_result : matrix_Qc_entries (matrix_rref fractional_example) =
  [[1%Q; 0%Q; (4#3)%Q]; [0%Q; 1%Q; (1#3)%Q]].
Proof. vm_compute. reflexivity. Qed.

Section RealLiteralRegression.
Local Open Scope R_scope.
Local Open Scope V_Scope.
Local Open Scope M_Scope.
Example real_literal_values :
  (⟨⟨2, 1, 3⟩, ⟨0, 3, 1⟩⟩ : matrix R 2 3) =
  ⟨⟨2%R, 1%R, 3%R⟩, ⟨0%R, 3%R, 1%R⟩⟩.
Proof. reflexivity. Qed.
End RealLiteralRegression.

(** A larger example exercises cached intermediate rows. *)
Example eight_pivots :
  matrix_rref (⟨⟨20, -1, 0, 1, 2, -2, -1, 0, 13⟩,
   ⟨-1, 20, 1, 2, -2, -1, 0, 1, 42⟩,
   ⟨0, 1, 20, -2, -1, 0, 1, 2, 72⟩,
   ⟨1, 2, -2, 20, 0, 1, 2, -2, 83⟩,
   ⟨2, -2, -1, 0, 20, 2, -2, -1, 85⟩,
   ⟨-2, -1, 0, 1, 2, 20, -1, 0, 123⟩,
   ⟨-1, 0, 1, 2, -2, -1, 20, 1, 142⟩,
   ⟨0, 1, 2, -2, -1, 0, 1, 20, 162⟩⟩ : matrix Qc 8 9) =
  ⟨⟨1, 0, 0, 0, 0, 0, 0, 0, 1⟩,
   ⟨0, 1, 0, 0, 0, 0, 0, 0, 2⟩,
   ⟨0, 0, 1, 0, 0, 0, 0, 0, 3⟩,
   ⟨0, 0, 0, 1, 0, 0, 0, 0, 4⟩,
   ⟨0, 0, 0, 0, 1, 0, 0, 0, 5⟩,
   ⟨0, 0, 0, 0, 0, 1, 0, 0, 6⟩,
   ⟨0, 0, 0, 0, 0, 0, 1, 0, 7⟩,
   ⟨0, 0, 0, 0, 0, 0, 0, 1, 8⟩⟩.
Proof. qc_mat_compute. Qed.
