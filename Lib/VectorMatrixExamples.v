From Lib Require Import Imports FunctionalMatrix.
Import VectorNotations MatrixNotations FunctionalVectorNotations FunctionalMatrixNotations.

(** Concrete data and coordinate formulas can be used side by side. *)
Definition textbook_vector : vector nat 3 := ⟨1, 2, 3⟩%V.
Definition coordinate_vector : fvector nat 3 := fun i => S (proj1_sig (Fin.to_nat i)).

Example display_coordinate_vector : function_to_vector coordinate_vector = textbook_vector.
Proof. apply vector_eq. reflexivity. Qed.

Example read_coordinate : vector_to_function textbook_vector (Fin.FS Fin.F1) = 2.
Proof. reflexivity. Qed.

Lemma opaque_length : List.length [4; 5; 6] = 3.
Proof. reflexivity. Qed.

Example read_with_opaque_length :
  vector_to_function (mk_vector [4; 5; 6] opaque_length) (Fin.FS Fin.F1) = 5.
Proof. reflexivity. Qed.

Example read_tabulated_function : vector_to_function (function_to_vector coordinate_vector) Fin.F1 = 1.
Proof. reflexivity. Qed.

Example display_vector_sum :
  function_to_vector (coordinate_vector + coordinate_vector)%FV = ⟨2, 4, 6⟩%V.
Proof. apply vector_eq. reflexivity. Qed.

Example functional_dot : (coordinate_vector · coordinate_vector)%FV = 14.
Proof. reflexivity. Qed.

Definition textbook_matrix : matrix nat 2 3 := ⟨⟨1, 2, 3⟩, ⟨4, 5, 6⟩⟩%V.
Definition coordinate_matrix : fmatrix nat 2 3 :=
  fun i j => 3 * proj1_sig (Fin.to_nat i) + S (proj1_sig (Fin.to_nat j)).
Definition right_matrix : matrix nat 3 2 := ⟨⟨7, 8⟩, ⟨9, 1⟩, ⟨2, 3⟩⟩%V.

Example display_coordinate_matrix : function_to_matrix coordinate_matrix = textbook_matrix.
Proof. unfold coordinate_matrix, textbook_matrix, function_to_matrix. auto_vec. Qed.

Example rectangular_transpose :
  function_to_matrix (coordinate_matrix^T)%FM = ⟨⟨1, 4⟩, ⟨2, 5⟩, ⟨3, 6⟩⟩%V.
Proof. unfold function_to_matrix. auto_vec. Qed.

Example rectangular_product :
  function_to_matrix (coordinate_matrix × matrix_to_function right_matrix)%FM =
  ⟨⟨31, 19⟩, ⟨85, 55⟩⟩%V.
Proof. unfold function_to_matrix. auto_vec. Qed.

Example display_identity : function_to_matrix (I : fmatrix nat 2 2)%FM = (⟨⟨1%nat, 0%nat⟩, ⟨0%nat, 1%nat⟩⟩%V : matrix nat 2 2).
Proof. unfold function_to_matrix. auto_vec. Qed.

Example display_scaled_matrix :
  function_to_matrix (2 * coordinate_matrix)%FM = ⟨⟨2, 4, 6⟩, ⟨8, 10, 12⟩⟩%V.
Proof. unfold function_to_matrix. auto_vec. Qed.

Example display_hadamard_product :
  function_to_matrix (coordinate_matrix ⊙ coordinate_matrix)%FM = ⟨⟨1, 4, 9⟩, ⟨16, 25, 36⟩⟩%V.
Proof. unfold function_to_matrix. auto_vec. Qed.

(** A list theorem can be proved entirely through coordinates. *)
Example list_add_comm_via_functions {n} (v w : vector R n) : (v + w = w + v)%V.
Proof.
  apply vector_function_eq_iff. intros i.
  rewrite !vector_to_function_add, fvector_add_comm_R. reflexivity.
Qed.

Example list_matrix_add_comm_via_functions {m n} (M N : matrix R m n) : (M + N = N + M)%M.
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite !matrix_to_function_add. apply Rplus_comm.
Qed.

Example transfer_vector_order {n} (v w : vector R n) :
  (v <= w)%V <-> (vector_to_function v <= vector_to_function w)%FV.
Proof. apply vector_to_function_le. Qed.

Example transfer_matrix_order {m n} (M N : matrix R m n) :
  (M >= N)%V <-> (matrix_to_function M >= matrix_to_function N)%FM.
Proof. apply matrix_to_function_ge. Qed.

(** Empty dimensions preserve their shapes, even for an uninhabited element type. *)
Example empty_vector_roundtrip (v : vector Datatypes.Empty_set 0) :
  function_to_vector (vector_to_function v) = v.
Proof. apply function_vector_roundtrip. Qed.

Example no_rows_roundtrip (M : matrix Datatypes.Empty_set 0 3) :
  function_to_matrix (matrix_to_function M) = M.
Proof. apply function_matrix_roundtrip. Qed.

Example no_columns_roundtrip (M : matrix Datatypes.Empty_set 2 0) :
  function_to_matrix (matrix_to_function M) = M.
Proof. apply function_matrix_roundtrip. Qed.

Example transpose_no_rows :
  function_to_matrix (fmatrix_transpose (matrix_to_function (⟨⟩%V : matrix nat 0 3))) =
  (⟨⟨⟩, ⟨⟩, ⟨⟩⟩%V : matrix nat 3 0).
Proof. unfold function_to_matrix. auto_vec. Qed.

Example zero_inner_dimension :
  function_to_matrix ((0 : fmatrix nat 2 0) × (0 : fmatrix nat 0 3))%FM =
  ⟨⟨0%nat, 0%nat, 0%nat⟩, ⟨0%nat, 0%nat, 0%nat⟩⟩%V.
Proof. unfold function_to_matrix. auto_vec. Qed.

Example empty_dot : ((0 : fvector nat 0) · (0 : fvector nat 0))%FV = 0.
Proof. reflexivity. Qed.

(** Dimensions are checked before any calculation or proof. *)
Fail Definition invalid_coordinate := vector_to_function textbook_vector (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
Fail Definition invalid_product := fmatrix_mult coordinate_matrix coordinate_matrix.
