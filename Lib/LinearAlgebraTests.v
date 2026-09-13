From Lib Require Import Imports Vector Matrix.
Import VectorNotations MatrixNotations.

(** Local definitions must reduce without manual unfolding or symbolic search. *)
Section ConcreteMatrixComputation.
  Local Open Scope R_scope.
  Local Open Scope V_Scope.
  Local Open Scope M_Scope.
  Let A : matrix R 2 3 := ⟨⟨1, 2, 3⟩, ⟨4, 5, 6⟩⟩.
  Let B : matrix R 3 2 := ⟨⟨7, 8⟩, ⟨9, 1⟩, ⟨2, 3⟩⟩.

  Example matrix_product_compute : A × B = ⟨⟨31, 19⟩, ⟨85, 55⟩⟩.
  Proof. vec_compute. Qed.

  Example matrix_product_auto : A × B = ⟨⟨31, 19⟩, ⟨85, 55⟩⟩.
  Proof. auto_mat. Qed.

  Example matrix_transpose_compute : A^T = ⟨⟨1, 4⟩, ⟨2, 5⟩, ⟨3, 6⟩⟩.
  Proof. vec_compute. Qed.

  Example symbolic_entries_compute (a b : R) :
    ⟨⟨a, b⟩⟩ × ⟨⟨b⟩, ⟨a⟩⟩ = ⟨⟨(2 * a * b)%R⟩⟩.
  Proof. vec_compute. Qed.
End ConcreteMatrixComputation.

(** Decimal coefficients are exact rationals, including in symbolic entries. *)
Section DecimalComputation.
  Local Open Scope R_scope.
  Local Open Scope V_Scope.
  Local Open Scope M_Scope.
  Let Md1 : matrix R 2 2 := ⟨⟨1.5, 2.0⟩, ⟨0.5, 3.5⟩⟩.
  Let Md2 : matrix R 2 2 := ⟨⟨4.0, 1.2⟩, ⟨2.0, 0.0⟩⟩.

  Example decimal_product_compute : Md1 × Md2 = ⟨⟨10.0, 1.8⟩, ⟨9.0, 0.6⟩⟩.
  Proof. vec_compute. Qed.

  Example decimal_product_auto : Md1 × Md2 = ⟨⟨10.0, 1.8⟩, ⟨9.0, 0.6⟩⟩.
  Proof. auto_mat. Qed.

  Example decimal_symbolic_product (a b : R) :
    ⟨⟨a, b⟩⟩ × ⟨⟨0.5⟩, ⟨1.25⟩⟩ = ⟨⟨((2*a + 5*b) / 4)%R⟩⟩.
  Proof. vec_compute. Qed.

  Example signed_decimal_and_fraction :
    ⟨(-1.25)%R, 0.1, (1/3)%R⟩ + ⟨0.5, 0.2, (1/6)%R⟩ = ⟨(-0.75)%R, 0.3, 0.5⟩.
  Proof. vec_compute. Qed.

  Fail Definition reject_wrong_decimal : ⟨(0.1 + 0.2)%R⟩ = ⟨0.4⟩ := ltac:(vec_compute).
  Fail Definition reject_zero_denominator : ⟨(1/0)%R⟩ = ⟨1%R⟩ := ltac:(vec_compute).
  Fail Definition reject_unproved_denominator (a b : R) :
    ⟨(a*b/b)%R⟩ = ⟨a⟩ := ltac:(vec_compute).
End DecimalComputation.

(** These tests intentionally precede the functional imports: the original
    Vector/Matrix entry points must work on their own. *)
Section ListVectorTests.
  Local Open Scope R_scope.
  Local Open Scope V_Scope.
  Variables (n : nat) (u v w : vector R n) (a b : R).

  Example vector_comm_solver : u + v = v + u.
  Proof. auto_vec. Qed.

  Example vector_polynomial_solver :
    (a + b)%R * (u + v) = a * u + b * v + b * u + a * v.
  Proof. solve_vec. Qed.

  Example vector_hadamard_solver : (u + v) ⊙ w = w ⊙ u + v ⊙ w.
  Proof. auto_vec. Qed.

  Example vector_dot_solver :
    (a * u + b * v) · (u + w) =
      (a * (u · u) + b * (w · v) + a * (w · u) + b * (u · v))%R.
  Proof. auto_vec. Qed.

  Example vector_norm_solver : ∥ (-1)%R * v ∥ = ∥ v ∥.
  Proof. auto_vec. Qed.

  Example vector_map_solver (f g : R -> R) :
    vector_map f (vector_map g v) = vector_map (fun x => f (g x)) v.
  Proof. auto_vec. Qed.

  Example vector_scalar_hypothesis (H : a = b) : a * v = b * v.
  Proof. auto_vec. Qed.
  
  Example vector_coordinate_hypothesis
      (H : forall i, (i < n)%nat -> vector_coord u i = vector_coord v i) : u = v.
  Proof. auto_vec. Qed.
  Example vector_fraction_solver (H : b <> 0%R) :
    ⟨(a * b / b)%R, (b / b)%R⟩ = ⟨a, 1%R⟩.
  Proof. auto_vec. Qed.
  Example vector_symbolic_literal :
    ⟨a + b, a * b⟩ + ⟨a - b, b * a⟩ = ⟨2 * a, 2 * a * b⟩.
  Proof. auto_vec. Qed.
End ListVectorTests.

Example nat_vector_solver n (u v : vector nat n) : (u + v = v + u)%V.
Proof. auto_vec. Qed.
Example empty_generic_vector (u v : vector Datatypes.Empty_set 0) : u = v.
Proof. auto_vec. Qed.
Example empty_vector_dot (u v : vector R 0) : vector_dot u v = 0%R.
Proof. auto_vec. Qed.

Example vector_solver_rollback n (u v : vector R n) (H : exists _ : u = v, True) : u = v.
Proof. Fail auto_vec. destruct H as [H _]. exact H. Qed.

Section ListMatrixTests.
  Local Open Scope R_scope.
  Local Open Scope M_Scope.
  Variables (m n p q : nat) (A B : matrix R m n) (C D : matrix R n p) (E : matrix R p q).
  Variables (a b : R).

  Example matrix_comm_solver : A + B = B + A.
  Proof. auto_mat. Qed.
  Example matrix_distributive_solver :
    (A + B) × (C + D) = (B × D + A × C) + (B × C + A × D).
  Proof. auto_mat. Qed.
  Example matrix_associative_solver : ((A × C) × E) + A × (D × E) = A × ((C + D) × E).
  Proof. auto_mat. Qed.
  Example matrix_scale_solver :
    (a * A + b * B) × C = a * (A × C) + b * (B × C).
  Proof. auto_mat. Qed.
  Example matrix_transpose_solver : ((A + B) × (C + D))^T =
    D^T × B^T + C^T × A^T + C^T × B^T + D^T × A^T.
  Proof. auto_mat. Qed.
  Example matrix_identity_solver : I × A × I + 0 = A.
  Proof. auto_mat. Qed.
  Example matrix_zero_solver : A × (0 : matrix R n p) + (0 : matrix R m n) × C = 0.
  Proof. auto_mat. Qed.
  Example matrix_transpose_twice_solver : (A^T)^T = A.
  Proof. auto_mat. Qed.
  Example matrix_hadamard_solver : (A + B) ⊙ A = A ⊙ A + A ⊙ B.
  Proof. auto_mat. Qed.
  Example matrix_coordinate_hypothesis
      (H : forall i j, (i < m)%nat -> (j < n)%nat -> mat_nth A i j = mat_nth B i j) : A = B.
  Proof. auto_mat. Qed.
End ListMatrixTests.

Example nat_matrix_solver m n (A B : matrix nat m n) : (A + B = B + A)%M.
Proof. auto_mat. Qed.

Example nat_matrix_transpose m n (A B : matrix nat m n) :
  ((A + B)^T = B^T + A^T)%M.
Proof. auto_mat. Qed.

Example empty_matrix_product m p (A : matrix R m 0) (B : matrix R 0 p) :
  (A × B = 0)%M.
Proof. auto_mat. Qed.

Example matrix_solver_rollback m n (A B : matrix R m n) (H : exists _ : A = B, True) : A = B.
Proof. Fail auto_mat. destruct H as [H _]. exact H. Qed.

Local Open Scope V_Scope.

Example rectangular_literal_solver (a b : R) :
  (⟨⟨a, b⟩, ⟨b, a⟩, ⟨a, a⟩⟩ × ⟨⟨1%R⟩, ⟨2%R⟩⟩)%M =
  ⟨⟨(a + 2*b)%R⟩, ⟨(b + 2*a)%R⟩, ⟨(3*a)%R⟩⟩%V.
Proof. auto_mat. Qed.

(** False equalities must fail, including symbolic goals that used to cycle
    between vector equality and equality of their underlying lists. *)
Fail Definition reject_arbitrary_vectors n (v w : vector R n) : v = w := ltac:(auto_vec).
Fail Definition reject_false_vector : (⟨1%R⟩ = ⟨2%R⟩)%V := ltac:(auto_vec).
Fail Definition reject_matrix_commutation n (A B : matrix R n n) :
  (A × B = B × A)%M := ltac:(auto_mat).

From Lib Require Import FunctionalMatrix.
Import FunctionalVectorNotations FunctionalMatrixNotations.

(** Transpose is structural: even an uninhabited element type needs no Zero. *)
Example transpose_without_zero {A m n} (M : matrix A m n) : ((M^T)^T = M)%M.
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite !matrix_to_function_transpose. reflexivity.
Qed.

Example transpose_without_zero_solver {A m n} (M : matrix A m n) : ((M^T)^T = M)%M.
Proof. auto_mat. Qed.

Example boolean_transpose :
  ((⟨⟨true, false, true⟩, ⟨false, true, false⟩⟩%V : matrix bool 2 3)^T)%M =
  ⟨⟨true, false⟩, ⟨false, true⟩, ⟨true, false⟩⟩%V.
Proof. vec_compute. Qed.

Example transpose_empty_type_no_rows :
  ((⟨⟩%V : matrix Datatypes.Empty_set 0 2)^T)%M =
  (⟨⟨⟩, ⟨⟩⟩%V : matrix Datatypes.Empty_set 2 0).
Proof. vec_compute. Qed.

Example transpose_empty_type_no_columns :
  ((⟨⟨⟩, ⟨⟩⟩%V : matrix Datatypes.Empty_set 2 0)^T)%M =
  (⟨⟩%V : matrix Datatypes.Empty_set 0 2).
Proof. vec_compute. Qed.

Example transpose_empty_type_zero_by_zero :
  ((⟨⟩%V : matrix Datatypes.Empty_set 0 0)^T)%M =
  (⟨⟩%V : matrix Datatypes.Empty_set 0 0).
Proof. vec_compute. Qed.

Example transpose_bridge_without_zero {A m n} (M : fmatrix A m n) :
  function_to_matrix (fmatrix_transpose M) = matrix_transpose (function_to_matrix M).
Proof. apply function_to_matrix_transpose. Qed.

Section FunctionalTests.
  Variables (m n p : nat) (u v w : fvector R n).
  Variables (A B : fmatrix R m n) (C : fmatrix R n p) (a b : R).

  Example functional_vector_solver : (a * (u + v) = a * v + a * u)%FV.
  Proof. auto_vec. Qed.
  Example functional_dot_solver :
    ((a * u + b * v) · w)%FV = (a * (w · u)%FV + b * (w · v)%FV)%R.
  Proof. auto_vec. Qed.
  Example functional_norm_solver : (∥ (-1)%R * v ∥ = ∥ v ∥)%FV.
  Proof. auto_vec. Qed.
  Example functional_matrix_solver : ((a * A + b * B) × C = b * (B × C) + a * (A × C))%FM.
  Proof. auto_mat. Qed.
  Example functional_transpose_solver : ((A × C)^T = C^T × A^T)%FM.
  Proof. auto_mat. Qed.
  Example functional_identity_solver : (I × A × I = A)%FM.
  Proof. auto_mat. Qed.
  Example converted_vector_solver :
    function_to_vector (a * (u + v))%FV = (a * function_to_vector v + a * function_to_vector u)%V.
  Proof. auto_vec. Qed.
  Example converted_matrix_solver :
    function_to_matrix ((A + B) × C)%FM =
    (function_to_matrix B × function_to_matrix C + function_to_matrix A × function_to_matrix C)%M.
  Proof. auto_mat. Qed.
End FunctionalTests.

Example generic_functional_transpose A m n (M : fmatrix A m n) :
  fmatrix_transpose (fmatrix_transpose M) = M.
Proof. auto_mat. Qed.

Fail Definition reject_functional_vectors n (v w : fvector R n) : v = w := ltac:(auto_vec).
Fail Definition reject_functional_commutation n (A B : fmatrix R n n) :
  (A × B = B × A)%FM := ltac:(auto_mat).
