From Lib Require Import Imports FunctionalMatrix.

Import VectorNotations MatrixNotations FunctionalMatrixNotations.

Local Open Scope R_scope.
Local Open Scope V_Scope.
Local Open Scope M_Scope.

Theorem theorem_2_6_1 {T m n} (A : matrix T m n) :
  ((A^T)^T = A).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite !matrix_to_function_transpose.
  rewrite fmatrix_transpose_involutive.
  reflexivity.
Qed.

Theorem theorem_2_6_2 {T m n} `{Add T} (A B : matrix T m n) :
  (A + B)^T = A^T + B^T.
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_to_function_add.
  repeat rewrite matrix_to_function_transpose.
  rewrite matrix_to_function_add.
  unfold fmatrix_transpose, fmatrix_add.
  reflexivity.
Qed.

Theorem theorem_2_6_3 {T m n} `{Scale T T}(c : T) (A : matrix T m n) :
  (c * A)^T = c * (A^T).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_to_function_scale.
  repeat rewrite matrix_to_function_transpose.
  rewrite matrix_to_function_scale.
  unfold fmatrix_transpose, fmatrix_scale.
  reflexivity.
Qed.

Theorem theorem_2_6_4 {m n p} (A : matrix R m n) (B : matrix R n p) :
  (A × B)^T = B^T × A^T.
Proof.
  apply matrix_ext. intros i j Hi Hj.
  rewrite matrix_transpose_nth, !matrix_mult_nth by lia.
  apply mat_sum_ext. intros k Hk.
  autorewrite with matrix_coords.
  ring.
Qed.

Theorem invertable_unique_inverse {n} (A : matrix R n n) :
  invertable A -> exists! B : matrix R n n, inverse A B.
Proof.
  intros [B [H1 H2]].
  exists B.
  repeat split.
  - exact H1.
  - exact H2.
  - intros C [H3 H4].
    replace B with (I × B) by auto_mat.
    replace C with (C × I) by auto_mat.
    rewrite <- H4 at 1.
    rewrite matrix_assoc, H1.
    reflexivity.
Qed.