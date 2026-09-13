From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_app1_3_a :
  ∀ theta T, rotates theta T -> ∀ v w, dot (T v) (T w)=dot v w.
Abort.

Lemma lemma_4_app1_3_b_unit :
  ∀ theta, dot (pair 1 0) (pair (cos theta) (sin theta))=cos theta.
Abort.

Lemma lemma_4_app1_3_b :
  ∀ v w theta, v<>pair 0 0 -> w<>pair 0 0 ->
    angle_between v w theta -> dot v w=norm v*norm w*cos theta.
Abort.
