From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_app1_7 :
  ∀ v w theta, v<>pair 0 0 -> w<>pair 0 0 ->
    angle_between v w theta -> det v w=norm v*norm w*sin theta.
Abort.
