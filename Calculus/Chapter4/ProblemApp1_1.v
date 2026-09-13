From Calculus.Chapter4 Require Import Prelude.

(* Appendix 1, pp. 77-78. T is rotation by theta, as a map of rays.
   Do not assume linearity: that is exactly the assertion in (b). *)
Lemma lemma_4_app1_1_a :
  ∀ theta T, rotates theta T ->
    T (pair 1 0) = pair (cos theta) (sin theta) /\
    T (pair 0 1) = pair (-sin theta) (cos theta).
Abort.

Lemma lemma_4_app1_1_b :
  ∀ theta T, rotates theta T ->
    (∀ v w, T (point_add v w) = point_add (T v) (T w)) /\
    (∀ a w, T (point_scale a w) = point_scale a (T w)).
Abort.

Lemma lemma_4_app1_1_c :
  ∀ theta T, rotates theta T -> ∀ x y,
    T (pair x y) = pair (x*cos theta-y*sin theta) (x*sin theta+y*cos theta).
Abort.

Lemma lemma_4_app1_1_d :
  ∀ T, rotates (-π/4) T -> ∀ x y,
    T (pair x y) = pair (x/√2+y/√2) (-x/√2+y/√2) /\
    ((fst (T (pair x y))/√2)^2-(snd (T (pair x y))/√2)^2=1 <-> x*y=1).
Abort.
