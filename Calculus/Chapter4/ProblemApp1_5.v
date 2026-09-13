From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_app1_5_a :
  ∀ a w, 0<a ->
    (0<snd w -> det (pair a 0) w=parallelogram_area (pair a 0) w) /\
    (snd w<0 -> det (pair a 0) w= -parallelogram_area (pair a 0) w).
Abort.

Lemma lemma_4_app1_5_b_rotation :
  ∀ theta T, rotates theta T -> ∀ v w, det (T v) (T w)=det v w.
Abort.

Lemma lemma_4_app1_5_b_area :
  ∀ v w : point, parallelogram_area v w=|det v w|.
Abort.

Lemma lemma_4_app1_5_b_orientation :
  ∀ v w theta, v<>pair 0 0 -> w<>pair 0 0 ->
    angle_between v w theta ->
    (0<theta<π -> det v w=parallelogram_area v w) /\
    (-π<theta<0 -> det v w= -parallelogram_area v w).
Abort.
