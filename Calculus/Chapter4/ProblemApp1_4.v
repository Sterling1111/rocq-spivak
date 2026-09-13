From Calculus.Chapter4 Require Import Prelude.

(* p. 79: the sole subpart is printed (a). Figure 9 assumes w2>0
   and a positive horizontal intercept. Those signs are essential for a
   positive area equal to det(v,w). The general area is |det(v,w)|. *)
Lemma lemma_4_app1_4_a_intercept :
  ∀ v w : point, snd w<>0 ->
    pair ((fst v*snd w-fst w*snd v)/snd w) 0 ∈ line_through v w.
Abort.

Lemma lemma_4_app1_4_a :
  ∀ v w : point, 0<snd w ->
    0<(fst v*snd w-fst w*snd v)/snd w ->
    parallelogram_area v w=det v w.
Abort.

Lemma lemma_4_app1_4_sign :
  ∀ v w : point, det w v = -det v w.
Abort.
