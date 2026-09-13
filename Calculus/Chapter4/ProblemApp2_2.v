From Calculus.Chapter4 Require Import Prelude.

(* Figure 8: a sphere of radius C centered at (0,0,h) has its
   equator on the cylinder. With unit n, |n·center-d|=C says it is tangent
   to the plane, and plane_foot is the point of tangency. *)
Lemma lemma_4_app2_2_a :
  ∀ n : space, ∀ d C h : ℝ, ∀ z : space,
    vector_norm n=1 -> 0<C ->
    |(n · axis_center h)%V-d|=C ->
    z ∈ plane3 n d -> z ∈ cylinder3 C ->
    distance3 z (plane_foot n d (axis_center h))=|coord z 2-h|.
Abort.

Lemma lemma_4_app2_2_b :
  ∀ n : space, ∀ d C h1 h2 : ℝ,
    vector_norm n=1 -> 0<C -> h1<h2 ->
    |(n · axis_center h1)%V-d|=C ->
    |(n · axis_center h2)%V-d|=C -> coord n 2<>0 ->
    let F1 := plane_foot n d (axis_center h1) in
    let F2 := plane_foot n d (axis_center h2) in
    distance3 F1 F2 < h2-h1 /\
    ∀ z, z ∈ plane3 n d ->
      (z ∈ cylinder3 C <-> distance3 z F1+distance3 z F2=h2-h1).
Abort.
