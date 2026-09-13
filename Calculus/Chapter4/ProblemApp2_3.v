From Calculus.Chapter4 Require Import Prelude.

(* Figure 9(a),(b): Dandelin spheres and their tangency points supply
   the foci. A plane avoiding the vertex cuts a nondegenerate ellipse when
   its slope is less than the cone's, and a hyperbola when greater.
   "Just one half" alone is insufficient: a parabola also meets only one
   nappe. The strict conditions below exclude that case. See REVIEW.md. *)
Local Definition tangent_cone_sphere (n : space) (d C h : ℝ) : Prop :=
  h<>0 /\ |(n · axis_center h)%V-d| = |h|/√(1+C^2).

Lemma lemma_4_app2_3_ellipse :
  ∀ n : space, ∀ d C : ℝ,
    vector_norm n=1 -> 0<C -> d<>0 ->
    coord n 0 ^ 2+coord n 1 ^ 2 < C^2*coord n 2 ^ 2 ->
    ∃ h1 h2 K : ℝ,
      h1<>h2 /\ 0<h1*h2 /\
      tangent_cone_sphere n d C h1 /\ tangent_cone_sphere n d C h2 /\
      let F1 := plane_foot n d (axis_center h1) in
      let F2 := plane_foot n d (axis_center h2) in
      distance3 F1 F2<K /\
      ∀ z, z ∈ plane3 n d ->
        (z ∈ cone3 C <-> distance3 z F1+distance3 z F2=K).
Abort.

Lemma lemma_4_app2_3_hyperbola :
  ∀ n : space, ∀ d C : ℝ,
    vector_norm n=1 -> 0<C -> d<>0 ->
    C^2*coord n 2 ^ 2 < coord n 0 ^ 2+coord n 1 ^ 2 ->
    ∃ h1 h2 K : ℝ,
      h1*h2<0 /\
      tangent_cone_sphere n d C h1 /\ tangent_cone_sphere n d C h2 /\
      let F1 := plane_foot n d (axis_center h1) in
      let F2 := plane_foot n d (axis_center h2) in
      0<K<distance3 F1 F2 /\
      ∀ z, z ∈ plane3 n d ->
        (z ∈ cone3 C <-> |distance3 z F1-distance3 z F2|=K).
Abort.
