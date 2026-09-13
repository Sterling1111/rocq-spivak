From Calculus.Chapter4 Require Import Prelude.

(* Appendix 2, pp. 82-83: use orthonormal coordinates WITHIN the
   intersecting plane. C is a positive cylinder radius. Include vertical
   planes, whose sections may be two lines, one line, or empty. *)
Lemma lemma_4_app2_1_equation :
  ∀ n : space, ∀ d C : ℝ,
    vector_norm n=1 -> 0<C ->
    ∃ o u v alpha beta, plane_frame n d o u v /\
      ∀ x y, (plane_chart o u v x y ∈ cylinder3 C <->
                   (alpha*x+beta)^2+y^2=C^2).
Abort.

Lemma lemma_4_app2_1_possibilities :
  ∀ alpha beta C : ℝ, 0<C ->
    let S := locus (λ x y, (alpha*x+beta)^2+y^2=C^2) in
    (alpha<>0 -> ellipse S) /\
    (alpha=0 -> beta^2<C^2 ->
      S = (graph (λ _, √(C^2-beta^2))) ⋃
          (graph (λ _, -√(C^2-beta^2)))) /\
    (alpha=0 -> beta^2=C^2 -> S=graph (λ _, 0)) /\
    (alpha=0 -> C^2<beta^2 -> S=∅).
Abort.

Lemma lemma_4_app2_1_circle :
  ∀ alpha beta C : ℝ, 0<C ->
    (circle (locus (λ x y, (alpha*x+beta)^2+y^2=C^2)) <-> alpha^2=1).
Abort.
