From Calculus.Chapter4 Require Import Prelude.

(* The algebraic implication holds for arbitrary Lambda and epsilon.
   The nondegenerate classification needs Lambda<>0 and epsilon>=0;
   the PDF's unqualified "any" includes counterexamples. *)
Local Definition conic_equation (Lambda epsilon : ℝ) : Ensemble point :=
  locus (λ x y, (1-epsilon^2)*x^2+y^2=Lambda^2-2*Lambda*epsilon*x).

Lemma lemma_4_app3_7_equation :
  ∀ Lambda epsilon r theta : ℝ,
    1+epsilon*cos theta<>0 -> r=Lambda/(1+epsilon*cos theta) ->
    polar_point r theta ∈ conic_equation Lambda epsilon.
Abort.

Lemma lemma_4_app3_7_graph :
  ∀ Lambda epsilon : ℝ, Lambda<>0 ->
    polar_locus (λ r theta, 1+epsilon*cos theta<>0 /\
                                r=Lambda/(1+epsilon*cos theta)) =
    conic_equation Lambda epsilon.
Abort.

Lemma lemma_4_app3_7_ellipse :
  ∀ Lambda epsilon : ℝ, Lambda<>0 -> 0<=epsilon<1 ->
    ellipse (conic_equation Lambda epsilon).
Abort.

Lemma lemma_4_app3_7_parabola :
  ∀ Lambda : ℝ, Lambda<>0 -> parabola (conic_equation Lambda 1).
Abort.

Lemma lemma_4_app3_7_hyperbola :
  ∀ Lambda epsilon : ℝ, Lambda<>0 -> 1<epsilon ->
    hyperbola (conic_equation Lambda epsilon).
Abort.
