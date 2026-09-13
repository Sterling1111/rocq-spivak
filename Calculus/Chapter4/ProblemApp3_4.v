From Calculus.Chapter4 Require Import Prelude.

(* Cartesian equations for Appendix 3, Problem 3(i)-(iii). *)
Lemma lemma_4_app3_4_i :
  ∀ a x y : ℝ,
    (pair x y ∈ polar_graph (λ theta, a*sin theta) <-> x^2+y^2=a*y).
Abort.

Lemma lemma_4_app3_4_ii :
  ∀ a x y : ℝ, a<>0 ->
    (pair x y ∈ polar_locus (λ r theta, cos theta<>0 /\ r=a*sec theta) <-> x=a).
Abort.

Lemma lemma_4_app3_4_ii_zero :
  polar_locus (λ r theta, cos theta<>0 /\ r=0*sec theta) = ⦃pair 0 0⦄.
Abort.

Lemma lemma_4_app3_4_iii :
  ∀ x y : ℝ,
    (pair x y ∈ polar_graph (λ theta, cos (2*theta)) <->
     (x^2+y^2)^3=(x^2-y^2)^2).
Abort.
