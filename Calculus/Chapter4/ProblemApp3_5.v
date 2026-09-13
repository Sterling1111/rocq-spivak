From Calculus.Chapter4 Require Import Prelude.

(* Both hyperbola branches are represented using signed r. With the
   specified foci, Lambda=(1-epsilon^2)*a is NEGATIVE. Restricting r to
   nonnegative values would lose a branch. *)
Lemma lemma_4_app3_5 :
  ∀ a epsilon : ℝ, 0<a -> 1<epsilon ->
    let Lambda := (1-epsilon^2)*a in
    ∀ x y : ℝ,
      (|distance (pair x y) (pair 0 0) -
        distance (pair x y) (pair (-2*epsilon*a) 0)|=2*a <->
       pair x y ∈ polar_locus (λ r theta,
         1+epsilon*cos theta<>0 /\ r=Lambda/(1+epsilon*cos theta))).
Abort.
