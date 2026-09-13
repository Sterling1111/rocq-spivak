From Calculus.Chapter4 Require Import Prelude.

(* (a) For a>0, sketch the lemniscate. *)
Definition problem_4_app3_10_a (a : ℝ) : Ensemble point :=
  polar_locus (λ r theta, r^2=2*a^2*cos (2*theta)).

Lemma lemma_4_app3_10_b :
  ∀ a : ℝ, 0<a -> ∀ x y : ℝ,
    (pair x y ∈ problem_4_app3_10_a a <-> (x^2+y^2)^2=2*a^2*(x^2-y^2)).
Abort.

Lemma lemma_4_app3_10_c :
  ∀ a : ℝ, 0<a -> ∀ p : point,
    (p ∈ problem_4_app3_10_a a <->
     distance p (pair (-a) 0)*distance p (pair a 0)=a^2).
Abort.

(* (d) Guess the shapes of these loci for b>a^2 and b<a^2 (a>0).
   The latter also includes b=0 and b<0; do not silently assume b>0. *)
Definition problem_4_app3_10_d (a b : ℝ) : Ensemble point :=
  λ p, distance p (pair (-a) 0)*distance p (pair a 0)=b.
