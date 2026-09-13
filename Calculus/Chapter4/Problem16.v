From Calculus.Chapter4 Require Import Prelude.

(* PDF p. 72: the hint's "A and B" must read "A and C". *)
Definition quadratic_locus (A B C D E : ℝ) : Ensemble point :=
  locus (λ x y, A*x^2+B*x+C*y^2+D*y+E=0).

Lemma lemma_4_16 :
  ∀ A B C D E : ℝ, (A <> 0 \/ C <> 0) -> let S := quadratic_locus A B C D E in parabola S \/ ellipse S \/ hyperbola S \/ degenerate_conic S.
Abort.

Lemma lemma_4_16_circle :
  ∀ A B C D E : ℝ, (A <> 0 \/ C <> 0) -> (circle (quadratic_locus A B C D E) <-> A=C /\ A<>0 /\ (B^2+D^2)/(4*A^2)-E/A > 0).
Abort.
