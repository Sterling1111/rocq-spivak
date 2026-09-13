From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_2_a :
  ∀ b x : ℝ, 0 < b -> x ∈ [0,b] -> ∃ t : ℝ, 0 <= t <= 1 /\ x = t*b /\ t = x/b.
Abort.

Lemma lemma_4_2_a_midpoint :
  ∀ b : ℝ, 0 < b -> distance (pair (0) (0)) (pair (b/2) (0)) = distance (pair (b/2) (0)) (pair (b) (0)) /\ b/2 ∈ [0,b].
Abort.

Lemma lemma_4_2_b :
  ∀ a b x : ℝ, a < b -> x ∈ [a,b] -> ∃ t : ℝ, 0 <= t <= 1 /\ x = (1-t)*a+t*b /\ t = (x-a)/(b-a).
Abort.

Lemma lemma_4_2_b_midpoint :
  ∀ a b : ℝ, a < b -> (a+b)/2 ∈ [a,b] /\ (a+b)/2-a = b-(a+b)/2.
Abort.

Lemma lemma_4_2_b_third :
  ∀ a b : ℝ, a < b -> (2*a+b)/3 ∈ [a,b] /\ (2*a+b)/3-a = (b-a)/3.
Abort.

Lemma lemma_4_2_c :
  ∀ a b t : ℝ, a < b -> 0 <= t <= 1 -> ((1-t)*a+t*b) ∈ [a,b].
Abort.

Lemma lemma_4_2_d :
  ∀ a b x : ℝ, a < b -> (x ∈ (a,b) <-> ∃ t : ℝ, 0 < t < 1 /\ x = (1-t)*a+t*b).
Abort.
