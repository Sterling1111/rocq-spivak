From Calculus.Chapter4 Require Import Prelude.

(* pp. 68-69: locate each set on the real line and express it with intervals. *)

Lemma lemma_4_1_i :
  ∀ x : ℝ, (|x-3| < 1 <-> x ∈ (2, 4)).
Abort.

Lemma lemma_4_1_ii :
  ∀ x : ℝ, (|x-3| <= 1 <-> x ∈ [2, 4]).
Abort.

Lemma lemma_4_1_iii :
  ∀ a epsilon x : ℝ, (|x-a| < epsilon <-> x ∈ (a-epsilon, a+epsilon)).
Abort.

Lemma lemma_4_1_iv :
  ∀ x : ℝ, (|x^2-1| < 1/2 <-> x ∈ ((-√(3/2), -√(1/2)) ⋃ (√(1/2), √(3/2)))).
Abort.

Lemma lemma_4_1_v :
  ∀ x : ℝ, (1/(1+x^2) >= 1/5 <-> x ∈ [-2, 2]).
Abort.

Lemma lemma_4_1_vi :
  ∀ a x : ℝ,
    (1/(1+x^2) <= a <->
     (a >= 1 \/ (0 < a < 1 /\
      x ∈ (( -∞, -√(1/a-1)] ⋃ [√(1/a-1), ∞))))).
Abort.

Lemma lemma_4_1_vii :
  ∀ x : ℝ, (x^2+1 >= 2 <-> x ∈ (( -∞, -1] ⋃ [1, ∞))).
Abort.

Lemma lemma_4_1_viii :
  ∀ x : ℝ, ((x+1)*(x-1)*(x-2) > 0 <-> x ∈ ((-1, 1) ⋃ (2, ∞))).
Abort.

