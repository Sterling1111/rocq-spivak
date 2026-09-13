From Calculus.Chapter4 Require Import Prelude.

(* Sketch all six graphs on their natural domains. Use the integer-valued
   floor Zfloor, not Lib's natural-valued notation, which truncates negatives. *)
Local Notation floorR x := (((Zfloor x)%Z : ℝ)).

Definition problem_4_17_i : Ensemble point :=
  graph_on ℝ (λ x, floorR x).

Definition problem_4_17_ii : Ensemble point :=
  graph_on ℝ (λ x, x-floorR x).

Definition problem_4_17_iii : Ensemble point :=
  graph_on ℝ (λ x, √(x-floorR x)).

Definition problem_4_17_iv : Ensemble point :=
  graph_on ℝ (λ x, floorR x+√(x-floorR x)).

Definition problem_4_17_v : Ensemble point :=
  graph_on (λ x, x <> 0) (λ x, floorR (1/x)).

Definition problem_4_17_vi : Ensemble point :=
  graph_on (λ x, x <> 0 /\ floorR (1/x) <> 0) (λ x, 1 / floorR (1/x)).
