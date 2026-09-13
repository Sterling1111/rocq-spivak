From Calculus.Chapter4 Require Import Prelude.

(* Sketch all six polar graphs; signed radii are allowed. For (i),(ii),
   a is the scale parameter (usually positive); (ii) excludes poles of sec. *)
Definition problem_4_app3_3_i (a : ℝ) := polar_graph (λ theta, a*sin theta).
Definition problem_4_app3_3_ii (a : ℝ) : Ensemble point :=
  polar_locus (λ r theta, cos theta<>0 /\ r=a*sec theta).
Definition problem_4_app3_3_iii := polar_graph (λ theta, cos (2*theta)).
Definition problem_4_app3_3_iv := polar_graph (λ theta, cos (3*theta)).
Definition problem_4_app3_3_v := polar_graph (λ theta, |cos (2*theta)|).
Definition problem_4_app3_3_vi := polar_graph (λ theta, |cos (3*theta)|).
