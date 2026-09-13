From Calculus.Chapter4 Require Import Prelude.

(* Describe each transformed graph in terms of the graph of f.
   In (iii) and (iv), distinguish c=0, c>0, c<0. *)

Definition problem_4_14_i (f : ℝ -> ℝ) (c : ℝ) : Ensemble point :=
  graph (λ x, f x+c).

Definition problem_4_14_ii (f : ℝ -> ℝ) (c : ℝ) : Ensemble point :=
  graph (λ x, f (x+c)).

Definition problem_4_14_iii (f : ℝ -> ℝ) (c : ℝ) : Ensemble point :=
  graph (λ x, c*f x).

Definition problem_4_14_iv (f : ℝ -> ℝ) (c : ℝ) : Ensemble point :=
  graph (λ x, f (c*x)).

Definition problem_4_14_v (f : ℝ -> ℝ) : Ensemble point :=
  graph_on (λ x, x <> 0) (λ x, f (1/x)).

Definition problem_4_14_vi (f : ℝ -> ℝ) : Ensemble point :=
  graph (λ x, f (|x|)).

Definition problem_4_14_vii (f : ℝ -> ℝ) : Ensemble point :=
  graph (λ x, |f x|).

Definition problem_4_14_viii (f : ℝ -> ℝ) : Ensemble point :=
  graph (λ x, Rmax (f x) 0).

Definition problem_4_14_ix (f : ℝ -> ℝ) : Ensemble point :=
  graph (λ x, Rmin (f x) 0).

Definition problem_4_14_x (f : ℝ -> ℝ) : Ensemble point :=
  graph (λ x, Rmax (f x) 1).
