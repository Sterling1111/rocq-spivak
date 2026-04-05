From Calculus.Chapter23 Require Import Prelude.

(* Problem 21 *)

(* (a) Dirichlet's test *)
Lemma problem_23_21_a : forall a b,
  bounded (fun n => ∑ 1 n a) ->
  decreasing b ->
  ⟦ lim ⟧ b = 0 ->
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n * b n) = S.
Admitted.

(* (b) Derive Leibniz's Theorem from this result. *)
Lemma problem_23_21_b : forall b,
  decreasing b ->
  ⟦ lim ⟧ b = 0 ->
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else (-1)^(n+1) * b n) = S.
Admitted.

(* (c) Prove that \sum (\cos nx)/n converges if x <> 2k\pi. *)
Lemma problem_23_21_c : forall x,
  (forall k : Z, x <> 2 * IZR k * π) ->
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else cos (INR n * x) / INR n) = S.
Admitted.

(* (d) Abel's test *)
Lemma problem_23_21_d : forall a b,
  (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S) ->
  decreasing b ->
  bounded b ->
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n * b n) = S.
Admitted.
