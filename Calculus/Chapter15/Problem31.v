From Calculus.Chapter15 Require Import Prelude.

(* Problem 31 *)

(* (a) sin isn't a rational function *)
Lemma lemma_15_31_a :
  ~ exists (p q : R -> R),
    (exists n, forall x, p x = sum_f 0 n (fun i => nth i nil 0 * x ^ i)) /\
    (exists n, forall x, q x = sum_f 0 n (fun i => nth i nil 0 * x ^ i)) /\
    (forall x, q x <> 0 -> sin x = p x / q x).
Abort.

(* (b) sin isn't defined implicitly by an algebraic equation *)
Lemma lemma_15_31_b : forall (n : nat),
  ~ exists (fs : nat -> R -> R),
    (forall i, exists (ci : list R), forall x, fs i x = sum_f 0 (length ci) (fun j => nth j ci 0 * x ^ j)) /\
    (forall x, (sin x) ^ (S n) + ∑ 0 n (fun i => fs i x * (sin x) ^ i) = 0).
Abort.
