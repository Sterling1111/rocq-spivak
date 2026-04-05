From Calculus.Chapter21 Require Import Prelude.

(* Problem 5: Countable sets *)

(* (a) Show that if A and B are countable, then so is A ∪ B. *)
Lemma lemma_21_5_a : forall U (A B : Ensemble U),
  countable A -> countable B -> countable (A ⋃ B).
Admitted.

(* (b) Show that the set of positive rational numbers is countable. *)
Lemma lemma_21_5_b :
  countable (fun x : R => exists q : Q, x = Q2R q /\ x > 0).
Admitted.

(* (c) Show that the set of all pairs (m, n) of integers is countable. *)
Lemma lemma_21_5_c :
  countable (Full_set (Z * Z)).
Admitted.

(* (d) If A1, A2, A3... are each countable, A1 ∪ A2 ∪ A3... is countable. *)
Lemma lemma_21_5_d : forall U (F : nat -> Ensemble U),
  (forall n, countable (F n)) ->
  countable (fun x => exists n, x ∈ F n).
Admitted.

(* (e) Prove that the set of all triples (l, m, n) of integers is countable. *)
Lemma lemma_21_5_e :
  countable (Full_set (Z * Z * Z)).
Admitted.

(* (f) Prove that the set of all n-tuples is countable. *)
Lemma lemma_21_5_f : forall n : nat,
  countable (fun l : list Z => length l = n).
Admitted.

(* (g) Prove that the set of all roots of polynomial functions of degree n with integer coefficients is countable. *)
Definition roots_of_degree (n : nat) : Ensemble R :=
  fun x => exists l : list R, 
    degree l = n /\ 
    Forall (fun c => exists z : Z, c = IZR z) l /\
    leading_coefficient l <> 0 /\
    polynomial l x = 0.

Lemma lemma_21_5_g : forall n, countable (roots_of_degree n).
Admitted.

(* (h) Now use parts (d) and (g) to prove that the set of all algebraic numbers is countable. *)
Lemma lemma_21_5_h : countable (fun x => algebraic x).
Admitted.
