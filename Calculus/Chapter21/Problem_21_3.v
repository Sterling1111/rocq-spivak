From Calculus.Chapter21 Require Import Prelude.

(* Problem 3: Liouville's theorem on Diophantine approximation *)

Definition Z_poly (l : list R) : Prop :=
  Forall (fun c => exists z : Z, c = IZR z) l.

(* (a) Show that f(p/q) ≠ 0 for any rational number p/q. *)
Lemma lemma_21_3_a : forall α (l : list R),
  ~ (exists q : Q, α = Q2R q) ->
  Z_poly l ->
  leading_coefficient l <> 0 ->
  polynomial l α = 0 ->
  (forall l', Z_poly l' -> leading_coefficient l' <> 0 -> polynomial l' α = 0 -> (degree l' >= degree l)%nat) ->
  forall p q : Z, (q <> 0)%Z -> polynomial l (IZR p / IZR q) <> 0.
Admitted.

(* (b) Now show that |f(p/q)| ≥ 1/q^n for all rational numbers p/q with q > 0. *)
Lemma lemma_21_3_b : forall α (l : list R),
  ~ (exists q : Q, α = Q2R q) ->
  Z_poly l ->
  leading_coefficient l <> 0 ->
  polynomial l α = 0 ->
  (forall l', Z_poly l' -> leading_coefficient l' <> 0 -> polynomial l' α = 0 -> (degree l' >= degree l)%nat) ->
  forall p q : Z, (q > 0)%Z -> |polynomial l (IZR p / IZR q)| >= 1 / (IZR q) ^ (degree l).
Admitted.

(* (c) Use the Mean Value Theorem to prove the approximation bound. *)
Lemma lemma_21_3_c : forall α (l : list R),
  ~ (exists q : Q, α = Q2R q) ->
  Z_poly l ->
  leading_coefficient l <> 0 ->
  polynomial l α = 0 ->
  (forall l', Z_poly l' -> leading_coefficient l' <> 0 -> polynomial l' α = 0 -> (degree l' >= degree l)%nat) ->
  exists c : R, c > 0 /\ 
    (forall p q : Z, (q > 0)%Z -> |α - (IZR p / IZR q)| < 1 -> |α - (IZR p / IZR q)| > c / (IZR q) ^ (degree l)).
Admitted.
