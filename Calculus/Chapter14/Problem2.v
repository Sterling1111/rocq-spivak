From Calculus.Chapter14 Require Import Prelude.

(* Problem 2: For each of the following f, if F(x) = ∫ 0 x f,
   at which points x is F'(x) = f(x)? *)

(* (i) f(x) = 0 if x ≤ 1, f(x) = 1 if x > 1 *)
Definition f_2_i (x : R) : R := if Rle_dec x 1 then 0 else 1.

Lemma lemma_14_2_i : forall x,
  let F := fun x => ∫ 0 x f_2_i in
  x <> 1 -> ⟦ der x ⟧ F = f_2_i.
Abort.

(* (ii) f(x) = 0 if x < 1, f(x) = 1 if x ≥ 1 *)
Definition f_2_ii (x : R) : R := if Rlt_dec x 1 then 0 else 1.

Lemma lemma_14_2_ii : forall x,
  let F := fun x => ∫ 0 x f_2_ii in
  x <> 1 -> ⟦ der x ⟧ F = f_2_ii.
Abort.

(* (iii) f(x) = 0 if x ≠ 1, f(x) = 1 if x = 1 *)
Definition f_2_iii (x : R) : R :=
  match Req_dec_T x 1 with left _ => 1 | right _ => 0 end.

Lemma lemma_14_2_iii : forall x,
  let F := fun x => ∫ 0 x f_2_iii in
  ⟦ der x ⟧ F = (fun _ => 0).
Abort.

(* (iv) f(x) = 0 if x is irrational, f(x) = 1/q if x = p/q in lowest terms *)
(* This is the Thomae function; we state the result that F'(x) = 0 for all x *)
Lemma lemma_14_2_iv : forall f F,
  (forall x, F x = ∫ 0 x f) ->
  (forall x, ⟦ der x ⟧ F = (fun _ => 0)).
Abort.

(* (v) f(x) = 0 if x ≤ 0, f(x) = x if x ≥ 0 *)
Definition f_2_v (x : R) : R := if Rle_dec x 0 then 0 else x.

Lemma lemma_14_2_v : forall x,
  let F := fun x => ∫ 0 x f_2_v in
  ⟦ der x ⟧ F = f_2_v.
Abort.

(* (vi) f(x) = 0 if x ≤ 0 or x > 1, f(x) = 1/⌊1/x⌋ if 0 < x ≤ 1 *)
(* Stated informally; the derivative equals f at all but countably many points *)
Lemma lemma_14_2_vi : forall f F,
  (forall x, F x = ∫ 0 x f) ->
  forall x, continuous_at f x -> ⟦ der x ⟧ F = f.
Abort.

(* (vii) f is as shown in Figure 6 *)
(* Skipped: depends on a specific figure *)

(* (viii) f(x) = 1 if x = 1/n for some n in N, f(x) = 0 otherwise *)
Definition f_2_viii (x : R) : R :=
  if excluded_middle_informative (exists n : nat, (n > 0)%nat /\ x = 1 / INR n)
  then 1 else 0.

Lemma lemma_14_2_viii : forall x,
  let F := fun x => ∫ 0 x f_2_viii in
  ⟦ der x ⟧ F = (fun _ => 0).
Abort.
