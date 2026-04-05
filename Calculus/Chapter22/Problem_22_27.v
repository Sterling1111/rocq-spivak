From Calculus.Chapter22 Require Import Prelude.

(* We introduce ad-hoc limits superior and inferior concepts based on bounds for stating the problem. *)

Definition sequence_bound_sup (x : sequence) (n : nat) :=
  glb (fun y => forall k : nat, (k >= n)%nat -> x k <= y).

Lemma lemma_22_27_a : forall x y,
  bounded x ->
  (forall n, is_lub (fun r => exists k, (k >= n)%nat /\ x k = r) (y n)) ->
  convergent_sequence y.
Admitted.

Lemma lemma_22_27_b : exists P, P = True.
Admitted.

Lemma lemma_22_27_c : forall x c d y z,
  bounded x ->
  (forall n, is_lub (fun r => exists k, (k >= n)%nat /\ x k = r) (y n)) ->
  (forall n, is_glb (fun r => exists k, (k >= n)%nat /\ x k = r) (z n)) ->
  ⟦ lim ⟧ y = c -> ⟦ lim ⟧ z = d ->
  d <= c.
Admitted.

Lemma lemma_22_27_d : forall x c d L y z,
  bounded x ->
  (forall n, is_lub (fun r => exists k, (k >= n)%nat /\ x k = r) (y n)) ->
  (forall n, is_glb (fun r => exists k, (k >= n)%nat /\ x k = r) (z n)) ->
  ⟦ lim ⟧ y = c -> ⟦ lim ⟧ z = d ->
  (c = d <-> ⟦ lim ⟧ x = L /\ L = c /\ L = d).
Admitted.

Lemma lemma_22_27_e : exists P, P = True.
Admitted.
