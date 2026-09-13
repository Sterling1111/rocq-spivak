From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_7_a : ∀ l a,
  ∃ g b, ∀ x, polynomial l x = (x - a) * polynomial g x + b.
Proof.
  intros l a.
  induction l as [| h t [Q [b IH]]] using rev_ind.
  - exists [], 0. intros x. rewrite poly_nil. lra.
  - exists (Q ++ [b]), (b * a + h).
    intros x.
    rewrite poly_shift, IH, poly_shift.
    lra.
Qed.

Lemma lemma_3_7_b : ∀ l1 a,
  polynomial l1 a = 0 ->
  ∃ l2, ∀ x, polynomial l1 x = (x - a) * polynomial l2 x.
Proof.
  intros l1 a H1.
  destruct (lemma_3_7_a l1 a) as [l2 [b H2]].
  assert (H3 : b = 0).
  { pose proof (H2 a) as H3; lra. }
  exists l2.
  intros x.
  rewrite H2, H3.
  lra.
Qed.

(* The zero polynomial has no degree in the book. Lib.degree [] = 0,
   so explicitly exclude identically zero polynomials here. *)
Lemma lemma_3_7_c : ∀ (l roots : list R),
  (∃ x, polynomial l x <> 0) -> NoDup roots ->
  (∀ a, List.In a roots -> polynomial l a = 0) ->
  (List.length roots <= degree l)%nat.
Abort.

Lemma lemma_3_7_d : ∀ n : nat, ∃ l roots : list R,
  degree l = n /\ (∃ x, polynomial l x <> 0) /\
  NoDup roots /\ List.length roots = n /\
  (∀ x, polynomial l x = 0 <-> List.In x roots).
Abort.

Lemma lemma_3_7_d_even : ∀ n : nat, Nat.Even n ->
  ∃ l : list R, degree l = n /\ ∀ x, polynomial l x <> 0.
Abort.

Lemma lemma_3_7_d_odd : ∀ n : nat, Nat.Odd n ->
  ∃ (l : list R) (a : R), degree l = n /\
    (∃ x, polynomial l x <> 0) /\ (∀ x, polynomial l x = 0 <-> x = a).
Abort.
