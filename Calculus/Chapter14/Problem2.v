From Calculus.Chapter14 Require Import Prelude.

Definition f_2_i (x : R) : R := if Rle_dec x 1 then 0 else 1.

Lemma lemma_14_2_i : ∀ x,
  let F := λ x, ∫ 0 x f_2_i in
  x <> 1 -> ⟦ der x ⟧ F = f_2_i.
Abort.

Definition f_2_ii (x : R) : R := if Rlt_dec x 1 then 0 else 1.

Lemma lemma_14_2_ii : ∀ x,
  let F := λ x, ∫ 0 x f_2_ii in
  x <> 1 -> ⟦ der x ⟧ F = f_2_ii.
Abort.

Definition f_2_iii (x : R) : R :=
  match Req_dec_T x 1 with left _ => 1 | right _ => 0 end.

Lemma lemma_14_2_iii : ∀ x,
  let F := λ x, ∫ 0 x f_2_iii in
  ⟦ der x ⟧ F = (λ _, 0).
Abort.

Lemma lemma_14_2_iv : ∀ f F,
  (∀ x, F x = ∫ 0 x f) ->
  (∀ x, ⟦ der x ⟧ F = (λ _, 0)).
Abort.

Definition f_2_v (x : R) : R := if Rle_dec x 0 then 0 else x.

Lemma lemma_14_2_v : ∀ x,
  let F := λ x, ∫ 0 x f_2_v in
  ⟦ der x ⟧ F = f_2_v.
Abort.

Lemma lemma_14_2_vi : ∀ f F,
  (∀ x, F x = ∫ 0 x f) ->
  ∀ x, continuous_at f x -> ⟦ der x ⟧ F = f.
Abort.

Definition f_2_viii (x : R) : R :=
  if excluded_middle_informative (∃ n : nat, (n > 0)%nat /\ x = 1 / n)
  then 1 else 0.

Lemma lemma_14_2_viii : ∀ x,
  let F := λ x, ∫ 0 x f_2_viii in
  ⟦ der x ⟧ F = (λ _, 0).
Abort.
