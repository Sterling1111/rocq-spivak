From Calculus.Chapter3 Require Export Prelude.
From Stdlib Require Import Reals.Machin.

Lemma lemma_3_11_a : ∀ (H : R -> R) y,
  H (H y) = y -> Nat.iter 80 H y = y.
Proof.
  intros H y H1. cbn. repeat rewrite H1. reflexivity.
Qed.

Lemma lemma_3_11_b : ∀ (H : R -> R) y,
  H (H y) = y -> Nat.iter 81 H y = H y.
Proof.
  intros H y H1. cbn. repeat rewrite H1. reflexivity.
Qed.

Lemma lemma_3_11_c : ∀ (H : R -> R) y,
  H (H y) = H y -> Nat.iter 80 H y = H y /\ Nat.iter 81 H y = H y.
Proof.
  intros H y H1. cbn. repeat rewrite H1. split; reflexivity.
Qed.

Lemma lemma_3_11_d : ∃ H : R -> R,
  (∀ x, H (H x) = H x) /\
  H 1 = 36 /\ H 2 = PI / 3 /\ H 13 = 47 /\
  H 36 = 36 /\ H (PI / 3) = PI / 3 /\ H 47 = 47.
Proof.
  set (H := λ x, if Req_EM_T x 1 then 36 else
    if Req_EM_T x 2 then PI / 3 else if Req_EM_T x 13 then 47 else
    if Req_EM_T x 36 then 36 else if Req_EM_T x (PI / 3) then PI / 3 else
    if Req_EM_T x 47 then 47 else 0).
  assert (H1 : 3 < PI < 4).
  { pose proof (PI_2_3_7_ineq 0) as H1.
    cbn [sum_f_R0] in H1. unfold tg_alt, PI_2_3_7_tg, Ratan_seq in H1.
    simpl in H1. destruct H1 as [H1 H2].
    field_simplify in H1. field_simplify in H2. lra. }
  assert (H2 : H 0 = 0 /\ H 36 = 36 /\ H (PI / 3) = PI / 3 /\ H 47 = 47).
  { repeat apply conj; unfold H; repeat destruct Req_EM_T; lra. }
  exists H. split.
  - intro x. assert (H3 : H x = 0 \/ H x = 36 \/ H x = PI / 3 \/ H x = 47).
    { unfold H. repeat destruct Req_EM_T; tauto. }
    destruct H3 as [H3 | [H3 | [H3 | H3]]]; rewrite H3; tauto.
  - repeat apply conj; unfold H; repeat destruct Req_EM_T; lra.
Qed.

Lemma lemma_3_11_e : ∃ H : R -> R,
  (∀ x, H (H x) = H x) /\ H 1 = 7 /\ H 17 = 18.
Proof.
  set (H := λ x, if Req_EM_T x 1 then 7 else if Req_EM_T x 7 then 7 else
    if Req_EM_T x 17 then 18 else if Req_EM_T x 18 then 18 else 0).
  assert (H1 : H 0 = 0 /\ H 7 = 7 /\ H 18 = 18).
  { repeat apply conj; unfold H; repeat destruct Req_EM_T; lra. }
  exists H. split.
  - intro x. assert (H2 : H x = 0 \/ H x = 7 \/ H x = 18).
    { unfold H. repeat destruct Req_EM_T; tauto. }
    destruct H2 as [H2 | [H2 | H2]]; rewrite H2; tauto.
  - repeat apply conj; unfold H; repeat destruct Req_EM_T; lra.
Qed.
