From Calculus.Chapter15 Require Import Prelude.

Definition f_sinc (x : R) : R :=
  match Req_dec_T x 0 with
  | left _ => 1
  | right _ => sin x / x
  end.

Lemma lemma_15_3_a :
  ⟦ der 0 ⟧ f_sinc = (λ _, 0).
Proof.
  unfold derivative_at.
  apply limit_eq with (f1 := λ h, (sin h - h) / h^2).
  - exists 1. split; [lra |]. intros h H1.
    unfold f_sinc. rewrite Rplus_0_l.
    destruct (Req_dec_T h 0); [solve_R |].
    destruct (Req_dec_T 0 0); [field; auto | contradiction].
  - step_lhopital (λ h, cos h - 1) (λ h, 2 * h).
    step_lhopital (λ h, - sin h) (λ h : R, 2).
Qed.

Lemma lemma_15_3_b :
  ⟦ der^2 0 ⟧ f_sinc = (λ _, -1/3).
Proof.
  set (g := λ x, match Req_dec_T x 0 with
    | left _ => 0
    | right _ => (x * cos x - sin x) / x^2
    end).
  assert (H1 : ⟦ der ⟧ f_sinc = g).
  { intro x. destruct (Req_dec x 0) as [H1 | H1].
    - subst x. apply derivative_at_ext_val with (f' := λ _, 0).
      + apply lemma_15_3_a.
      + unfold g. destruct (Req_dec_T 0 0); [reflexivity | contradiction].
    - apply derivative_at_eq with (f1 := λ x, sin x / x).
      + exists (|x| / 2). split; [solve_R |]. intros y H2.
        unfold f_sinc. destruct (Req_dec_T y 0); [subst y; solve_R | reflexivity].
      + apply derivative_at_ext_val with (f' := λ x, (x * cos x - sin x) / x^2).
        * auto_diff.
        * unfold g. destruct (Req_dec_T x 0); [contradiction | reflexivity]. }
  exists 1, g. split; [lra |]. split.
  - apply nth_derivative_on_1.
    apply derivative_imp_derivative_on_open; [lra | exact H1].
  - unfold derivative_at.
    apply limit_eq with (f1 := λ h, (h * cos h - sin h) / h^3).
    + exists 1. split; [lra |]. intros h H2.
      unfold g. replace (0 + h) with h by lra.
      destruct (Req_dec_T h 0); [solve_R |].
      destruct (Req_dec_T 0 0); [field; auto | contradiction].
    + step_lhopital (λ h, - h * sin h) (λ h, 3 * h^2).
      step_lhopital (λ h, - sin h - h * cos h) (λ h, 6 * h).
      step_lhopital (λ h, -2 * cos h + h * sin h) (λ h : R, 6).
Qed.
