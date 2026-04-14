From Lib Require Import Imports Notations Reals_util Sets Limit Continuity Derivative Integral Trigonometry Functions Interval Sums Exponential.
Import IntervalNotations SetNotations FunctionNotations DerivativeNotations LimitNotations IntegralNotations SumNotations.

Inductive expr :=
| EVar
| EConst (c : R)
| EAdd (e1 e2 : expr)
| ESub (e1 e2 : expr)
| EMul (e1 e2 : expr)
| EDiv (e1 e2 : expr)
| ENeg (e : expr)
| ESin (e : expr)
| ECos (e : expr)
| ETan (e : expr)
| ECot (e : expr)
| ECsc (e : expr)
| ESec (e : expr)
| EArcsin (e : expr)
| EArccos (e : expr)
| EArctan (e : expr)
| ESqrt (e : expr)
| EExp (e : expr)
| ELog (e : expr)
| ERpow (e : expr) (r : R)
| ERpower (e1 e2 : expr)
| EPow (e : expr) (n : nat)
| EApp (f : R -> R) (df : option (R -> R)) (e : expr).

Fixpoint eval_expr (e : expr) (x : R) : R :=
  match e with
  | EVar => x
  | EConst c => c
  | EAdd e1 e2 => eval_expr e1 x + eval_expr e2 x
  | ESub e1 e2 => eval_expr e1 x - eval_expr e2 x
  | EMul e1 e2 => eval_expr e1 x * eval_expr e2 x
  | EDiv e1 e2 => eval_expr e1 x / eval_expr e2 x
  | ENeg e => - (eval_expr e x)
  | ESin e => sin (eval_expr e x)
  | ECos e => cos (eval_expr e x)
  | ETan e => tan (eval_expr e x)
  | ECot e => cot (eval_expr e x)
  | ECsc e => csc (eval_expr e x)
  | ESec e => sec (eval_expr e x)
  | EArcsin e => arcsin (eval_expr e x)
  | EArccos e => arccos (eval_expr e x)
  | EArctan e => arctan (eval_expr e x)
  | ESqrt e => sqrt (eval_expr e x)
  | EExp e => exp (eval_expr e x)
  | ELog e => log (eval_expr e x)
  | ERpow e r => (eval_expr e x) ^^ r
  | ERpower e1 e2 => (eval_expr e1 x) ^^ (eval_expr e2 x)
  | EPow e n => (eval_expr e x) ^ n
  | EApp f _ e => f (eval_expr e x)
  end.

Fixpoint wf_limit (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_limit e1 a /\ wf_limit e2 a
  | EDiv e1 e2 => wf_limit e1 a /\ wf_limit e2 a /\ eval_expr e2 a <> 0
  | ENeg e | ESin e | ECos e | EExp e | EPow e _ | EArctan e => wf_limit e a
  | ELog e => wf_limit e a /\ eval_expr e a > 0
  | ERpow e _ => wf_limit e a /\ eval_expr e a > 0
  | ERpower e1 e2 => wf_limit e1 a /\ wf_limit e2 a /\ eval_expr e1 a > 0
  | ETan e | ESec e => wf_limit e a /\ cos (eval_expr e a) <> 0
  | ECot e | ECsc e => wf_limit e a /\ sin (eval_expr e a) <> 0
  | EArcsin e | EArccos e => wf_limit e a /\ -1 < eval_expr e a < 1
  | ESqrt e => wf_limit e a /\ eval_expr e a >= 0
  | EApp f _ e => wf_limit e a /\ continuous_at f (eval_expr e a)
  end.

Fixpoint wf_limit_right (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_limit_right e1 a /\ wf_limit_right e2 a
  | EDiv e1 e2 => wf_limit_right e1 a /\ wf_limit_right e2 a /\ eval_expr e2 a <> 0
  | ENeg e | ESin e | ECos e | EExp e | EPow e _ | EArctan e => wf_limit_right e a
  | ELog e => wf_limit_right e a /\ eval_expr e a > 0
  | ERpow e _ => wf_limit_right e a /\ eval_expr e a > 0
  | ERpower e1 e2 => wf_limit_right e1 a /\ wf_limit_right e2 a /\ eval_expr e1 a > 0
  | ETan e | ESec e => wf_limit_right e a /\ cos (eval_expr e a) <> 0
  | ECot e | ECsc e => wf_limit_right e a /\ sin (eval_expr e a) <> 0
  | EArcsin e | EArccos e => wf_limit_right e a /\ -1 < eval_expr e a < 1
  | ESqrt e => wf_limit_right e a /\ eval_expr e a >= 0
  | EApp f _ e => wf_limit_right e a /\ continuous_at f (eval_expr e a)
  end.

Fixpoint wf_limit_left (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_limit_left e1 a /\ wf_limit_left e2 a
  | EDiv e1 e2 => wf_limit_left e1 a /\ wf_limit_left e2 a /\ eval_expr e2 a <> 0
  | ENeg e | ESin e | ECos e | EExp e | EPow e _ | EArctan e => wf_limit_left e a
  | ELog e => wf_limit_left e a /\ eval_expr e a > 0
  | ERpow e _ => wf_limit_left e a /\ eval_expr e a > 0
  | ERpower e1 e2 => wf_limit_left e1 a /\ wf_limit_left e2 a /\ eval_expr e1 a > 0
  | ETan e | ESec e => wf_limit_left e a /\ cos (eval_expr e a) <> 0
  | ECot e | ECsc e => wf_limit_left e a /\ sin (eval_expr e a) <> 0
  | EArcsin e | EArccos e => wf_limit_left e a /\ -1 < eval_expr e a < 1
  | ESqrt e => wf_limit_left e a /\ eval_expr e a > 0
  | EApp f _ e => wf_limit_left e a /\ continuous_at f (eval_expr e a)
  end.

Fixpoint wf_cont (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_cont e1 a /\ wf_cont e2 a
  | EDiv e1 e2 => wf_cont e1 a /\ wf_cont e2 a /\ eval_expr e2 a <> 0
  | ENeg e | ESin e | ECos e | EExp e | EPow e _ | EArctan e => wf_cont e a
  | ELog e => wf_cont e a /\ eval_expr e a > 0
  | ERpow e _ => wf_cont e a /\ eval_expr e a > 0
  | ERpower e1 e2 => wf_cont e1 a /\ wf_cont e2 a /\ eval_expr e1 a > 0
  | ETan e | ESec e => wf_cont e a /\ cos (eval_expr e a) <> 0
  | ECot e | ECsc e => wf_cont e a /\ sin (eval_expr e a) <> 0
  | EArcsin e | EArccos e => wf_cont e a /\ -1 < eval_expr e a < 1
  | ESqrt e => wf_cont e a /\ eval_expr e a > 0
  | EApp f _ e => wf_cont e a /\ continuous_at f (eval_expr e a)
  end.

Fixpoint wf_derive (e : expr) (x : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_derive e1 x /\ wf_derive e2 x
  | EDiv e1 e2 => wf_derive e1 x /\ wf_derive e2 x /\ eval_expr e2 x <> 0
  | ENeg e | ESin e | ECos e | EExp e | EPow e _ | EArctan e => wf_derive e x
  | ELog e => wf_derive e x /\ eval_expr e x > 0
  | ERpow e _ => wf_derive e x /\ eval_expr e x > 0
  | ERpower e1 e2 => wf_derive e1 x /\ wf_derive e2 x /\ eval_expr e1 x > 0
  | ETan e | ESec e => wf_derive e x /\ cos (eval_expr e x) <> 0
  | ECot e | ECsc e => wf_derive e x /\ sin (eval_expr e x) <> 0
  | EArcsin e | EArccos e => wf_derive e x /\ -1 < eval_expr e x < 1
  | ESqrt e => wf_derive e x /\ eval_expr e x > 0
  | EApp f (Some f') e => wf_derive e x /\ ⟦ der (eval_expr e x) ⟧ f = f'
  | EApp f None e => False
  end.

Fixpoint derive_expr (e : expr) : expr :=
  match e with
  | EVar => EConst 1
  | EConst _ => EConst 0
  | EAdd e1 e2 => EAdd (derive_expr e1) (derive_expr e2)
  | ESub e1 e2 => ESub (derive_expr e1) (derive_expr e2)
  | EMul e1 e2 => EAdd (EMul (derive_expr e1) e2) (EMul e1 (derive_expr e2))
  | EDiv e1 e2 => EDiv (ESub (EMul (derive_expr e1) e2) (EMul e1 (derive_expr e2))) (EPow e2 2)
  | ENeg e => ENeg (derive_expr e)
  | ESin e => EMul (ECos e) (derive_expr e)
  | ECos e => EMul (ENeg (ESin e)) (derive_expr e)
  | ETan e => EDiv (derive_expr e) (EPow (ECos e) 2)
  | ECot e => EMul (ENeg (EPow (ECsc e) 2)) (derive_expr e)
  | ECsc e => EMul (ENeg (EMul (ECsc e) (ECot e))) (derive_expr e)
  | ESec e => EMul (EMul (ESec e) (ETan e)) (derive_expr e)
  | EArcsin e => EDiv (derive_expr e) (ESqrt (ESub (EConst 1) (EPow e 2)))
  | EArccos e => EDiv (ENeg (derive_expr e)) (ESqrt (ESub (EConst 1) (EPow e 2)))
  | EArctan e => EDiv (derive_expr e) (EAdd (EConst 1) (EPow e 2))
  | ESqrt e => EDiv (derive_expr e) (EMul (EConst 2) (ESqrt e))
  | EExp e => EMul (EExp e) (derive_expr e)
  | ELog e => EDiv (derive_expr e) e
  | ERpow e r => EMul (EMul (EConst r) (ERpow e (r - 1))) (derive_expr e)
  | ERpower e1 e2 => EMul (ERpower e1 e2) (EAdd (EMul (derive_expr e2) (ELog e1)) (EMul e2 (EDiv (derive_expr e1) e1)))
  | EPow e n => match n with 0 => EConst 0 | S k => EMul (EMul (EConst (INR n)) (EPow e k)) (derive_expr e) end
  | EApp f (Some f') e => EMul (EApp f' (Some (λ _, 0)) e) (derive_expr e)
  | EApp f None e => EConst 0
  end.

Lemma right_limit_eval_expr : forall e a,
  wf_limit_right e a -> ⟦ lim a⁺ ⟧ (fun x => eval_expr e x) = eval_expr e a.
Proof.
  induction e; intros a H; simpl in *; try solve_R; try apply limit_right_id || apply limit_right_const.
  - destruct H as [H1 H2]. apply limit_right_plus; auto.
  - destruct H as [H1 H2]. apply limit_right_minus; auto.
  - destruct H as [H1 H2]. apply limit_right_mult; auto.
  - destruct H as [H1 [H2 H3]]. apply limit_right_div; auto.
  - apply limit_right_neg; auto.
  - apply limit_right_continuous_comp; auto. apply continuous_sin.
  - apply limit_right_continuous_comp; auto. apply continuous_cos.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_at_tan; auto.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_at_cot; auto.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_at_csc; auto.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_at_sec; auto.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_at_arcsin; auto.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_at_arccos; auto.
  - apply limit_right_continuous_comp; auto. apply continuous_at_arctan.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_sqrt.
  - apply limit_right_continuous_comp; auto. apply continuous_exp.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto. apply continuous_at_log; exact H2.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp with (f := fun y => y ^^ r); auto. apply continuous_at_Rpower_const; exact H2.
  - destruct H as [H1 [H2 H3]]. apply continuous_at_right_Rpower_comp; auto.
  - apply limit_right_pow; auto.
  - destruct H as [H1 H2]. apply limit_right_continuous_comp; auto.
Qed.

Lemma left_limit_eval_expr : forall e a,
  wf_limit_left e a -> ⟦ lim a⁻ ⟧ (fun x => eval_expr e x) = eval_expr e a.
Proof.
  induction e; intros a H1; simpl in *; try solve_R; try apply limit_left_id || apply limit_left_const.
  - destruct H1 as [H2 H3]. apply limit_left_plus; auto.
  - destruct H1 as [H2 H3]. apply limit_left_minus; auto.
  - destruct H1 as [H2 H3]. apply limit_left_mult; auto.
  - destruct H1 as [H2 [H3 H4]]. apply limit_left_div; auto.
  - apply limit_left_neg; auto.
  - apply limit_left_continuous_comp; auto. apply continuous_sin.
  - apply limit_left_continuous_comp; auto. apply continuous_cos.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_at_tan; auto.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_at_cot; auto.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_at_csc; auto.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_at_sec; auto.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_at_arcsin; auto.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_at_arccos; auto.
  - apply limit_left_continuous_comp; auto. apply continuous_at_arctan.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_sqrt.
  - apply limit_left_continuous_comp; auto. apply continuous_exp.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto. apply continuous_at_log; exact H3.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp with (f := fun y => y ^^ r); auto. apply continuous_at_Rpower_const; exact H3.
  - destruct H1 as [H2 [H3 H4]]. apply continuous_at_left_Rpower_comp; auto.
  - apply limit_left_pow; auto.
  - destruct H1 as [H2 H3]. apply limit_left_continuous_comp; auto.
Qed.

Lemma limit_eval_expr : forall e a,
  wf_limit e a -> ⟦ lim a ⟧ (fun x => eval_expr e x) = eval_expr e a.
Proof.
  induction e; intros a H1; simpl in *; try solve_R; try apply limit_id || apply limit_const.
  - destruct H1 as [H2 H3]. apply limit_plus; auto.
  - destruct H1 as [H2 H3]. apply limit_minus; auto.
  - destruct H1 as [H2 H3]. apply limit_mult; auto.
  - destruct H1 as [H2 [H3 H4]]. apply limit_div; auto.
  - apply limit_neg; auto.
  - apply limit_continuous_comp; auto. apply continuous_sin.
  - apply limit_continuous_comp; auto. apply continuous_cos.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_at_tan; auto.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_at_cot; auto.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_at_csc; auto.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_at_sec; auto.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_at_arcsin; auto.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_at_arccos; auto.
  - apply limit_continuous_comp; auto. apply continuous_at_arctan.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_sqrt.
  - apply limit_continuous_comp; auto. apply continuous_exp.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto. apply continuous_at_log; exact H3.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp with (f := fun y => y ^^ r); auto. apply continuous_at_Rpower_const; exact H3.
  - destruct H1 as [H2 [H3 H4]]. apply limit_Rpower_comp; auto.
  - apply limit_pow; auto.
  - destruct H1 as [H2 H3]. apply limit_continuous_comp; auto.
Qed.

Lemma continuity_correct : forall e x,
  wf_limit e x -> continuous_at (λ t, eval_expr e t) x.
Proof.
  intros e x H. apply limit_eval_expr in H. exact H.
Qed.

Lemma cont_correct : forall e x,
  wf_cont e x -> continuous_at (λ t, eval_expr e t) x.
Proof.
  induction e; intros x H; simpl in *; try solve_R; try apply continuous_at_id || apply continuous_at_const.
  - destruct H as [H1 H2]. apply continuous_at_plus; auto.
  - destruct H as [H1 H2]. apply continuous_at_minus; auto.
  - destruct H as [H1 H2]. apply continuous_at_mult; auto.
  - destruct H as [H1 [H2 H3]]. apply continuous_at_div; auto.
  - apply continuous_at_neg; auto.
  - replace (λ t : ℝ, sin (eval_expr e t)) with ((sin) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_sin]; auto.
  - replace (λ t : ℝ, cos (eval_expr e t)) with ((cos) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_cos]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, tan (eval_expr e t)) with ((tan) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_tan]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, cot (eval_expr e t)) with ((cot) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_cot]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, csc (eval_expr e t)) with ((csc) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_csc]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, sec (eval_expr e t)) with ((sec) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_sec]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, arcsin (eval_expr e t)) with ((arcsin) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_arcsin]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, arccos (eval_expr e t)) with ((arccos) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_arccos]; auto.
  - replace (λ t : ℝ, arctan (eval_expr e t)) with ((arctan) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_arctan]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, √ eval_expr e t) with ((R_sqrt.sqrt) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_sqrt]; auto.
  - replace (λ t : ℝ, exp (eval_expr e t)) with ((exp) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_exp]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, log (eval_expr e t)) with ((log) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe; auto | apply continuous_at_log; auto].
  - destruct H as [H1 H2]. replace (λ t : ℝ, eval_expr e t ^^ r) with ((λ y, y ^^ r) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe; auto | apply continuous_at_Rpower_const; auto].
  - destruct H as [H1 [H2 H3]]. apply continuous_at_Rpower_comp; auto.
  - replace (fun t : R => eval_expr e t ^ n) with ((fun y : R => pow y n) ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; [apply IHe | apply continuous_at_pow]; auto.
  - destruct H as [H1 H2]. replace (λ t : ℝ, f (eval_expr e t)) with (f ∘ (λ t : ℝ, eval_expr e t))%function by reflexivity.
    apply continuous_at_comp; auto.
Qed.

Lemma derive_correct : forall e x,
  wf_derive e x -> ⟦ der x ⟧ (λ t, eval_expr e t) = (λ t, eval_expr (derive_expr e) t).
Proof.
  induction e; simpl; try lra.
  - intros x _. apply derivative_at_id.
  - intros x _. apply derivative_at_const.
  - intros x [H1 H2]; apply derivative_at_plus; auto.
  - intros x [H1 H2]. apply derivative_at_minus; auto.
  - intros x [H1 H2]. apply derivative_at_mult; auto.
  - intros x [H1 [H2 H3]]. pose proof (derivative_at_div (eval_expr e1) (eval_expr (derive_expr e1)) (eval_expr e2) (eval_expr (derive_expr e2)) x) as H4.
    replace (λ t : ℝ, (eval_expr (derive_expr e1) t * eval_expr e2 t - eval_expr e1 t * eval_expr (derive_expr e2) t) / (eval_expr e2 t * (eval_expr e2 t * 1))) with
    (λ x : ℝ, (eval_expr (derive_expr e1) x * eval_expr e2 x - eval_expr (derive_expr e2) x * eval_expr e1 x) / (eval_expr e2 x * eval_expr e2 x)).
    2 : { extensionality t. rewrite Rmult_1_r. lra. }
    apply H4; auto.
  - intros x H1. apply derivative_at_neg; auto.
  - intros x H1.
    replace (λ t : ℝ, sin (eval_expr e t)) with ((sin) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, cos (eval_expr e t) * eval_expr (derive_expr e) t) with ((cos) ∘ (λ t : ℝ, eval_expr e t) ⋅ (λ t, eval_expr (derive_expr e) t))%function by reflexivity.
    apply derivative_at_comp.
    + apply IHe; auto.
    + apply derivative_at_sin.
  - intros x H1.
    replace (λ t : ℝ, cos (eval_expr e t)) with ((cos) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, - sin (eval_expr e t) * eval_expr (derive_expr e) t) with ((- sin) ∘ (λ t : ℝ, eval_expr e t) ⋅ (λ t, eval_expr (derive_expr e) t))%function by reflexivity.
    apply derivative_at_comp.
    + apply IHe; auto.
    + apply derivative_at_cos.
  - intros x [H1 H2].
    replace (λ t : ℝ, tan (eval_expr e t)) with ((tan) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, eval_expr (derive_expr e) t / (cos (eval_expr e t) * (cos (eval_expr e t) * 1))) with ((sec ^ 2) ∘ (λ t : ℝ, eval_expr e t) ⋅ (λ t, eval_expr (derive_expr e) t))%function.
    + apply derivative_at_comp; [apply IHe; auto | apply derivative_at_tan; auto ].
    + extensionality t. unfold compose, sec. assert (cos (eval_expr e t) = 0 \/ cos (eval_expr e t) <> 0) as [H3 | H3] by lra.
      * rewrite H3. unfold Rdiv; simpl; replace (0 * (0 * 1)) with 0 by ring; rewrite Rinv_0; ring.
      * field; auto.
  - intros x [H1 H2].
    change (fun t : R => cot (eval_expr e t)) with (compose cot (fun t => eval_expr e t)).
    eapply derivative_at_ext_val.
    + apply derivative_at_comp with (f' := fun t => eval_expr (derive_expr e) t) 
                                    (g' := fun y => - (csc y) ^ 2).
      * apply IHe; auto.
      * apply derivative_at_cot; auto.
    + unfold compose. reflexivity.
    
  - intros x [H1 H2].
    change (fun t : R => csc (eval_expr e t)) with (compose csc (fun t => eval_expr e t)).
    eapply derivative_at_ext_val.
    + apply derivative_at_comp with (f' := fun t => eval_expr (derive_expr e) t) 
                                    (g' := fun y => - csc y * cot y).
      * apply IHe; auto.
      * apply derivative_at_csc; auto.
    + unfold compose. lra.
  - intros x [H1 H2].
    change (fun t : R => sec (eval_expr e t)) with (compose sec (fun t => eval_expr e t)).
    eapply derivative_at_ext_val.
    + apply derivative_at_comp with (f' := fun t => eval_expr (derive_expr e) t) 
                                    (g' := fun y => sec y * tan y).
      * apply IHe; auto.
      * apply derivative_at_sec; auto.
    + unfold compose. reflexivity.
  - intros x [H1 H2].
    replace (λ t : ℝ, arcsin (eval_expr e t)) with ((arcsin) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, eval_expr (derive_expr e) t / √(1 - (eval_expr e t * (eval_expr e t * 1)))) with ((fun x => (1 / √(1 - x ^ 2))%R) ∘ (λ t : ℝ, eval_expr e t) ⋅ (λ t, eval_expr (derive_expr e) t))%function.
    + apply derivative_at_comp; [apply IHe; auto | apply derivative_at_arcsin; auto ].
    + extensionality t. unfold compose, Rdiv. simpl. lra.
  - intros x [H1 H2].
    replace (λ t : ℝ, arccos (eval_expr e t)) with ((arccos) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, - eval_expr (derive_expr e) t / √(1 - (eval_expr e t * (eval_expr e t * 1)))) with ((fun x => (-1 / √(1 - x ^ 2))%R) ∘ (λ t : ℝ, eval_expr e t) ⋅ (λ t, eval_expr (derive_expr e) t))%function.
    + apply derivative_at_comp; [apply IHe; auto | apply derivative_at_arccos; auto ].
    + extensionality t. unfold compose, Rdiv. simpl. lra.
  - intros x H1.
    replace (λ t : ℝ, arctan (eval_expr e t)) with ((arctan) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, eval_expr (derive_expr e) t / (1 + (eval_expr e t * (eval_expr e t * 1)))) with ((fun x => (1 / (1 + x ^ 2))%R) ∘ (λ t : ℝ, eval_expr e t) ⋅ (λ t, eval_expr (derive_expr e) t))%function.
    + apply derivative_at_comp; [apply IHe; auto | pose proof derivative_arctan as HH; unfold derivative in HH; apply HH].
    + extensionality t. unfold compose, Rdiv. simpl. lra.
  - intros x [H1 H2].
    apply derivative_at_sqrt_comp; auto.
  - intros x H1.
    replace (λ t : ℝ, exp (eval_expr e t)) with ((exp) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, exp (eval_expr e t) * eval_expr (derive_expr e) t) with ((exp) ∘ (λ t : ℝ, eval_expr e t) ⋅ (λ t, eval_expr (derive_expr e) t))%function by reflexivity.
    apply derivative_at_comp.
    + apply IHe; auto.
    + apply theorem_18_2.
  - intros x [H1 H2].
    replace (λ t : ℝ, log (eval_expr e t)) with ((log) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, eval_expr (derive_expr e) t / eval_expr e t) with (((fun y : R => (1 / y)%R) ∘ (λ t : ℝ, eval_expr e t)) ⋅ (λ t, eval_expr (derive_expr e) t))%function.
    2: { extensionality t. unfold compose. lra. }
    apply derivative_at_comp with (g := log) (g' := fun y => 1 / y).
    + apply IHe. exact H1.
    + apply derivative_log_x. exact H2.
  - intros x [H1 H2].
    replace (λ t : ℝ, eval_expr e t ^^ r) with ((λ y, y ^^ r) ∘ (λ t:ℝ, eval_expr e t))%function by reflexivity.
    replace (λ t : ℝ, r * eval_expr e t ^^ (r - 1) * eval_expr (derive_expr e) t) with (((fun y : R => (r * y ^^ (r - 1))%R) ∘ (λ t : ℝ, eval_expr e t)) ⋅ (λ t, eval_expr (derive_expr e) t))%function.
    2: { extensionality t. unfold compose. lra. }
    apply derivative_at_comp with (g := fun y => y ^^ r) (g' := fun y => r * y ^^ (r - 1)).
    + apply IHe. exact H1.
    + apply derivative_Rpower. exact H2.
  - intros x [H1 [H2 H3]]. apply derivative_at_Rpower_comp; auto.
  - intros x H1. destruct n.
    + replace (λ t, eval_expr e t ^ 0) with (fun t:ℝ => 1) by (extensionality t; simpl; lra).
      replace (λ t : ℝ, eval_expr (EConst 0) t) with (fun t:ℝ => 0) by (extensionality t; simpl; lra).
      apply derivative_at_const.
    + replace (fun t:ℝ => pow (eval_expr e t) (S n)) with ((fun y:ℝ => pow y (S n)) ∘ λ t, eval_expr e t)%function by reflexivity.
      replace (λ t : ℝ, eval_expr (EMul (EMul (EConst (S n)) (EPow e n)) (derive_expr e)) t) with (((λ y : ℝ, Rmult (INR (S n)) (y ^ (S n - 1))) ∘ λ t : ℝ, eval_expr e t) ⋅ eval_expr (derive_expr e))%function.
      1: { apply derivative_at_comp; [apply IHe; auto | apply derivative_at_pow]. }
      extensionality t. replace (S n - 1)%nat with n by lia. reflexivity.
  - intros x. destruct df.
    -- intros [H1 H2]. apply derivative_at_comp; auto.
    -- tauto.
Qed.

Lemma derive_correct_global : forall e,
  (forall x, wf_derive e x) -> ⟦ der ⟧ (fun x => eval_expr e x) = (fun x => eval_expr (derive_expr e) x).
Proof.
  intros e H1 x. apply derive_correct; auto.
Qed.

Lemma Der_correct_global : forall e,
  (forall x, wf_derive e x) -> 
  ⟦ Der ⟧ (fun x => eval_expr e x) = (fun x => eval_expr (derive_expr e) x).
Proof.
  intros e H1.
  apply derivative_imp_derive.
  apply derive_correct_global; auto.
Qed.

Ltac reify_constant c :=
  lazymatch type of c with
  | R => constr:(EConst c)
  | Z => let r := constr:(IZR c) in constr:(EConst r)
  | nat => let r := constr:(IZR (Z.of_nat c)) in constr:(EConst r)
  | positive => let z := constr:(Zpos c) in let r := constr:(IZR z) in constr:(EConst r)
  | _ => fail "reify_constant: Cannot parse term:" c
  end.

Ltac reify_expr x t :=
  lazymatch t with
  | x => constr:(EVar)
  | context[x] =>
      lazymatch t with
      | ?u + ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EAdd e1 e2)
      | ?u - ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(ESub e1 e2)
      | ?u * ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EMul e1 e2)
      | ?u / ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EDiv e1 e2)
      | - ?u    => let e := reify_expr x u in constr:(ENeg e)
      | sin ?u  => let e := reify_expr x u in constr:(ESin e)
      | cos ?u  => let e := reify_expr x u in constr:(ECos e)
      | tan ?u  => let e := reify_expr x u in constr:(ETan e)
      | cot ?u  => let e := reify_expr x u in constr:(ECot e)
      | csc ?u  => let e := reify_expr x u in constr:(ECsc e)
      | sec ?u  => let e := reify_expr x u in constr:(ESec e)
      | arcsin ?u => let e := reify_expr x u in constr:(EArcsin e)
      | arccos ?u => let e := reify_expr x u in constr:(EArccos e)
      | arctan ?u => let e := reify_expr x u in constr:(EArctan e)
      | sqrt ?u => let e := reify_expr x u in constr:(ESqrt e)
      | exp ?u  => let e := reify_expr x u in constr:(EExp e)
      | log ?u  => let e := reify_expr x u in constr:(ELog e)
      | ln ?u   => let e := reify_expr x u in constr:(ELog e)
      | ?u ^^ ?v => 
          let b := match v with | context[x] => constr:(true) | _ => constr:(false) end in
          lazymatch b with
          | true => 
              let e1 := reify_expr x u in 
              let e2 := reify_expr x v in 
              constr:(ERpower e1 e2)
          | false => 
              let e := reify_expr x u in constr:(ERpow e v)
          end
      | ?u ^ ?n => let e := reify_expr x u in constr:(EPow e n)
      | ?h ?u =>
          lazymatch type of h with
          | R -> R =>
              let e1 := reify_expr x u in 
              let df := match goal with | [ H1 : ⟦ der ⟧ h = ?g |- _ ] => constr:(Some g) | _ => constr:(@None (R -> R)) end in
              constr:(EApp h df e1)
          | _ => reify_constant t
          end
      end
  | _ => reify_constant t
  end.

Ltac change_fun_to_expr :=
  let reify_current f :=
    let x := fresh "x" in intros x;
    let fx := eval cbv beta in (f x) in
    let e := reify_expr x fx in
    instantiate (1 := fun y => eval_expr e y); reflexivity
  in
  lazymatch goal with
  | |- ⟦ lim ?a ⟧ ?f = ?L => eapply limit_ext; [ reify_current f | ]
  | |- ⟦ lim ?a⁺ ⟧ ?f = ?L => eapply right_limit_ext; [ reify_current f | ]
  | |- ⟦ lim ?a⁻ ⟧ ?f = ?L => eapply left_limit_ext; [ reify_current f | ]
  | |- continuous_at ?f ?a => eapply continuous_at_ext; [ reify_current f | ]
  end.

Ltac change_deriv_to_eval :=
  match goal with
  | [ |- ⟦ der ⟧ _ = _ ] => eapply derivative_eq
  | [ |- ⟦ der _ ⟧ _ = _ ] => eapply derivative_at_eq'
  end;
  [ let x := fresh "x" in intros x;
    match goal with 
    | [ |- _ = ?rhs ] =>
      let rhs_unfolded := eval unfold compose in rhs in
      let fx := eval cbv beta in rhs_unfolded in
      let e := reify_expr x fx in
      instantiate (1 := fun t => eval_expr e t); simpl; reflexivity
    end
  | idtac ].

Lemma ln_fun_eq : ln = log.
Proof. extensionality x. apply ln_eq_log. Qed.

Ltac normalize_math_funs :=
  try rewrite ln_fun_eq in *.

Ltac eval_math_constants :=
  try rewrite sin_0 in *;
  try rewrite cos_0 in *;
  try rewrite exp_0 in *;
  try rewrite log_1 in *;
  try rewrite ln_1 in *;
  try rewrite log_e in *;
  try rewrite ln_e in *.

Ltac solve_denoms :=
  simpl in *;
  try match goal with
  | [ H : ?v ∈ (?lo, ?hi) |- _ ] => 
      unfold "∈" in H; destruct H 
  end;
  try (nra || lra || solve_R);
  match goal with
  | |- ?X <> 0 => apply Rgt_not_eq; solve_denoms
  | |- ?X <> 0 => apply Rlt_not_eq; solve_denoms
  | |- 0 < √( ?X ) => apply sqrt_lt_R0; solve_denoms
  | |- 0 < exp ?X => apply exp_pos
  | |- exp ?X <> 0 => apply exp_neq_0
  | |- 0 < e => unfold e; apply exp_pos
  | |- e > 0 => unfold e; apply exp_pos
  | |- e <> 0 => unfold e; apply exp_neq_0
  | |- 0 < ?X ^ 2 => apply pow2_gt_0; solve_denoms
  | |- 0 < ?X ^^ ?Y => apply Rpower_gt_0; solve_denoms
  | |- ?X ^^ ?Y > 0 => apply Rpower_gt_0; solve_denoms
  | |- 0 < 1 + ?X => assert (0 < X) by solve_denoms; lra
  | |- 1 + ?X > 0 => assert (0 < X) by solve_denoms; lra
  | |- 0 < log (1 + ?X) => apply log_pos; assert (0 < X) by solve_denoms; lra
  | |- log (1 + ?X) > 0 => apply log_pos; assert (0 < X) by solve_denoms; lra
  | |- 0 < log ?X => apply log_pos; solve_denoms
  | |- log ?X > 0 => apply log_pos; solve_denoms
  | |- 0 < sin ?X => apply sin_gt_0; solve_denoms
  | |- sin ?X > 0 => apply sin_gt_0; solve_denoms
  | |- 0 < arcsin ?X => apply arcsin_pos; solve_denoms
  | |- arcsin ?X > 0 => apply arcsin_pos; solve_denoms
  | |- 0 < π => try pose proof π_pos; lra
  | |- π > 0 => try pose proof π_pos; lra
  | |- 0 < PI => try pose proof PI_RGT_0; lra
  | |- PI > 0 => try pose proof PI_RGT_0; lra
  end;
  try (nra || lra || solve_R).

Ltac diff_simplify :=
  simpl; 
  try unfold e in *;
  try eval_math_constants;
  try rewrite <- ln_fun_eq in *;
  try rewrite ln_exp in *;
  try solve [lra | nra]; 
  try field; 
  repeat split; 
  try solve_denoms.

Hint Resolve derivative_Rpower_base : core.

Ltac auto_limit :=
  intros;
  try solve [ solve_R ];
  normalize_math_funs;
  change_fun_to_expr;
  match goal with
  | [ |- ⟦ lim ?a ⟧ (fun x => eval_expr ?e x) = ?L ] => 
      apply limit_subst with (L1 := eval_expr e a);
      [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R 
      | apply limit_eval_expr; repeat split;
        try solve [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R | auto ] 
      ]
  | [ |- ⟦ lim ?a⁺ ⟧ (fun x => eval_expr ?e x) = ?L ] => 
      apply limit_right_subst with (L1 := eval_expr e a);
      [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R 
      | apply right_limit_eval_expr; repeat split;
        try solve [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R | auto ] 
      ]
  | [ |- ⟦ lim ?a⁻ ⟧ (fun x => eval_expr ?e x) = ?L ] => 
      apply limit_left_subst with (L1 := eval_expr e a);
      [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R 
      | apply left_limit_eval_expr; repeat split;
        try solve [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R | auto ] 
      ]
  end.

Ltac auto_cont :=
  intros;
  try solve [ solve_R ];
  normalize_math_funs;
  try (match goal with 
  | [ |- continuous_on ?f ?I ] => apply continuous_at_imp_continuous_on; let a := fresh "a" in let H := fresh "H" in intros a H 
  | [ |- continuous ?f ] => let a := fresh "a" in intros a 
  end);
  change_fun_to_expr;
  match goal with
  | [ |- continuous_at (fun x => eval_expr ?e x) ?a ] =>
      apply cont_correct;
      repeat split; try solve [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R | auto ]
  end.

Ltac auto_diff :=
  intros;
  try solve [ solve_R ];
  normalize_math_funs;
  
  try match goal with 
  | [ |- ⟦ der ⟧ (fun t => ∫ ?a t ?f) = _ ] => 
      apply FTC1_global; try auto_cont
  | [ |- ⟦ der ⟧ (fun t => ∫ t ?b ?f) = _ ] => 
      apply FTC1'_global; try auto_cont
  end;

  try (match goal with 
       | [ |- ⟦ der ⟧ _ ?D = _ ] => 
           apply derivative_at_imp_derivative_on; 
           [ try apply differentiable_domain_open; 
             try apply differentiable_domain_closed; 
             try apply differentiable_domain_gt; 
             try apply differentiable_domain_lt; 
             try solve [ simpl; try eval_math_constants; try solve_denoms; try lra; solve_R ]
           | let x := fresh "x" in let H1 := fresh "H" in intros x H1 ] 
       end);
       
  try change_deriv_to_eval;
  
  match goal with
  | [ |- ⟦ der ?y ⟧ (fun t => eval_expr ?e t) = ?rhs ] =>
      apply derivative_at_ext_val with (f' := fun t => eval_expr (derive_expr e) t);
      [ apply derive_correct; 
        simpl in *; try eval_math_constants;
        repeat split; 
        try solve [ try solve_denoms; try lra; solve_R | auto ]
      | unfold compose in *; try diff_simplify ]

  | [ |- ⟦ der ⟧ (fun t => eval_expr ?e t) = ?rhs ] =>
      replace rhs with (fun t => eval_expr (derive_expr e) t);
      [ apply derive_correct_global; 
        simpl in *; try eval_math_constants;
        repeat split; 
        try solve [ try solve_denoms; try lra; solve_R | auto ]
      | let x := fresh "x" in extensionality x; unfold compose in *; try diff_simplify ]
  end.

Ltac compute_Der :=
  repeat match goal with
  | |- context [ nth_derive_at ?n ?f ?a ] => change (nth_derive_at n f a) with ((nth_derive n f) a)
  end;
  repeat rewrite nth_derive_succ;
  repeat rewrite nth_derive_1;
  repeat rewrite nth_derive_0;

  repeat match goal with
  | |- context [ derive ?f ] =>
      lazymatch f with
      | context [ derive ] => fail
      | _ => idtac
      end;
      let e_ast := match constr:(fun x : R => ltac:(
          let fx := eval cbv beta in (f x) in
          let e := reify_expr x fx in
          exact e
      )) with fun _ => ?e => e end in
      change (derive f) with (derive (fun y => eval_expr e_ast y));
      rewrite (Der_correct_global e_ast);
      [ cbv [eval_expr derive_expr] 
      | intro; simpl; try eval_math_constants; repeat split; 
        try solve [try solve_denoms; try lra; solve_R]; auto ]
  end;
  
  simpl; try eval_math_constants.

Ltac compute_tp :=
  intros;
  autounfold with taylor_polynomial;
  repeat rewrite sum_f_i_Sn_f; try lia;
  try rewrite sum_f_0_0; try lia;
  compute_Der;
  try solve_R.

Module Tactic_Tests.

Example FTC2_test : ∫ 0 1 (λ x : ℝ, 2 * x) = 1.
Proof.
  set (f := λ x : ℝ, 2 * x).
  set (g := λ x : ℝ, x^2).
  assert (H1 : 0 < 1) by lra.
  assert (H2 : continuous_on f [0, 1]). { unfold f. auto_cont. }
  assert (H3 : ⟦ der ⟧ g [0, 1] = f) by (unfold f, g; auto_diff).
  replace 1 with (g 1 - g 0) at 2 by (unfold g; lra).
  apply (FTC2 0 1 f g H1 H2 H3).
Qed.

Lemma integral_sin5_cos : ∫ (λ x, sin x ^ 5 * cos x) = (λ x, sin x ^ 6 / 6).
Proof.
  unfold antiderivative; auto_diff.
Qed.

Lemma test_auto_cont : continuous (λ x, sin (x^2 + 1)).
Proof.
  auto_cont.
Qed.

Lemma test_auto_cont_2 : continuous_on (λ x: ℝ, 1/x) (0, 1).
Proof.
  auto_cont.
Qed.

End Tactic_Tests.

Module Tactic_Tests_Advanced.

Lemma test_auto_diff_rpower : ⟦ der ⟧ (fun x => x ^^ 5) (1, 2) = (fun x => 5 * x ^^ 4).
Proof.
  auto_diff.
  replace (5 - 1) with 4 by lra. lra.
Qed.

Lemma test_auto_diff_ln : ⟦ der ⟧ (fun x => ln (x + 1)) (0, 1) = (fun x => 1 / (x + 1)).
Proof.
  auto_diff.
Qed.

Lemma stress_diff_quotient :
  ⟦ der ⟧ (fun x => (arcsin x * ln (x + 1)) / (x^2 + 1)) (-0.5, 0.5) =
  (fun x => ((1 / √(1 - x^2) * ln (x + 1) + arcsin x * (1 / (x + 1))) * (x^2 + 1) -
  (arcsin x * ln (x + 1)) * (2 * x)) / ((x^2 + 1) ^ 2)).
Proof.
  auto_diff. 
Qed.

Lemma stress_limit_huge : ⟦ lim 0 ⟧ (fun x => (sin x + cos x) / exp x) = 1.
Proof.
  auto_limit.
Qed.

Lemma test_exp : ⟦ der ⟧ (fun x => e ^^ x) = (fun x => e ^^ x).
Proof.
  auto_diff.
Qed.

Lemma derivative_exp_neg : ⟦ der ⟧ (fun x => e ^^ (- x)) = (fun x => - e ^^ (- x)).
Proof.
  auto_diff.
Qed.

Lemma integral_tan_local : 
  ⟦ der ⟧ (fun x => - ln (cos x)) (-1, 1) = (fun x => tan x).
Proof.
  auto_diff.
  - admit.
  -
  unfold tan.
  field.
  admit.
Abort.

End Tactic_Tests_Advanced.