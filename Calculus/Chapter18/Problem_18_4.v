From Calculus.Chapter18 Require Import Prelude.
From Interval Require Import Plot Tactic.
Open Scope R_scope.

Local Notation exp := Rtrigo_def.exp.
Local Notation sin := Rtrigo_def.sin.

Definition fa x := exp(x + 1).
Definition fb x := exp(sin x).
Definition fc x := exp x + exp(-x).
Definition fd x := exp x - exp(-x).
Definition fe x := (fd x) / (fc x).

Definition fc_prime x := exp x - exp(-x).
Definition fd_prime x := exp x + exp(-x).

Definition pa := ltac:(plot fa (-3) 1).
Definition pb := ltac:(plot fb (-10) 5).
Definition pc := ltac:(plot fc (-2) 2).
Definition pd := ltac:(plot fd (-2) 2).
Definition pe := ltac:(plot fe (-3) 3).

Definition pc_prime := ltac:(plot fc_prime (-3) 3).
Definition pd_prime := ltac:(plot fd_prime (-3) 3).

Plot pa as "Calculus/Chapter18/Problem_18_4/fa.gp".
Plot pb as "Calculus/Chapter18/Problem_18_4/fb.gp".
Plot pc as "Calculus/Chapter18/Problem_18_4/fc.gp".
Plot pd as "Calculus/Chapter18/Problem_18_4/fd.gp".
Plot pe as "Calculus/Chapter18/Problem_18_4/fe.gp".
