From Calculus.Chapter11 Require Import Prelude.

Definition f_i x := x + 1 / x.
Definition f_ii x := x + 3 / x^2.
Definition f_iii x := x^2 / (x^2 - 1).
Definition f_iv x := 1 / (1 + x^2).

Definition p_i_neg := ltac:(plot f_i (-5) (-1/10) with (i_size 2000 1000)).
Definition p_i_pos := ltac:(plot f_i (1/10) 5 with (i_size 2000 1000)).

Definition p_ii_neg := ltac:(plot f_ii (-5) (-1/10) with (i_size 2000 1000)).
Definition p_ii_pos := ltac:(plot f_ii (1/10) 5 with (i_size 2000 1000)).

Definition p_iii_left := ltac:(plot f_iii (-5) (-11/10) with (i_size 2000 1000)).
Definition p_iii_mid := ltac:(plot f_iii (-9/10) (9/10) with (i_size 2000 1000)).
Definition p_iii_right := ltac:(plot f_iii (11/10) 5 with (i_size 2000 1000)).

Definition p_iv := ltac:(plot f_iv (-5) 5 with (i_size 2000 1000)).

Plot p_i_neg as "Calculus/Chapter11/Problem3/f_i_neg.gp".
Plot p_i_pos as "Calculus/Chapter11/Problem3/f_i_pos.gp".
Plot p_ii_neg as "Calculus/Chapter11/Problem3/f_ii_neg.gp".
Plot p_ii_pos as "Calculus/Chapter11/Problem3/f_ii_pos.gp".
Plot p_iii_left as "Calculus/Chapter11/Problem3/f_iii_left.gp".
Plot p_iii_mid as "Calculus/Chapter11/Problem3/f_iii_mid.gp".
Plot p_iii_right as "Calculus/Chapter11/Problem3/f_iii_right.gp".
Plot p_iv as "Calculus/Chapter11/Problem3/f_iv.gp".
