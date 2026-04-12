#!/bin/bash
f="Calculus/Chapter18/Problem_18_4/fc.gp"
base="fc"
func="fc(x) = exp x + exp(-x)"

extra_plots=", exp(x) title 'exp x' with lines linecolor rgb 'green', exp(-x) title '1/exp x' with lines linecolor rgb 'blue'"
sed "s|notitle with filledcurves|title '${func}' with filledcurves${extra_plots}|" "$f" | grep plot
