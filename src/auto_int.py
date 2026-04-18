import sympy
import sys
import argparse

def to_prefix_lines(expr):
    if isinstance(expr, sympy.Symbol):
        return ["EVar"]
    elif isinstance(expr, sympy.Number):
        if expr.is_Integer:
            if expr < 0:
                return ["ENeg", "EConst", str(-expr)]
            return ["EConst", str(expr)]
        elif expr.is_Rational:
            p, q = expr.p, expr.q
            lines = ["EDiv"]
            if p < 0:
                lines.extend(["ENeg", "EConst", str(-p)])
            else:
                lines.extend(["EConst", str(p)])
            lines.extend(["EConst", str(q)])
            return lines
        else:
            return ["EConst", str(float(expr))]
    elif isinstance(expr, sympy.Add):
        args = expr.args
        lines = to_prefix_lines(args[0])
        for arg in args[1:]:
            lines = ["EAdd"] + lines + to_prefix_lines(arg)
        return lines
    elif isinstance(expr, sympy.Mul):
        args = expr.args
        lines = to_prefix_lines(args[0])
        for arg in args[1:]:
            lines = ["EMul"] + lines + to_prefix_lines(arg)
        return lines
    elif isinstance(expr, sympy.Pow):
        base_lines = to_prefix_lines(expr.base)
        if expr.exp.is_Integer:
            n = expr.exp
            if n > 0:
                return ["EPow"] + base_lines + [str(n)]
            elif n < 0:
                return ["EDiv", "EConst", "1", "EPow"] + base_lines + [str(-n)]
            else:
                return ["EConst", "1"]
        elif expr.exp == sympy.Rational(1, 2):
            return ["ESqrt"] + base_lines
        elif expr.exp == sympy.Rational(-1, 2):
            return ["EDiv", "EConst", "1", "ESqrt"] + base_lines
        elif expr.exp.is_Rational:
            return ["ERpow"] + base_lines + [f"{expr.exp.p}/{expr.exp.q}"]
        else:
            exp_lines = to_prefix_lines(expr.exp)
            return ["ERpower"] + base_lines + exp_lines
    elif isinstance(expr, sympy.sin):
        return ["ESin"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.cos):
        return ["ECos"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.tan):
        return ["ETan"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.cot):
        return ["ECot"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.sec):
        return ["ESec"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.csc):
        return ["ECsc"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.asin):
        return ["EArcsin"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.acos):
        return ["EArccos"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.atan):
        return ["EArctan"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.exp):
        return ["EExp"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.log):
        return ["ELog"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.StrictGreaterThan):
        return []
    else:
        raise ValueError(f"Unknown expression type: {type(expr)} for {expr}")

def main():
    if len(sys.argv) != 3:
        print("Usage: python auto_int.py <in.txt> <out.txt>")
        sys.exit(1)
        
    in_file = sys.argv[1]
    out_file = sys.argv[2]

    with open(in_file, 'r') as f:
        expr_str = f.read().strip()
    
    x = sympy.Symbol('x')
    f = sympy.sympify(expr_str)
    
    F = sympy.integrate(f, x)
    
    lines = to_prefix_lines(F)
    
    with open(out_file, 'w') as f:
        for line in lines:
            f.write(line + "\n")

if __name__ == "__main__":
    main()
