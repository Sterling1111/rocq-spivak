import sympy
import sys

def to_prefix_lines(expr):
    if isinstance(expr, sympy.Symbol):
        if expr != sympy.Symbol("x"):
            raise ValueError(f"Unsupported symbol: {expr}")
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
            raise ValueError(f"Inexact numeric primitive: {expr}")
    elif isinstance(expr, (sympy.Add, sympy.Mul)):
        # Keep the existing left-associated tree without repeatedly copying it.
        token = "EAdd" if isinstance(expr, sympy.Add) else "EMul"
        lines = [token] * (len(expr.args) - 1)
        for arg in expr.args:
            lines.extend(to_prefix_lines(arg))
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
            p, q = expr.exp.p, expr.exp.q
            if q == 2:
                n = abs(p) // 2
                rem = abs(p) % 2
                if n == 0:
                    pos_lines = ["ESqrt"] + base_lines
                elif n == 1:
                    if rem == 1:
                        pos_lines = ["EMul"] + base_lines + ["ESqrt"] + base_lines
                    else:
                        pos_lines = base_lines
                else:
                    if rem == 1:
                        pos_lines = ["EMul", "EPow"] + base_lines + [str(n), "ESqrt"] + base_lines
                    else:
                        pos_lines = ["EPow"] + base_lines + [str(n)]
                
                if p < 0:
                    return ["EDiv", "EConst", "1"] + pos_lines
                else:
                    return pos_lines
            return ["ERpow"] + base_lines + [f"{p}/{q}"]
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
    elif isinstance(expr, sympy.sinh):
        return ["ESinh"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.cosh):
        return ["ECosh"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.tanh):
        return ["ETanh"] + to_prefix_lines(expr.args[0])
    elif isinstance(expr, sympy.log):
        return ["ELog"] + to_prefix_lines(expr.args[0])
    else:
        raise ValueError(f"Unknown expression type: {type(expr)} for {expr}")

def integrate(expr_str):
    """Return a candidate only; Rocq checks its derivative and domain."""
    x = sympy.Symbol('x')
    f = sympy.sympify(expr_str)
    return to_prefix_lines(sympy.integrate(f, x))


def serve():
    # One line per request/response; errors leave the stream synchronized.
    for line in sys.stdin:
        try:
            response = "OK " + " ".join(integrate(line.strip()))
        except Exception as exc:
            response = "ERROR " + " ".join(str(exc).split())
        print(response, flush=True)


def main():
    if sys.argv[1:] == ["--server"]:
        serve()
    elif len(sys.argv) == 3:
        with open(sys.argv[1]) as source:
            lines = integrate(source.read().strip())
        with open(sys.argv[2], 'w') as output:
            output.write("\n".join(lines) + "\n")
    else:
        sys.exit("Usage: python auto_int.py <in.txt> <out.txt> | --server")


if __name__ == "__main__":
    main()
