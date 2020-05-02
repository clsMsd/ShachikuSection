
def tokenize(src):
    return src.replace("(", " ( ").replace(")", " ) ").split()

def to_atom(tk):
    try:
        return int(tk)
    except ValueError:
        pass
    try:
        return float(tk)
    except ValueError:
        pass
    return str(tk)

def parse(tokens):
    p = 0
    def head():
        return tokens[p]
    def consume():
        nonlocal p
        p += 1

    def s_exrp():
        if head() == "(":
            consume()
            return lst()
        else:
            return atom()

    def atom():
        res = to_atom(head())
        consume()
        return res
    
    def lst():
        res = []
        while head() != ")":
            res.append(s_exrp())
        consume()
        return res
    
    return s_exrp()

class Env(dict):
    def __init__(self, parms=(), args=(), outer=None):
        self.update(zip(parms, args))
        self.outer = outer

    def find(self, var):
        if var in self:
            return self
        else:
            return self.outer.find(var)

from functools import reduce
GEnv = Env()
GEnv.update({
    "+": lambda *x: sum(x),
    "-": lambda *x: reduce(lambda a, b: a - b, x, x[0] * 2),
    "*": lambda *x: reduce(lambda a, b: a * b, x, 1),
    "/": lambda *x: reduce(lambda a, b: a / b, x, x[0] * x[0]),
    "=": lambda *x: len(set(x)) == 1,
    "eq?": lambda x, y: x is y,
    "<": lambda *x: x[0] < x[1],
    ">": lambda *x: x[0] > x[1],
    "not": lambda x: not x,
    "cons": lambda x, y: [x] + [y],
    "car": lambda x: x[0],
    "cdr": lambda x: x[1:],
    "list": lambda *x: x,
    "null?": lambda *x: len(x) == 0, 
    "print": lambda *x: print(x),
    "#t": True,
    "#f": False,
})

def eval(x, env=GEnv):
    if isinstance(x, str):
        return env.find(x)[x]
    elif not isinstance(x, list):
        return x
    elif x[0] == "quote":
        (_, expr) = x
        return expr 
    elif x[0] == "if":
        (_, cond, texpr, eexpr) = x
        cond = eval(cond, env)
        if cond:
            return eval(texpr, env)
        else:
            return eval(eexpr, env)
    elif x[0] == "define":
        (_, var, expr) = x
        env[var] = eval(expr, env)
    elif x[0] == "set!":
        (_, var, expr) = x
        env.find(var)[var] = eval(expr, env)
    elif x[0] == "lambda":
        (_, vars, expr) = x
        return lambda *args: eval(expr, Env(vars, args, env))
    else:
        exprs = [eval(e, env) for e in x]
        proc = exprs.pop(0)
        return proc(*exprs)

if __name__ == "__main__":
    while True:
        print(eval(parse(tokenize(input("> ")))))
