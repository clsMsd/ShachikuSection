# Scheme入門

## 基礎文法
Scheme(Lisp)のプログラムは、S式と呼ばれるデータ構造で表現される。  

### Hello World
```scheme
(print "Hello World")
```

S式は `(値1 値2 値3 ...)` のように、カッコの中に空白区切りで値を書いてリストを表現したものである。   
リストの先頭に当たる`値1`(上のプログラムでは`print`)には基本的に関数が来て、関数に引数として`値2``値3`...を適用したものがS式全体を評価した値となる。  
(`print`を評価した結果は`undef`なので、上のS式を評価した結果は`undef`になる)

### 四則演算
Schemeでは演算子と関数は特に区別しない。  
```scheme
(+ 1 2 3) ;=> 6
```

演算が全てカッコで区切られるので優先順位の問題が発生しない。  
```scheme
(+ 1 (* 2 3) (- 5 4)) ;=> 1 + (2 * 3) + (5 - 4) = 8 
```

比較も同じように書く。
```scheme
(< 1 2) ;=> #t (真)
(= 1 2) ;=> #f (偽)
```

### if式
`(if cond then_value eles_value)` のように書き、  
式を評価すると`cond`が偽(`#f`)でないなら`then_value`に、偽なら`else_value`に評価される。  

真偽値として`#t`と`#f`の2つの値があるが、`#f`以外の値は全て真として扱われることに注意。  

```scheme
(if 1 2 3) ;=> 2
(if #f 2 3) ;=> 3
```

### 変数
`define`で変数を定義することができる。  
```scheme
(define a 42)

(print a) ;=> 42
```

`set!`で変数に再代入することができる。 
```scheme
(define a 42)
(set! a 43)
(print a) ;=> 43
```

変数は厳密にはシンボルという。  
シンボルは評価されるとシンボルに紐付いた値になるので、上の例で`a`を評価すると`a`に紐付いた値である`43`に評価される  
(このような、シンボルと値の対応関係のことを環境という)。  
上で出てきた `print` や `+` や `define` といった 関数、演算子、予約語っぽいものも実は全てシンボルである  
(というか、Schemeに予約語は存在しない)。  

シンボルは別のシンボルを紐付けることもできるので、次のようなこともできる。   
```scheme
(define 定義 define)
(定義 再定義 set!)
(定義 足す +)
(定義 表示 print)
(定義 もし if)

(定義 変数ア 0)
(再定義 変数ア 2)

(表示 (足す 変数ア 40)) ;=> 42
```

シンボルを、シンボルに紐付いた値としてではなくシンボルそのものとして評価したい場合、`\``を付ける。  
```scheme
(print `x) ;=> x
```

### 関数
`lambda`で関数を作ることができる。  

```scheme
((lambda (a b) (+ a b)) 1 2) ;=> 3
```

関数もシンボルに紐付けることができるので、次のように書ける。  
```scheme
(define add (lambda (a b) (+ a b)))
(add 1 2) ;=> 3
```

再帰も普通にできる。  
```scheme
(define fact
   (lambda (n)
      (if
         (= n 0)
         1
         (* n (fact (- n 1)))
      )
   )
)

(fact 5) ;=> 120
```

クロージャも使える。
```scheme 
(define make-coutner
   (lambda (n)
      (lambda ()
         (set! n (+ n 1))
         n
      )   
   )
)

(define coutner (make-coutner 0))
(coutner) ;=> 1
(coutner) ;=> 2
(coutner) ;=> 3
```

## Lisp処理系を作ろう!
Lispは特に処理系を実装しやすい言語として知られている。  
というのも、ソースをS式で書くのである意味最初からパース済みというか構文木になっていると考えられ、
演算子の優先順位などに悩むことが無いし、パーサが簡単に書けるからである
(実際言語によっては処理系の中間表現としてS式を採用しているものもある(WebAssemblyなど))。 
実際世の中には42種類の言語でLisp処理系を実装したとかいう猛者もいる
([https://github.com/zick?tab=repositories])。 

まあそれでもSchemeをちゃんとに実装しようとすると静的スコープや第一級継続や末尾再帰の最適化やGCなど
いろいろ面倒くさいものがある。
そこで今回はとりあえず四則演算ができて変数や関数が使える程度のクッソ簡単なLisp処理系をPythonで作ってみよう。
([http://www.aoky.net/articles/peter_norvig/lispy.htm])

```python
def tokenize(src):
    return src.replace("(", " ( ").replace(")", " ) ").split()
```

```python
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
```

次はS式のパーサーを作る。  
S式の文法はBNFで書くと次のようになるので、再帰下降法でパースすればよい。  
```
S_Expr ::= List | Atom
List ::= "(" S_Expr* ")"
Atom ::= Number | Symbol
```

```python
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
```

次に環境を表すクラスをつくる。  
```python
class Env(dict):
    def __init__(self, parms=(), args=(), outer=None):
        self.update(zip(parms, args))
        self.outer = outer

    def find(self, var):
        if var in self:
            return self
        else:
            return self.outer.find(var)
```

次に四則演算等の基本的な関数を作る。  
Lispの四則演算等は基本的に可変長引数なのでちょっと面倒だが、Pythonの可変長引数とうまいこと使うと次のように書ける。  
```python
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
```

後はS式を評価する関数をつくる。
```python
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
```

後は標準入力を受け取って評価して表示するのを繰り返せばよい。  
```python
if __name__ == "__main__":
    while True:
        print(eval(parse(tokenize(input("> ")))))
```
