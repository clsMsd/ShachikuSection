# 関数論理プログラミング言語 Curry

Curry は関数型と論理型の両方の性質を持つプログラミング言語。

- Curry, https://www-ps.informatik.uni-kiel.de/currywiki/

> Curry is a universal programming language aiming to amalgamate the most important declarative programming paradigms, namely functional programming and logic programming. 

次のような特徴を持つ。

- functional programming (nested expressions, higher-order functions, lazy evaluation),
- logic programming (logical variables, partial data structures, built-in search), 
- concurrent programming (concurrent evaluation of expressions with synchronization on logical variables).

Curry の処理系として PAKCS という実装がある。
PAKCS は Curry プログラムを Prolog にコンパイルする。

- PACKS, https://www.informatik.uni-kiel.de/~pakcs/

```
  ______      __       _    _    ______   _______     
 |  __  |    /  \     | |  / /  |  ____| |  _____|   Portland Aachen Kiel
 | |  | |   / /\ \    | |_/ /   | |      | |_____    Curry System
 | |__| |  / /__\ \   |  _  |   | |      |_____  |   
 |  ____| / ______ \  | | \ \   | |____   _____| |   Version 2.1.1
 |_|     /_/      \_\ |_|  \_\  |______| |_______|   
 ***WITH TYPECLASSES***

Curry2Prolog(swi 8.0) Compiler Environment (Version of 2019-03-17)
(RWTH Aachen, CAU Kiel, Portland State University)

Type ":h" for help (contact: pakcs@curry-language.org)
Prelude> 
```

Curry では `free varialbe` という記法があり、式の中で未定の変数を使うことができる。
次のように `where ... free` で `free varialbe` を宣言することができる。

```
Prelude> x && (y || (not x)) where x,y free
{x=True, y=True} True
{x=True, y=False} False
{x=False, y=y} False
```

`free varialbe` を含む式を評価すると、それらの変数が取り得る値を探索して、すべての場合の結果が返ってくる。

また、式の中で制約を定義することで、制約を満たす解を導くことができる。
例えば、次のように `e1 =:= e2` という等号制約を含む式を評価すると、`2+3` と `x` が同じ値になるような値 `x` が導き出される。

```
Prelude> 2+3=:=x where x free
{x=5} True
```

上で見たBooleanの式も、結果が `True` になる場合の `free varialbe` の組み合わせを以下のように導き出せる。

```
Prelude> (x && (y || (not x))) =:= True where x,y free
{x=True, y=True} True
```

Curryの他の特徴として `non-deterministic operations` がある。
例えば、次のように複数の結果を返す関数を定義することができる。

```
choose x y = x
choose x y = y
```

`choose` を評価すると複数の結果が返ってくる。

```
test> choose 1 2
1
2
```

上で定義した `choose` は built-in で `?` として定義されている。

これを使うと、`x ∈ {1, 2, 3}` の中から `x + x = x ∗ x` を満たす `x` を導き出す式を以下のように書ける。

```
Prelude> x =:= (1 ? 2 ? 3) & x+x =:= x*x where x free
{x=2} True
```

List型の値に対しても `free varialbe` を使うことができる。
`++` はList同士の結合関数。

```
Prelude> [1,2,3] ++ [e] =:= [1,2,3,4] where e free
{e=4} True
```

Listの最後の値を返す `last` 関数は次のように定義できる。

```
last xs | xs =:= _ ++ [e] = e where e free
```

実行結果は以下の通り。

```
test> last [1,2,3,4]
4
```

また、`last` 関数は以下のように引数のパターンマッチに `++` が現れる形でも書くことができる。

```
last (_ ++ [e]) = e
```


# 参考
- Curry A Tutorial Introduction, https://www.informatik.uni-kiel.de/~curry/tutorial/tutorial.pdf
