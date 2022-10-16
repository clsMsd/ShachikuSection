# Alloy

> Alloy is a language for describing structures and a tool for exploring them. It has been used in a wide range of applications from finding holes in security mechanisms to designing telephone switching networks.
> 
> https://alloytools.org/about.html

```Alloy
sig File, Dir {}
```

`sig`で宣言されるシグネチャはオブジェクトの集合を表す。

```Alloy
sig File {}
sig Dir {
    contents : set File
}
```

集合`Dir`と集合`File`の間の関係(relation)として`contents`が定義される。

集合多重度
- set 任意個
- one ちょうど1個
- lone 0か1個
- some 1個以上

```Alloy
abstract sig Object {}

sig File extends Object {}
sig Dir extends Object {
    contents : set Object
}

pred SomeDirInDir {
    some disj d1, d2 : Dir | d1.contents = d2
}
run SomeDirInDir
```

`sig A extends B`という宣言は、AがBの部分集合であることを示す。

`abstract`で宣言されたシグネチャは、それ自身は要素を持たないことを示す。

`pred`は述語の宣言であり、Alloyで検査したい制約を定義する。

`run`コマンドは、与えられた述語の充足例を探索するコマンド。

`.`は関係演算子で、関係の結合を表す。

```Alloy
abstract sig Object {}

sig File extends Object {}
sig Dir extends Object {
    contents : set Object
}

assert SomeDir {
    all o : Object | some contents.o
}
check SomeDir
```
```
Starting the solver...

Executing "Check SomeDir"
Solver=sat4j Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
Generating CNF...
146 vars. 18 primary vars. 214 clauses. 1ms.
Solving...
Counterexample found. Assertion is invalid. 2ms.
```

```Alloy
abstract sig Object {}

sig File extends Object {}
sig Dir extends Object {
    contents : set Object
}

one sig Root extends Dir {}

fact {
    all o : Object | o in Root.(*contents)
}

assert SomeDir {
    all o : Object - Root | some contents.o
}
check SomeDir
```
```
Starting the solver...

Executing "Check SomeDir"
Solver=sat4j Bitwidth=4 MaxSeq=4 SkolemDepth=1 Symmetry=20 Mode=batch
Generating CNF...
No counterexample found. Assertion may be valid. 0ms.
```

# 参考
- https://alloytools.org/about.html
- 抽象によるソフトウェア設計 ― Alloyではじめる形式手法 第1版, https://www.ohmsha.co.jp/book/9784274068584/
- http://softwareabstractions.org/models/a4-models-index.html
