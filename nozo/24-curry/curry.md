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

# 参考
- Curry A Tutorial Introduction, https://www.informatik.uni-kiel.de/~curry/tutorial/tutorial.pdf
