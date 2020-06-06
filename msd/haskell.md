# Haskell入門

## はじめに
> Haskell is a general-purpose, statically typed, purely functional programming language with type inference and lazy evaluation.
> Developed to be suitable for teaching, research and industrial application, Haskell has pioneered a number of advanced programming language features.
> Type classes, for example, enable type-safe operator overloading, were first proposed by Philip Wadler and Stephen Blott for Standard ML and were first implemented in Haskell.
>  Haskell's main implementation is the Glasgow Haskell Compiler. It is named after logician Haskell Curry. [Cited from Wikipedia]

特徴として
- 強い静的型付け
- 純粋関数型
- 遅延評価
が挙げられる。  

最大の特徴として、副作用全般をモナドと呼ばれる型クラスを通して扱うというものがある。  
この特徴のおかげで、プログラムの中で副作用を持つ部分と持たない部分ははっきり分けることができるという利点があるのだが、
一方でプログラムの基本である入出力の扱いを理解することが難しく、Haskell入門者の泣き所となっている。  

あと地味にオフサイドルールを使っているので、インデントがおかしいとエラーになる。  

## 環境構築
Haskellのコンパイラの実装はいくつかあるが、GHC(Glasgow Haskell Compiler)というものが一番広く使われている。  
また、stackというコンパイラ・ビルドツール・パッケージマネージャ等をひとまとめにしたツールがあるので、  
それを使うと良い。  

### stackの使い方
- `stack ghc` コンパイル
- `stack runghc` コンパイル後に自動実行
- `stack ghci` REPLを起動

## 文法

### Hello World

```haskell
main:: IO ()
main = putStrLn "Hello World" -- putStrLn で改行あり出力
```

`main`式がエントリーポイントとなる。  
`main:: IO()` は型宣言で、`main`という変数が`IO()`型であるということを宣言している(`::`で型注釈)。  
型推論があるので上の例では型宣言を省略しても動作するが、基本的には書いたほうがよいだろう。

複数行書くときは`do`を使う
```haskell
main:: IO()
main = do
   putStr "Hello" -- putStr で改行なし出力
   putStr "World"
   putStr "!!!"
```

後で説明するが、これは次のような書き方のシンタックスシュガーである。  
```haskell
main:: IO()
main = putStrLn "Hello"
   >>= (\_ -> putStr "World")
   >>= (\_ -> putStr "!!!")
```

文字列以外を表示する場合は`print`を使う。  
```haskell
main:: IO()
main =
   print 42
```

### 変数
`let`または`where`で値を変数に束縛することができる。  

```haskell
main =
   let a = 1 in
   print a
```

```haskell
main =
   print a
   where a = 2  -- where を使うと変数を使用箇所の後ろで定義できる
```

### 条件分岐
`if`式と`case`式がある。  
`case`式は他の言語でいうところの`match`や`switch`に相当する。  

```haskell
main = do
   if True then
      putStrLn "true"
   else
      putStrLn "false"
```

```haskell
main = 
   let s = case 2 of
            1 -> "One"
            2 -> "Two"
            _ -> "Other"
   in
      putStrLn s
```

### ラムダ式
`\引数 -> 本体` でラムダ式。  

```haskell
main =
   print (add 1 2)
   where add = \x y -> x + y
```

### 関数
基本的には`関数名 引数 = 本体`と書く
```haskell
add:: Int -> Int -> Int
add x y = x + y

main:: IO()
main =
   print (add 1 2)
```

OCamlやF#などと同じように、関数はカリー化される。  

便利な記法として `$` があり、これは対応する閉じカッコが省略された開きカッコのような役割をする。

```haskell 
main:: IO()
main =
   print $ add 1 2 -- 末尾に閉じカッコがあるのと同じように動く
```

```haskell
foo(bar(baz(3))) -- カッコを使う場合

foo $ bar $ baz 3 -- $ を使う場合
```

#### 副作用を持つ関数 
副作用の無い関数は上のようにシンプルに書けるが、入出力などの副作用がある関数を書く場合は話が難しくなる。  

例として、上のadd関数に引数と戻り値を出力する機能を付け足した場合は次のようになる。
```haskell
add :: Int -> Int -> IO Int
add x y = do
   print (x, y)
   print res
   return res
   where res = x + y
```

ここで着目して欲しいのは、関数の型が`Int -> Int -> Int`から`Int -> Int -> IO Int`に変わった点である。  
Haskellでは入出力はモナドという型クラスを通して扱うと先に述べたが、このようにHaskellではIOを扱う関数の戻り地は
必ず`IO T`型になるという制約がある。  

### データ型

タプル
```
Prelude> :type (1::Int, "hoge", True)
(1::Int, "hoge", True) :: (Int, [Char], Bool)
```

リスト
```
Prelude> :type [1,2,3]
[1,2,3] :: Num a => [a]
```

列挙型
```
Prelude> data Season = Spring | Summer | Fall | Winter
Prelude> :type Spring
Spring :: Season
```
```swift
enum Season {
   case Spring, Summer, Fall, Winter
}
```

直和型(名前付き直和)
`data 型名 = コンストラクタ名 型 ...`
```
Prelude> data Person = Person String Int
Prelude> let p = Person "masuda" 28
Prelude> :type p
p :: Person
```
```swift
typealias Person = (String, Int)
```

直和型
`data 型名 = コンストラクタ名1 型 ... | コンストラクタ名2 型 ...`
```
Prelude> data Shape = Circle Int | Rect Int Int
Prelude> :type Circle 1
Circle 1 :: Shape
```
```swift
enum Shape {
   case Circle(Int)
   case Rect(Int, Int)
}
```

直積型は、コンストラクタが一つだけの直和型と考えることもできる。  

### レコード構文
直和や直積のフィールドに名前を付けることができる。  

```haskell
data Person = Person { name :: String, age :: Int }

main = do
   print (name p)
   print (age p)
   where p = Person { name = "masuda", age = 28 }
```

```haskell
data Shape = Circle { radius :: Int }
            | Rect { height :: Int, width :: Int }
            deriving Show

main = do
   print (Circle { radius = 1 })
   print (Rect { height = 2, width = 3 })
```

#### 導出
列挙型や、下で挙げている直和型、直積型などはREPLや`print`で表示しようとするとエラーになる
```
Prelude> Spring

<interactive>:10:1: error:
    ? No instance for (Show Season) arising from a use of ‘print’
    ? In a stmt of an interactive GHCi command: print it
```
これはHaskellコンパイラが新しく定義された`Season`型を文字列に変換する方法を知らないからである。  

新しく型を定義したときには、その型の値を文字列に変換する方法を自分で定義してもよいし、コンパイラに自動生成させることもできる。   

コンパイラに自動生成させるには、型定義の後に`deriving Show`を付ける。  
```
Prelude> data Season = Spring | Summer | Fall | Winter deriving Show
Prelude> Spring
Spring
```

自前で実装する場合は次のように書く。(`:{`と`:}`はREPL上で複数行入力するためのコマンド)
```
Prelude> :{
Prelude| instance Show Season where
Prelude|   show x = case x of
Prelude|     Spring -> "S"
Prelude|     Summer -> "S"
Prelude|     Fall -> "F"
Prelude|     Winter -> "W"
Prelude| :}
Prelude> Spring
S
Prelude>
```
