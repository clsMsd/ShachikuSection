# 依存型の紹介
依存型についてIdrisを使って紹介する。

## Idris
IdrisはHaskellライクな構文をもつ関数型プログラミング言語である。
特徴として依存型を扱えることを推している。

[Idris - A Language with Dependent Types](https://www.idris-lang.org/)

このページのidrisのバージョンは以下のものである。
```
$ idris --version
1.3.1-git:PRE
```

## First Class Types
依存型を持たない型システムでは型は値につくものであり、言語の中で型と値は明確に区別される。
```
1       : Int
"hoge"  : String
True    : Bool
\x -> x : A -> A
```

依存型を持つ型システムは、型に値が現れたり型を値として扱うことを許容する。
そのように型と値を区別することなく扱えることを型がFirst Classであると言う。

例えば次の関数はBool型の値を入力に受け取り**型を返す**関数である。
```Idris
isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat
```
引数に値`True`が渡されると型`Nat`を返し、値`False`が渡されると型`List Nat`を返している。

この`isSingleton`関数を使うと引数の値によって返り値の型が異なる関数を定義できる。
```Idris
mkSingle : (x : Bool) -> isSingleton x
mkSingle True = 0
mkSingle False = []
```
`mkSingle`関数の返り値の**型に`isSingleton`関数が現れている**ことに注目したい。
`isSingleton`関数には`mkSingle`関数の引数である`Bool`型の値`x`が渡されている。
`mkSingle`関数に値`True`が渡されると返り値の型は`Nat`となり、値`False`が渡されると返り値の型は`List Nat`となる。

返り値の型だけでなく、引数の型にも関数が現れることも可能である。
```Idris
sum : (single : Bool) -> isSingleton single -> Nat
sum True x = x
sum False [] = 0
sum False (x :: xs) = x + sum False xs
```
`sum`関数の第１引数に渡される値によって第２引数の型が決定される。

## 長さ付きリスト型
もう少し実用的な例を見てみる。
次のプログラムは長さ付きリスト型の宣言である。

```Idris
data Vect : Nat -> Type -> Type where
   Nil  : Vect Z a
   (::) : a -> Vect k a -> Vect (S k) a
```

例えば長さ３の`Int`型のリストは次のように書ける。
```Idris
vec : Vect 3 Int
vec = 1 :: 2 :: 3 :: Nil
```
値`vec`の型にはリストの長さを表す値が現れている。

２つの長さ付きリストを結合する関数は次のように書ける。
```Idris
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)
```
引数の型を見ると長さ`n`のリストと長さ`m`のリストを受け取ることがわかる。
返り値の型は`Vect (n + m) a`となっており長さが`n + m`のリストが返ってくることが型レベルで保証される。

型で返り値のリストの長さが保証されていると、次のようなプログラムのバグが型チェックで検証できる。
```Idris
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ xs) -- BROKEN
```

型チェックを実行すると次のようなエラーが出力される。
```
$ idris --check vector.idr 
vector.idr:7:23-24:
  |
7 | (++) (x :: xs) ys = x :: (xs ++ xs)
  |                       ~~
When checking right hand side of Main.++ with expected type
        Vect (S k + m) a

When checking an application of constructor Main.:::
        Type mismatch between
                Vect (k + k) a (Type of xs ++ xs)
        and
                Vect (plus k m) a (Expected type)
        
        Specifically:
                Type mismatch between
                        plus k k
                and
                        plus k m
```
エラーが出た行の`(++)`関数の引数の型は`xs`の長さを`k`とすると次のような関係になる。
```
(x :: xs) : Vect (k + 1) a
ys        : Vect m a
```
すると`x :: (xs ++ xs)`の`(xs ++ xs)`の部分の型は`Vect (k + k)`となってしまう。
関数の型の定義によるとこの部分の型は`Vect (k + m)`であるべきなので型がマッチせずエラーとなっている。

## The Finite Sets
次の例は有限集合型である。
```Idris
data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)
```
集合型という名前から`{1,2,3}`のような何かの値のコレクションだと思ってしまうがそうではない。

例えば型`Fin 3`の属する値は次の３つである。
```Idris
fin0 : Fin 3
fin0 = FZ

fin1 : Fin 3
fin1 = FS FZ

fin2 : Fin 3
fin2 = FS (FS FZ)
```

値`FS (FS (FS FZ))`に`Fin 3`を型付けしようとするとエラーが出る。
```Idris
fin3 : Fin 3
fin3 = FS (FS (FS FZ))
```
型チェック実行結果。
```
$ idris --check vector.idr
vector.idr:31:16-20:
   |
31 | fin3 = FS (FS (FS FZ))
   |                ~~~~~
When checking right hand side of fin3 with expected type
        Fin 3

When checking an application of constructor Main.FS:
        Type mismatch between
                Fin (S k) (Type of FZ)
        and
                Fin 0 (Expected type)
        
        Specifically:
                Type mismatch between
                        S k
                and
                        0
```

値`FS (FS (FS FZ))`が`Fin 3`型であるとすると、内側の`FZ`の型は`Fin 0`であるはずである。
しかし、`Fin`型の定義より`Fin 0`型の値は存在しないため型エラーとして報告される。
```
(FS (FS (FS FZ))) : Fin 3
    (FS (FS FZ))  : Fin 2
        (FS FZ)   : Fin 1
            FZ    : Fin 0
```

以上の特性から、`Fin n`型に属する値は`0`から`(n-1)`であることを型によって保証される。
この特性を用いるとリストへの添字アクセス関数について範囲外へのアクセスが発生しないことを型レベルで保証できる。
```Idris
indexFin : Fin n -> Vect n a -> a
indexFin FZ     (x :: xs) = x
indexFin (FS k) (x :: xs) = indexFin k xs
```

範囲外へのアクセスを行うプログラムを記述すると型チェックの時点でエラーが報告される。
```Idris
res_err : Int
res_err = indexFin (FS (FS (FS FZ))) (1::2::3::Nil)
```
型チェック実行結果。
```
$ idris --check vector.idr
vector.idr:41:46-47:
   |
41 | res_err = indexFin (FS (FS (FS FZ))) (1::2::3::Nil)
   |                                              ~~
When checking right hand side of res_err with expected type
        Int

When checking an application of constructor Main.:::
        Type mismatch between
                Vect 0 a (Type of [])
        and
                Vect (S k) Int (Expected type)
        
        Specifically:
                Type mismatch between
                        0
                and
                        S k
```

## 参考文献
- The Idris Tutorial, http://docs.idris-lang.org/en/latest/tutorial/index.html
