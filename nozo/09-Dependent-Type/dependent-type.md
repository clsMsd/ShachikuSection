# 依存型の紹介
依存型についてIdrisを使って紹介する。

## Idris
IdrisはHaskellライクな構文をもつ関数型プログラミング言語である。
特徴として依存型を扱えることを推している。

[Idris - A Language with Dependent Types](https://www.idris-lang.org/)

## First Class Types
依存型を持たない型システムでは型は値につくものであり、言語の中で型と値は明確に区別される。
```
1       : Int
"hoge"  : String
True    : Bool
\x -> x : A -> A
```

依存型を持つ型システムは、型レベルに値が現れることを許容する。
つまり、型と値の間に区別がなくなる。
型と値を区別すること扱えることを型がFirst Classであると言う。

例えば次の関数はBool型の値を入力に受け取り**型を返す**関数である。
```Idris
isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat
```
引数に値`True`が渡されると型`Nat`を返し、値`False`が渡されると型`List Nat`を返している。

この`isSingleton`関数を使うと次のような入力された値によって返す型が異なる関数を定義できる。
```Idris
mkSingle : (x : Bool) -> isSingleton x
mkSingle True = 0
mkSingle False = []
```
`mkSingle`関数の返り値の型に`isSingleton`関数が現れていることに注目したい。
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

例えば長さ2の`Int`型のリストは次のように書ける。
```Idris
v1 : Vect 2 Int
v1 = 1 :: 2 :: Nil
```
`v1`の型にはリストの長さを表す値が現れている。


```Idris
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)
```

```Idris
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ xs) -- BROKEN
```

```
idris --check vector.idr 
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

## The Finite Sets
```
data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)
```

## 参考文献
- The Idris Tutorial, http://docs.idris-lang.org/en/latest/tutorial/index.html
