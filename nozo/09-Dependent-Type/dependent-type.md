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

```Idris
data Vect : Nat -> Type -> Type where
   Nil  : Vect Z a
   (::) : a -> Vect k a -> Vect (S k) a
```

```Idris
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)
```

## 参考文献
- The Idris Tutorial, http://docs.idris-lang.org/en/latest/tutorial/index.html
