# 依存型の紹介

## Idris

## First Class Types

```
isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat
```

```
mkSingle : (x : Bool) -> isSingleton x
mkSingle True = 0
mkSingle False = []
```

```
sum : (single : Bool) -> isSingleton single -> Nat
sum True x = x
sum False [] = 0
sum False (x :: xs) = x + sum False xs
```

## 長さ付きリスト型

```
data Vect : Nat -> Type -> Type where
   Nil  : Vect Z a
   (::) : a -> Vect k a -> Vect (S k) a
```

```
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)
```

## 参考文献
- The Idris Tutorial, http://docs.idris-lang.org/en/latest/tutorial/index.html
