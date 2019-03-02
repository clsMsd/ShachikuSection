data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)

indexFin : Fin n -> Vect n a -> a
indexFin FZ     (x :: xs) = x
indexFin (FS k) (x :: xs) = indexFin k xs

vec : Vect 3 Int
vec = 1 :: 2 :: 3 :: Nil

fin0 : Fin 3
fin0 = FZ

fin1 : Fin 3
fin1 = FS FZ

fin2 : Fin 3
fin2 = FS (FS FZ)

-- -- Type Check Error
-- -- (FS (FS (FS FZ))) : Fin 3
-- --     (FS (FS FZ))  : Fin 2
-- --         (FS FZ)   : Fin 1
-- --             FZ    : Fin 0
-- fin3 : Fin 3
-- fin3 = FS (FS (FS FZ))

res : Int
res = indexFin FZ (1::2::3::Nil)

-- -- Type Check Error
-- res_err : Int
-- res_err = indexFin (FS (FS (FS FZ))) (1::2::3::Nil)
