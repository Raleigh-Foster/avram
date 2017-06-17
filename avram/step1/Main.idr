module Main

%default total



namespace list
 data MyList a = Nil | (::) a (MyList a)

namespace listgadt
 data MyListt : Type -> Type where
  Nil : MyListt a
  (::) : a -> MyListt a -> MyListt a


index' : Nat -> MyList a -> Maybe a
index' _ [] = Nothing
index' Z (x::xs) = Just x
index' (S k) (x::xs) = index' k xs


data Fin : Nat -> Type where
 FZ : Fin (S k)
 FS : Fin k -> Fin (S k)



data Vect : Nat -> Type -> Type where
 Nil : Vect 0 a
 (::) : a -> Vect n a -> Vect (S n) a


index : Fin n -> Vect n a -> a
index FZ (x::xs) = x
index (FS fk) (x::xs) = index fk xs



deleteAt : Fin (S n) -> Vect (S n) a -> Vect n a
deleteAt FZ (x::xs) = xs
deleteAt {n=S n1} (FS fk) (x::xs) = x :: (deleteAt fk xs)


{-

namespace untyped_unbalanced
 data Tree : Type -> Type -> Type where
  Leaf : Tree keyType valueType
  Branch :
   keyType ->
   valueType ->
   Tree keyType valueType ->
   Tree keyType valueType ->
   Tree keyType valueType

 insert :
 (key : keyType) ->
 (value : valueType) ->
 Ord keyType =>
 Tree keyType valueType ->
 Tree keyType valueType

 insert key value Leaf = Branch key value Leaf Leaf
 insert key value (Branch k1 v1 left right) with (compare key k1)
  | LT = Branch k1 v1 (insert key value left) right
  | EQ = Branch key value left right
  | GT = Branch k1 v1 left (insert key value right)
-}

{-instead of nat, can we just store the balance factor as an ADT of 5 values????-}
namespace avl_tree


 data Tree : Type -> Type -> Type where
  Leaf : Tree keyType valueType
  Branch :
   Nat ->
   keyType ->
   valueType ->
   Tree keyType valueType ->
   Tree keyType valueType ->
   Tree keyType valueType


 balance : Tree keyType valueType -> Tree keyType valueType
 balance Leaf = Leaf
{-
 balance (Branch n key value Leaf Leaf) = Branch 1 key value Leaf Leaf
 balnace (Branch n key value (Branch m k1 v1 l r) Lear
-}

 insert :
  keyType ->
  valueType ->
  Ord keyType =>
  Tree keyType valueType ->
  Tree keyType valueType

 insert key value Leaf = Branch 1 key value Leaf Leaf
 insert key value (Branch n k1 v1 left right) with (compare key k1)
  | LT = balance $ Branch n k1 v1 (insert key value left) right
  | EQ = Branch n key value left right
  | GT = balance $ Branch n k1 v1 left (insert key value right)


main : IO ()
main = pure ()



