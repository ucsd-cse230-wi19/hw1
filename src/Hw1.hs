module Hw1 where 

import Prelude hiding (lookup, reverse, abs, repeat, map, length, head, take, drop)
import qualified Data.Set as S

-----------------------------------------------------------------------------
-- | Problem 1 : Fix the refined type of `abs` so that `problem1` type checks 
-----------------------------------------------------------------------------

{-@ abs :: Int -> Nat @-}
abs :: Int -> Int
abs x
  | x < 0     = - x
  | otherwise = x

{-@ problem1 :: _  -> Nat @-}
problem1 :: [(Int, Int)] -> Int 
problem1 [] 	            = 0 
problem1 ((x1, x2) : rest)  = abs (x1 - x2) + problem1 rest 


-----------------------------------------------------------------------------
-- Problem 2: Fix the signature for `sub` so it implements subtraction 
--            restricted to (suitable) natural numbers.
-----------------------------------------------------------------------------

{-@ sub :: x:Nat -> {y:Nat | y <= x} -> Nat @-}
sub :: Int -> Int -> Int 
sub x y = x - y

-----------------------------------------------------------------------------
-- Problem 3: Fix the implementation of `sub'` so that it behaves 
--            as described below 
-----------------------------------------------------------------------------
--
-- >>> sub' 10 2 
-- Just 8 
--
-- >>> sub' 2 10 
-- Nothing 

{-@ sub' :: Nat -> Nat -> Maybe Nat @-}
sub' :: Int -> Int -> Maybe Int 
sub' x y = Just (x - y)

-----------------------------------------------------------------------------
-- | Problem 4: Write a signature for `halve` so that `problem4` typechecks
-----------------------------------------------------------------------------

{-@ halve :: Int -> (Int, Int) @-}
halve :: Int -> (Int, Int)
halve i = (j, j + r)
  where
    j = i `div` 2
    r = i `mod` 2

{-@ problem4 :: {v:_ | v = 100} @-}
problem4   :: Int
problem4   = a + b 
  where 
    (a, b) = halve 100 

-- HINT: You can use `fst` and `snd` in the refinement to access the components of the pair.

-----------------------------------------------------------------------------
-- | Problem 5: Taking `i` elements out of a list. 
--              Can you fix the following definition of `take`?
-----------------------------------------------------------------------------

-- >>> take 3 (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil))))
-- Cons 1 (Cons 2 (Cons 3 Nil))

{-@ take :: i:Nat -> List a -> { ys : List a | length ys == i } @-}
take :: Int -> List a -> List a
take _ Nil         = Nil
take 0 _           = Nil
take i (Cons x xs) = x `Cons` take (i - 1) xs

-- **Hint** Could you use impossible in the definition of take?

-----------------------------------------------------------------------------
-- | Problem 6: Dropping `i` elements from a list. 
--              Write a refinement type for `drop n xs` which "removes" 
--              the first `n` elements of a list.
-----------------------------------------------------------------------------

{-@ drop :: Int -> List a -> List a @-}
drop :: Int -> List a -> List a
drop _ Nil         = Nil
drop 0 xs          = xs
drop i (Cons _ xs) = drop (i - 1) xs
drop _ _           = impossible "drop"

{-@ problem6 :: {v:_ | length v == 2} @-}
problem6 = drop 2 (Cons "i" (Cons "am" (Cons "the" (Cons "walrus" Nil))))

-----------------------------------------------------------------------------
-- | Problem 7: The `sublist s l xs` function returns the sub-sequence of `l`
--              elements of `xs` starting at position `s`. Fix its specification 
--              so that both `sublist` and `problem7` verify.
-----------------------------------------------------------------------------

{-@ sublist :: s:Int -> l:Int -> xs:List a -> List a @-}
sublist :: Int -> Int -> List a -> List a
sublist s l xs = take l (drop s xs)

{-@ problem7 :: {v:_ | length v == 2} @-}
problem7:: List Int
problem7 = sublist 1 2 (1 `Cons` 2 `Cons` 3 `Cons` 4 `Cons` Nil)


-----------------------------------------------------------------------------
-- | Problem 8: Write the specification and implementation of a function that 
--              `reverse`s the order of elements in a list. Your implementation 
--              must ensure that `last` defined below also typechecks.
-----------------------------------------------------------------------------

{-@ reverse :: List a -> List a @-}
reverse :: List a -> List a 
reverse xs = impossible "TBD: reverse"

{-@ last :: {v:List a | length v > 0} -> a @-}
last :: List a -> a 
last xs = head (reverse xs)

----------------------------------------------------------------------------------
-- | Problem 9: Recall the definition of `Table`; write a safe lookup function.
----------------------------------------------------------------------------------

data Table key val 
  = Empty
  | Bind key val (Table key val)
  deriving (Show)

lookup :: Ord key => key -> Table key val -> val
lookup k (Bind k' v r)
  | k == k'            = v
  | otherwise          = lookup k r
lookup _ Empty         = impossible "lookup: Empty"

----------------------------------------------------------------------------------
-- | Problem 10: Consider the following `Expr`ession type; can you fix the spec
--               of the `eval` function so the code typechecks? 
--   HINT: you may need to write a suitable "measure" for `Expr`... 
----------------------------------------------------------------------------------

data Expr 
  = EVar String 
  | ENum Int
  | EAdd Expr Expr 
  deriving (Show)

{-@ eval :: env:Table String Int -> e:Expr -> Int @-}
eval :: Table String Int -> Expr -> Int 
eval _   (ENum n)     = n 
eval env (EVar x)     = lookup x env 
eval env (EAdd e1 e2) = eval env e1 + eval env e2 

problem10 :: Int
problem10 = eval env10 exp10 
  where 
    env10 = Bind "x" 10 (Bind "y" 20 Empty)
    exp10 = EAdd (EVar "x") (EAdd (EVar "y") (ENum 10))

----------------------------------------------------------------------------------
-- Definitions 
----------------------------------------------------------------------------------

{-@ data List [length] @-}
data List a = Nil | Cons a (List a)
  deriving (Show)

infixr 5 `Cons`

{-@ measure length          @-}
{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil           = 0
length (x `Cons` xs) = 1 + length xs

{-@ assume impossible :: { s : String | True } -> a @-}
impossible :: String -> a
impossible msg = undefined -- error msg

{-@ head :: {v:_ | length v > 0} -> _ @-}
head :: List a -> a
head (Cons x xs) = x

{-@ measure size @-}
{-@ size :: Table key val -> Nat @-}
size :: Table key val -> Int
size Empty        = 0
size (Bind _ _ t) = 1 + size t

{-@ data Table [size] @-}
{-@ measure keys @-}
keys :: Ord key => Table key val -> S.Set key
keys Empty        = S.empty
keys (Bind k _ t) = S.union (S.singleton k) (keys t)
