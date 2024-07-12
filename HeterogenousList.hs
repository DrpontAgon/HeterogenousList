{-# LANGUAGE NoStarIsType -- I don't like the * to denote types, * is for multiplication.
           , DataKinds    -- Needed to lift the already existing list to type level.
           , GADTs        -- Generalised Algebraic Datatypes ftw.
           , TypeFamilies -- Enables type families.
           , UndecidableInstances -- Turns off the not-so-smart termination checker of instance resolution.
           , TypeOperators        -- Enables the definition of operators at type level
           , StandaloneDeriving   -- Enables deriving independently from the data declaration. Advantage: can work with GADTs, since an instance context can be given with this.
#-}

module HeterogeneousList where

import Data.Kind
import GHC.TypeError
{-
Yesterday we saw:

data Dynamic where
  Dyn :: Type a -> a -> Dynamic

data Type a where
 INT :: Type Int
 BOOL :: ...


"Type a" encoded some of the types (Int,Bool,List,Pair as examples) but not all of them.

We saw the "cast :: Type a -> Dynamic -> Maybe a" function:
this is essentially haskell's Typeable typeclass' functionality.
(https://hackage.haskell.org/package/base-4.20.0.1/docs/Data-Typeable.html)

We could redifine the above type:

data Dynamic where
  Dyn :: Typeable a => a -> Dynamic

Since GHC 7.10 it is automatically derived for data types.

-------

But Haskell is pretty good with types, why would we want to hide those?
We can have heterogenous lists without hiding the types in a Dynamic type.

Problem:
-- Tuples are heterogenous but have fixed "number of elements"
-- Lists can have arbitrarily many elements but are homogenous.

Idea: try to somehow combine the best from both of the worlds,
namely arbitrarily many elements with possibly different types.

----------------------------------------------------------------
Session from Utrecht, 2024 july 12

GHCI stuff:

λ> :t []
[] :: forall a. [a]
λ> :k []
[] :: Type -> Type
λ> head' (True ::: 'a' ::: False ::: HNil)
True
λ> head' ('a' ::: False ::: HNil)
'a'
λ> head' $ tail' (True ::: 'a' ::: False ::: HNil)
'a'
λ> tail' (True ::: 'a' ::: False ::: HNil)
'a' ::: False ::: []
λ> [1,2,3,4]
[1,2,3,4]
λ> (1 :: Int) ::: True ::: 'a' ::: (False ::: 6 ::: HNil) ::: () ::: ['a','b'] ::: HNil
[1,True,'a',[False,6],(),"ab"]
λ> (True ::: 'a' ::: HNil) +++ HNil
[True,'a']
λ> (True ::: 'a' ::: HNil) +++ HNil == True ::: 'a' ::: HNil
True
λ> (True ::: 'a' ::: HNil) +++ HNil == True ::: 'b' ::: HNil
False

Lists with different types at the same position cause a complation error.
-}

infixr 5 :::
data HList :: [Type] -> Type where
  HNil  :: HList '[]
  (:::) :: a -> HList as -> HList (a ': as)

deriving instance All Eq as => Eq (HList as)

head' :: HList (a ': as) -> a
head' (x ::: _) = x

tail' :: HList (a ': as) -> HList as
tail' (_ ::: xs) = xs

{-
instance Show (HList '[]) where
  show HNil = "[]"

instance (Show a, Show (HList as)) => Show (HList (a ': as)) where
  show (x ::: xs) = show x ++ " ::: " ++ show xs
-}
{-
type family Member' (x :: k) (xs :: '[k]) :: 'Bool where
  Member' x '[]       = 'False
  Member' x (x ': xs) = 'True
  Member' x (y ': xs) = Member' x xs

type Member x xs = Member' x xs ~ 'True -- ??

The problem is that Haskell doesn't know that the constructors are injective.

TODO: example when using type equality with Bools is problematic.
-}

-- Completely valid forms of Constraints:

-- Empty constraint -> Trivially holds
id' :: () => a -> a
id' x = x

-- Constraints can be nested.
f :: (Eq a, (Show a, Num a)) => a -> a
f x = x

type Member :: k -> [k] -> Constraint
type family Member x xs where
  Member x '[] = TypeError (Text "Nop")
  Member x (x ': xs) = ()
  Member x (y ': xs) = Member x xs


-- This idea is analogous to the value level "all :: (a -> Bool) -> [a] -> Bool" function.

-- type family All (p :: k -> Constraint) (xs :: [k]) :: Constraint -- < original syntax for type families to give the kinds.
type All :: (k -> Constraint) -> [k] -> Constraint -- StandaloneKindSignatures pragma might be needed.
type family All p xs where
  All p '[]       = ()
  All p (x ': xs) = (p x, All p xs)

{-
All Show [Int,String,Char,Bool] =
(Show Int, (Show String, (Show Char, (Show Bool,()))))
-}

-- Showing a list the usual way.
-- instance Show a => Show [a] where
showList' :: Show a => [a] -> String
showList' [] = "[]"
showList' (x:xs) = '[' : show x ++ showH xs where
  showH [] = "]"
  showH (y:ys) = ',' : show y ++ showH ys

-- Same idea:
instance All Show as => Show (HList as) where
  show HNil = "[]"
  show (x ::: xs) = '[' : show x ++ showH xs where
    showH :: All Show bs => HList bs -> String -- with GADTs and ScopedTypeVariables take extra care to name this a different type variable from the top-level one.
    showH HNil = "]"
    showH (y ::: ys) = ',' : show y ++ showH ys

{-
-- Already derived with standalone deriving
instance All Eq as => Eq (HList as) where
  HNil       == HNil       = True
  (x ::: xs) == (y ::: ys) = x == y && xs == ys
-}

infixr 5 ++
type (++) :: [Type] -> [Type] -> [Type]
type family (++) xs ys where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': xs ++ ys

infixr 5 +++
(+++) :: HList as -> HList bs -> HList (as ++ bs)
HNil       +++ ys = ys
(x ::: xs) +++ ys = x ::: xs +++ ys

-- Problem: We have to define the EXACT SAME function on type level (type families) and value level.
-- Solution: Dependent types allow the neccessary abstraction and is enough to define the function only once.
