{-# LANGUAGE NoStarIsType
           , DataKinds
           , GADTs
           , TypeFamilies
           , UndecidableInstances
           , TypeOperators
           , StandaloneDeriving
           , DerivingStrategies #-}

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


-}

infixr 5 :::
data HList :: [Type] -> Type where
  HNil  :: HList '[]
  (:::) :: a -> HList as -> HList (a ': as)

deriving stock instance All Eq as => Eq (HList as)

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
-}
id' :: () => a -> a
id' x = x

f :: (Eq a, (Show a, Num a)) => a -> a
f x = x

type Member :: k -> [k] -> Constraint
type family Member x xs where
  Member x '[] = TypeError (Text "Nop")
  Member x (x ': xs) = ()
  Member x (y ': xs) = Member x xs

-- type family All (p :: k -> Constraint) (xs :: [k]) :: Constraint
type All :: (k -> Constraint) -> [k] -> Constraint
type family All p xs where
  All p '[]       = ()
  All p (x ': xs) = (p x, All p xs)

{-
All Show [Int,String,Char,Bool] =
(Show Int, (Show String, (Show Char, (Show Bool,()))))
-}

-- all' :: (a -> Bool) -> [a] -> Bool

-- instance Show a => Show [a] where

showList' :: Show a => [a] -> String
showList' [] = "[]"
showList' (x:xs) = '[' : show x ++ showH xs where
  showH [] = "]"
  showH (y:ys) = ',' : show y ++ showH ys

instance All Show as => Show (HList as) where
  show HNil = "[]"
  show (x ::: xs) = '[' : show x ++ showH xs where
    showH :: All Show bs => HList bs -> String
    showH HNil = "]"
    showH (y ::: ys) = ',' : show y ++ showH ys

-- [1,2,3,4] ++ [5]
infixr 5 ++
type (++) :: [Type] -> [Type] -> [Type]
type family (++) xs ys where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': xs ++ ys

infixr 5 +++
(+++) :: HList as -> HList bs -> HList (as ++ bs)
HNil       +++ ys = ys
(x ::: xs) +++ ys = x ::: xs +++ ys

{-
instance All Eq as => Eq (HList as) where
  HNil       == HNil       = True
  (x ::: xs) == (y ::: ys) = x == y && xs == ys
-}
