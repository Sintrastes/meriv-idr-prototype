
module Meriv.Core.Util

import Data.List

||| A simple set type using lists.
export
data Set : Type -> Type where
  MkSet : List a -> Set a
  
export
mkSet : Ord a => List a -> Set a
mkSet xs = MkSet $ sort $ nub xs

export
add : Ord a => Set a -> a -> Set a 
add (MkSet xs) x = MkSet (sort $ nub $ x::xs)

export
(++) : Ord a => Set a -> Set a -> Set a
(MkSet xs) ++ (MkSet ys) = MkSet $ sort $ nub $ xs ++ ys

export
values : Ord a => Set a -> List a
values (MkSet xs) = sort $ nub xs

export
elem : Ord a => a -> Set a -> Bool
elem x (MkSet xs) = x `elem` xs

export
Ord a => Eq (Set a) where
  (MkSet xs) == (MkSet ys) = nub (sort xs) == nub (sort ys)

export 
subsetList : List a -> List a -> Bool
subsetList xs ys = all (\x -> x `elem` ys) ys 