{-# OPTIONS --safe --without-K #-}
open import Relation.Binary
open import Data.FreshList.InductiveInductive
open import Data.Nat renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties renaming (<-trans to <ℕ-trans)
open import Data.Nat.Induction
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded

open import Algebra.Structure.OICM

module Free.IdempotentCommutativeMonoid.Base
  {X : Set} {_≈_ : X → X → Set} {_<_ : X → X → Set}
  (<-STO : IsPropStrictTotalOrder _≈_ _<_)
  where

private
  ≈-Eq = IsPropStrictTotalOrder.isEquivalence <-STO
  ≈-sym = IsEquivalence.sym ≈-Eq
  <-tri = IsPropStrictTotalOrder.compare <-STO
  <-trans = IsPropStrictTotalOrder.trans <-STO
  <-resp-≈ = IsPropStrictTotalOrder.<-resp-≈ <-STO
  open WithEq _<_ ≈-Eq <-resp-≈

SortedList : Set
SortedList = List# _<_


-- The union or merge of two lists is defined using wellfounded
-- recursion on their total length; sometimes we decrease the length
-- of the first list, sometimes the second. We also simultaneously
-- prove that if a is fresh for two lists, then it is also fresh for
-- their union.
union : (xs ys : SortedList) → Acc _<ℕ_ (length xs + length ys) → SortedList
union-fresh : {a : X} {xs ys : SortedList} {p : Acc _<ℕ_ (length xs + length ys)} → a # xs → a # ys → a # (union xs ys p)

union [] ys rs = ys
union (cons x xs x#xs) [] rs = cons x xs x#xs
union (cons x xs x#xs) (cons y ys y#ys) (acc rs) with <-tri x y
... | tri< x<y x≉y y≮x = cons x (union xs (cons y ys y#ys) (rs _ ≤-refl)) (union-fresh x#xs (x<y ∷ (#-trans <-trans x y ys x<y y#ys)))
... | tri≈ x≮y x≈y y≮x = cons x (union xs ys (rs _ (s≤s (≤-trans (n≤1+n _) (≤-reflexive $ sym $ +-suc _ _))))) (union-fresh x#xs (#-resp-≈ y#ys (≈-sym x≈y)))
... | tri> x≮y x≉y y<x = cons y (union (cons x xs x#xs) ys (rs _ (s≤s (≤-reflexive $ sym $ +-suc _ _)))) (union-fresh (y<x ∷ #-trans <-trans y x xs y<x x#xs) y#ys)

union-fresh {a} {[]} {ys} {acc rs} a#xs a#ys = a#ys
union-fresh {a} {cons x xs x#xs} {[]} {acc rs} a#xs a#ys = a#xs
union-fresh {a} {cons x xs x#xs} {cons y ys y#ys} {acc rs} (a<x ∷ a#xs) (a<y ∷ a#ys) with <-tri x y
... | tri< x<y x≉y y≮x = a<x ∷ union-fresh a#xs (a<y ∷ a#ys)
... | tri≈ x≮y x≈y y≮x = a<x ∷ (union-fresh a#xs a#ys)
... | tri> x≮y x≉y y<x = a<y ∷ union-fresh (a<x ∷ a#xs) a#ys

-- The top-level operation we really want
_∪_ : SortedList → SortedList → SortedList
xs ∪ ys = union xs ys (<-wellFounded (length xs + length ys))

insert : X → SortedList → SortedList
insert x xs = cons x [] [] ∪ xs
