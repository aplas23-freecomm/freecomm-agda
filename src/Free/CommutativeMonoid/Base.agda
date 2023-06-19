{-# OPTIONS --safe --without-K #-}

open import Algebra.Structure.OICM

module Free.CommutativeMonoid.Base
  {X : Set} {_≈_ : X → X → Set} {_≤_ : X → X → Set}
  (≤-PDTO : IsPropDecTotalOrder _≈_ _≤_)
  where

open import Data.Sum
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s)
                     renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties
  using (1+n≢n; 1+n≢0; +-identityʳ; m≤m+n; +-suc; suc-injective; +-assoc; +-comm)
  renaming (≤-step to ≤ℕ-step; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans; ≤-reflexive to ≤ℕ-reflexive)
open import Data.Nat.Induction
open import Induction.WellFounded




open import Relation.Binary.PropositionalEquality

open import Data.FreshList.InductiveInductive

private
  total   = IsPropDecTotalOrder.total ≤-PDTO
  ≤-refl  = IsPropDecTotalOrder.refl ≤-PDTO
  ≤-trans = IsPropDecTotalOrder.trans ≤-PDTO

SortedList : Set
SortedList = List# _≤_

----------------
-- Merge Sort --
----------------

union : (xs ys : SortedList) → Acc _<ℕ_ (length xs + length ys) → SortedList
union-fresh : {a : X} {xs ys : SortedList} {p : Acc _<ℕ_ (length xs + length ys)} → a # xs → a # ys → a # (union xs ys p)

union [] ys (acc rs) = ys
union (cons x xs x#xs) [] (acc rs) = cons x xs x#xs
union (cons x xs x#xs) (cons y ys y#ys) (acc rs) with total x y
... | inj₁ x≤y = cons x (union xs (cons y ys y#ys) (rs _ ≤ℕ-refl))
                        (union-fresh x#xs (#-trans ≤-trans x y (cons y ys y#ys) x≤y (≤-refl ∷ y#ys)))
... | inj₂ y≤x = cons y (union (cons x xs x#xs) ys (rs _ (s≤s (≤ℕ-reflexive (sym (+-suc _ _))))))
                        (union-fresh (#-trans ≤-trans y x (cons x xs x#xs) y≤x (≤-refl ∷ x#xs)) y#ys)

union-fresh {a} {[]} {ys} {acc rs} a#xs a#ys = a#ys
union-fresh {a} {cons x xs x#xs} {[]} {acc rs} a#xs a#ys = a#xs
union-fresh {a} {cons x xs x#xs} {cons y ys y#ys} {acc rs} (a≤x ∷ a#xs) (a≤y ∷ a#ys) with total x y
... | inj₁ x≤y = a≤x ∷ union-fresh a#xs (a≤y ∷ a#ys)
... | inj₂ y≤x = a≤y ∷ union-fresh (a≤x ∷ a#xs) a#ys

_∪_ : SortedList → SortedList → SortedList
xs ∪ ys = union xs ys (<-wellFounded (length xs + length ys))


---------------
-- Insertion --
---------------

-- Can now define insert in terms of union
insert' : X → (xs : SortedList) → Acc _<ℕ_ (suc (length xs)) → SortedList
insert' x xs p = union (cons x [] []) xs p

insert : X → SortedList → SortedList
insert x xs = insert' x xs (<-wellFounded _)
