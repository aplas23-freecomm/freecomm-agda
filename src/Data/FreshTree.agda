{-# OPTIONS --safe --without-K #-}

open import Level

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Function

open import Relation.Nullary
open import Relation.Unary using () renaming (Decidable to Decidable₁)
open import Relation.Binary using () renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Binary.Structures
open import Relation.Binary.Definitions using (Symmetric; Irreflexive)

module Data.FreshTree where

data Tree# {n m o} {A : Set n} (Rₗ : A → A → Set m) (Rᵣ : A → A → Set o) : Set (n ⊔ m ⊔ o)
data _<#_  {n m o} {A : Set n} {Rₗ : A → A → Set m} {Rᵣ : A → A → Set o} : Tree# Rₗ Rᵣ → A → Set (n ⊔ m ⊔ o)
data _#>_  {n m o} {A : Set n} {Rₗ : A → A → Set m} {Rᵣ : A → A → Set o} : A → Tree# Rₗ Rᵣ → Set (n ⊔ m ⊔ o)

data Tree# {A = A} Rₗ Rᵣ where
  leaf  : Tree# Rₗ Rᵣ
  _<#>_ : {l : Tree# Rₗ Rᵣ} {x : A} {r : Tree# Rₗ Rᵣ} → l <# x → x #> r → Tree# Rₗ Rᵣ

data _<#_ {A = A} {Rₗ} {Rᵣ} where
  leaf : ∀ {x} → leaf <# x
  node : ∀ {x l y r} {l<#y : l <# y} {y#>r : y #> r}
        → l <# x → Rₗ x y → x #> r → (l<#y <#> y#>r) <# x

data _#>_ {A = A} {Rₗ} {Rᵣ} where
  leaf : ∀ {x} → x #> leaf
  node : ∀ {x l y r} {l<#y : l <# y} {y#>r : y #> r}
        → l <# x → Rᵣ x y → x #> r → x #> (l<#y <#> y#>r)

-- Some predicates for fresh trees.
data NonEmpty {n m o} {A : Set n} {Rₗ : A → A → Set m} {Rᵣ : A → A → Set o} : Tree# Rₗ Rᵣ → Set (n ⊔ m ⊔ o) where
  _<#>_ : {l : Tree# Rₗ Rᵣ} {x : A} {r : Tree# Rₗ Rᵣ}
        → (l<#x : l <# x) → (x#>r : x #> r)
        → NonEmpty (l<#x <#> x#>r)

data All {n m o p} {A : Set n} {Rₗ : A → A → Set m} {Rᵣ : A → A → Set o} (P : A → Set p) : Tree# Rₗ Rᵣ → Set (n ⊔ m ⊔ o ⊔ p) where
  leaf  : All P leaf
  node : ∀ {l x r} {l<#x : l <# x} {x#>r : x #> r}
        → All P l → P x → All P r → All P (l<#x <#> x#>r)

data Any {n m o p} {A : Set n} {Rₗ : A → A → Set m} {Rᵣ : A → A → Set o} (P : A → Set p) : Tree# Rₗ Rᵣ → Set (n ⊔ m ⊔ o ⊔ p) where
  here  : ∀ {l x r} {l<#x : l <# x} {x#>r : x #> r}
        → P x → Any P (l<#x <#> x#>r)
  left  : ∀ {l x r} {l<#x : l <# x} {x#>r : x #> r}
        → Any P l → Any P (l<#x <#> x#>r)
  right : ∀ {l x r} {l<#x : l <# x} {x#>r : x #> r}
        → Any P r → Any P (l<#x <#> x#>r)

R⊥ : ∀ {n} {A : Set n} → A → A → Set
R⊥ _ _ = ⊥

R⊤ : ∀ {n} {A : Set n} → A → A → Set
R⊤ _ _ = ⊤

List# : ∀ {n m} {A : Set n} (R : A → A → Set m) → Set (n ⊔ m)
List# R = Tree# R⊥ R

-------------------------------------
-- Positive and negative elements --
-------------------------------------

-- Maybe should be in its own file
data Signed {n} (X : Set n) : Set n where
  pos : X → Signed X
  neg : X → Signed X

pure : ∀ {n} {X : Set n} → X → Signed X
pure = pos

abs : ∀ {n} {X : Set n} → Signed X → X
abs (pos x) = x
abs (neg x) = x

-- When we take fresh trees over Signed X, we get structures with inverse elements.
-- But we need to externally decide to treat them as such, unless we force them into
-- normal form by augmenting the freshness relation with the condition that x and x⁻¹
-- can't be adjacent. At first glance this seems to go wrong for commutative structures,
-- but it actually works because our notion of commutative is "ordered".
liftR : ∀ {n m} {X : Set n}
      → (R : X → X → Set m) → (Signed X → Signed X → Set (n ⊔ m))
liftR {n} {m} R (pos x) (pos y) = Lift (n ⊔ m) (R x y)
liftR {n} {m} R (neg x) (neg y) = Lift (n ⊔ m) (R x y)
liftR R (pos x) (neg y) = (x ≢ y) × (R x y) 
liftR R (neg x) (pos y) = (x ≢ y) × (R x y)

-----------------
-- Free Stuff! --
-----------------

module _ {n} (X : Set n) where
  --------------------------
  -- Sets with an element --
  --------------------------

  -- Maybe.
  FreePointedSet : Set n
  FreePointedSet = List# {A = X} R⊥

  ---------------------------------
  -- Sets with a binary operator --
  ---------------------------------

  -- Non-empty binary trees.
  FreeMagma : Set n
  FreeMagma = Σ[ T ∈ Tree# {A = X} R⊤ R⊤ ] (NonEmpty T)

  -- Associative
  -- Non-empty lists.
  FreeSemigroup : Set n
  FreeSemigroup = Σ[ L ∈ List# {A = X} R⊤ ] (NonEmpty L)

  -- Invertible
  -- Non-empty binary trees with invertable elements.
  FreeQuasigroup : Set n
  FreeQuasigroup = Σ[ T ∈ Tree# {A = Signed X} (liftR R⊤) (liftR R⊤)] (NonEmpty T)

  -- Invertible and Associative
  -- Non-empty lists with invertable elements.
  FreeInverseSemigroup : Set n
  FreeInverseSemigroup = Σ[ L ∈ List# {A = Signed X} (liftR R⊤) ] (NonEmpty L)


  ------------------------------------------------
  -- Sets with an Element and a Binary Operator --
  ------------------------------------------------

  -- Unital.
  -- Binary trees.
  FreeUnitalMagma : Set n
  FreeUnitalMagma = Tree# {A = X} R⊤ R⊤

  -- Unital and Associative.
  -- Lists.
  FreeMonoid : Set n
  FreeMonoid = List# {A = X} R⊤

  -- Unital and Invertible
  -- Binary trees with invertable elements.
  FreeLoop : Set n
  FreeLoop = Tree# {A = Signed X} (liftR R⊤) (liftR R⊤)

  -- Unital, Invertible, and Associative.
  -- Lists with invertable elements.
  FreeGroup : Set n
  FreeGroup = List# {A = Signed X} (liftR R⊤)

  -- Unital, Associative, and Idempotent.
  -- Lists with no duplicate elements.
  -- Possible tweak: generalise to any aparness relation?
  FreeIdempotentMonoid : Set n
  FreeIdempotentMonoid = List# {A = X} _≢_

  -----------------------------------------------------
  ------------------- Total Orders --------------------
  -- Note: Nothing in this section is free over Set. --
  -----------------------------------------------------

  -- Unital and Commutative.
  -- Binary search trees.
  FreeCommutativeUnitalMagma : ∀ {m} {_≤_ : X → X → Set m}
                             → IsTotalOrder _≡_ _≤_ → Set (n ⊔ m)
  FreeCommutativeUnitalMagma {m} {_≤_} TO = Tree# {A = X} (flip _≤_) _≤_

  -- Unital, Commutative, and Idempotent.
  -- Binary search trees with no duplicated elements.
  FreeIdempotentCommutativeUnitalMagma : ∀ {m} {_<_ : X → X → Set m}
                                       → IsStrictTotalOrder _≡_ _<_ → Set (n ⊔ m)
  FreeIdempotentCommutativeUnitalMagma {m} {_<_} STO = Tree# {A = X} (flip _<_) _<_

  -- Unital, Associative and Commutative.
  -- Sorted Lists.
  FreeCommutativeMonoid : ∀ {m} {_≤_ : X → X → Set m}
                        → IsTotalOrder _≡_ _≤_ → Set (n ⊔ m)
  FreeCommutativeMonoid {m} {_≤_} TO = List# {A = X} _≤_

  -- Unital, Associative, Commutative, and Idempotent.
  -- Sorted Lists with no duplicated elements.
  FreeIdempotentCommutativeMonoid : ∀ {m} {_<_ : X → X → Set m}
                                  → IsStrictTotalOrder _≡_ _<_ → Set (n ⊔ m)
  FreeIdempotentCommutativeMonoid {m} {_<_} STO = List# {A = X} _<_

  -- Unital, Invertible, Associative, and Commutative.
  -- Sorted Lists with invertable elements.
  FreeAbelianGroup : ∀ {m} {_≤_ : X → X → Set m}
                   → IsTotalOrder _≡_ _≤_ → Set (n ⊔ m)
  FreeAbelianGroup {m} {_≤_} TO = List# {A = Signed X} (liftR _≤_)
