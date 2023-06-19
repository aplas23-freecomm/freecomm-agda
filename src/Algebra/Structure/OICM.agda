{-# OPTIONS --without-K --safe #-}
open import Algebra
open import Data.Product
open import Relation.Binary hiding (Irrelevant)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures
open import Relation.Nullary
open import Data.Empty
open import Data.Sum

module Algebra.Structure.OICM where

record IsPropStrictTotalOrder
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _<_ : S → S → Set )
  : Set where
  constructor MkDto
  field
    isSTO : IsStrictTotalOrder _≈_ _<_
    ≈-prop : ∀ {x y} → Irrelevant (x ≈ y)
    <-prop : ∀ {x y} → Irrelevant (x < y)
  open IsStrictTotalOrder isSTO public

record IsPropDecTotalOrder
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _≤_ : S → S → Set )
  : Set where
  constructor MkDto
  field
    isDTO : IsDecTotalOrder _≈_ _≤_
    ≤-prop : ∀ {x y} → Irrelevant (x ≤ y)
  open IsDecTotalOrder isDTO public

record IsPropDecApartnessRelation
  { S : Set }
  ( _≈_ : S → S → Set )
  (_#_ : S → S → Set )
  : Set where
  field
    isEquivalence : IsEquivalence _≈_
    isAR : IsApartnessRelation _≈_ _#_
    prop : ∀ {x y} → Irrelevant (x # y)
    dec : ∀ x y → x ≈ y ⊎ x # y
  open IsApartnessRelation isAR public
  open IsEquivalence isEquivalence renaming (sym to ≈-sym) public

denialApartness : {X : Set} {_≈_ : X → X → Set} → IsEquivalence _≈_ → Decidable _≈_ → IsPropDecApartnessRelation {X} _≈_ (λ x y → ¬ x ≈ y)
IsPropDecApartnessRelation.isEquivalence (denialApartness isEq ≡-dec) = isEq
IsApartnessRelation.irrefl (IsPropDecApartnessRelation.isAR (denialApartness isEq ≡-dec)) x≡y ¬x≡y = ¬x≡y x≡y
IsApartnessRelation.sym (IsPropDecApartnessRelation.isAR (denialApartness isEq ≡-dec)) ¬x≡y y≡x = ¬x≡y (IsEquivalence.sym isEq y≡x )
IsApartnessRelation.cotrans (IsPropDecApartnessRelation.isAR (denialApartness isEq ≡-dec)) {x} {y} ¬x≡y z with ≡-dec x z | ≡-dec z y
... | yes x≡z | yes z≡y = ⊥-elim (¬x≡y (IsEquivalence.trans isEq x≡z z≡y))
... | yes x≡z | no ¬z≡y = inj₂ ¬z≡y
... | no ¬x≡z | _ = inj₁ ¬x≡z
IsPropDecApartnessRelation.prop (denialApartness isEq ≡-dec) p q = refl
IsPropDecApartnessRelation.dec (denialApartness isEq ≡-dec) x y with ≡-dec x y
... | yes x≡y = inj₁ x≡y
... | no ¬x≡y = inj₂ ¬x≡y


-- NB: **Necessarily** strictly ordered when idempotent, non-strict when not.
record IsOrderedCommutativeMonoid
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _≤_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsCommutativeMonoid _≈_ _∙_ ε
    isPDTO : IsPropDecTotalOrder _≈_ _≤_
  open IsPropDecTotalOrder isPDTO
  open IsCommutativeMonoid isICM hiding (refl; sym; trans) public

record IsOrderedIdempotentCommutativeMonoid
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _<_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsIdempotentCommutativeMonoid _≈_ _∙_ ε
    isSTO : IsPropStrictTotalOrder _≈_ _<_

    -- This is a sensible thing to ask, but is not true for sorted lists with lexicographic order.
    -- ∙-preservesˡ-< : ∀ {a b} x → a < b → (x ∙ a) < (x ∙ b)

    -- This is also too strong, but might be an interesting thing to think about.
    -- ε-minimal : ∀ {a} → ε ≢ a → ε < a

  open IsStrictTotalOrder
  open IsIdempotentCommutativeMonoid hiding (refl; sym; trans) public

record IsLeftRegularMonoidWithPropDecApartness
  { S : Set }
  ( _≈_ : S → S → Set )
  ( _#_ : S → S → Set )
  ( _∙_ : S → S → S )
  ( ε : S )
  : Set where
  field
    isICM : IsMonoid _≈_ _∙_ ε
    leftregular : (x y : S) → ((x ∙ y) ∙ x) ≈ (x ∙ y)
    isApartness : IsPropDecApartnessRelation _≈_ _#_

  open IsPropDecApartnessRelation isApartness public
  open IsMonoid isICM hiding (refl; sym; trans; reflexive; isPartialEquivalence) public
