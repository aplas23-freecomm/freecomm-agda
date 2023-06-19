{-# OPTIONS --safe --without-K #-}
module Free.MysteryStructure.Base where

open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Unit

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.FreshList.InductiveInductive

ℕ⁺ : Set
ℕ⁺ = Σ[ n ∈ ℕ ] NonZero n

module FL-≡ (A : Set)(A-set : Irrelevant (_≡_ {A = A})) where

  private
    cons-cong = WithIrr.cons-cong _≡_ A-set

  MA : Set
  MA = List# {A = A} _≡_

  mutual
    repeat : A → ℕ → MA
    repeat a zero = []
    repeat a (suc n) = cons a (repeat a n) (repeat-equal a n)

    repeat-equal : (a : A) → (n : ℕ) → a # repeat a n
    repeat-equal a zero = []
    repeat-equal a (suc n) = refl ∷ repeat-equal a n

  length-repeat : (a : A) → (n : ℕ) → length (repeat a n) ≡ n
  length-repeat a zero = refl
  length-repeat a (suc n) = cong suc (length-repeat a n)

  to : MA → ⊤ ⊎ (A × ℕ⁺)
  to [] = inj₁ tt
  to (cons x xs x#xs) = inj₂ (x , (suc (length xs) , _))

  from : ⊤ ⊎ (A × ℕ⁺) → MA
  from (inj₁ _) = []
  from (inj₂ (a , (n , _))) = repeat a n

  to-from : (x : ⊤ ⊎ (A × ℕ⁺)) → to (from x) ≡ x
  to-from (inj₁ _) = refl
  to-from (inj₂ (a , suc n , record { nonZero = tt })) rewrite length-repeat a n = refl

  from-to : (xs :  MA) → from (to xs) ≡ xs
  from-to [] = refl
  from-to (cons x xs x#xs) = cons-cong refl (lemma xs x#xs)
    where
      lemma : ∀ {x} xs → x # xs → repeat x (length xs) ≡ xs
      lemma [] p = refl
      lemma (cons x xs x#xs) (refl ∷ p) = cons-cong refl (lemma xs p)
