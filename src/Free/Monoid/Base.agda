{-# OPTIONS --without-K --safe #-}
module Free.Monoid.Base where

open import Data.FreshList.InductiveInductive
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Function

open import Algebra.Definitions
open import Algebra.Structures

open import Relation.Const
open import Relation.Binary.PropositionalEquality
open import Relation.Binary



List : Set → Set
List X = List# {A = X} R⊤

tt# : ∀ {X} {x : X} {xs : List X} → x # xs
tt# {x = x} {[]} = []
tt# {x = x} {cons y ys y#ys} = tt ∷ tt# {x = x} {ys}

_++_ : ∀ {X} → List X → List X → List X
[] ++ ys = ys
(cons x xs _) ++ ys = cons x (xs ++ ys) tt#
infixl 1 _++_

++-assoc : ∀ {X} → Associative _≡_ (_++_ {X})
++-assoc [] y z = refl
++-assoc (cons x xs x#xs) y z = cong (λ z → cons x z tt#) (++-assoc xs y z)

++-idR : ∀ {X} → RightIdentity _≡_ [] (_++_ {X})
++-idR [] = refl
++-idR {X} (cons x xs x#xs) = trans
  (cong (λ z → cons x z tt#) (++-idR xs))
  (cong (cons x xs) (WithIrr.#-irrelevant R⊤ (λ {a} {b} → R⊤-irr {X} {a} {b}) _ _))

++-id : ∀ {X} → Identity _≡_ [] (_++_ {X})
proj₁ ++-id xs = refl
proj₂ ++-id xs = ++-idR xs

ListMonoid : ∀ {X} → IsMonoid {A = List X} _≡_ _++_ []
IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup ListMonoid)) = isEquivalence
IsMagma.∙-cong (IsSemigroup.isMagma (IsMonoid.isSemigroup ListMonoid)) refl refl = refl
IsSemigroup.assoc (IsMonoid.isSemigroup ListMonoid) = ++-assoc
IsMonoid.identity ListMonoid = ++-id

map-list-fun : ∀ {X Y} → (X → Y) → List X → List Y
map-list-fun f []  = []
map-list-fun f (cons x xs x#xs) = cons (f x) (map-list-fun f xs) tt#

map-list-preserves-∙ : ∀ {X} {Y} (f : X → Y)
                       (xs : List X) (ys : List X) →
                        map-list-fun f (xs ++ ys) ≡ (map-list-fun f xs ++ map-list-fun f ys)
map-list-preserves-∙ f [] ys = refl
map-list-preserves-∙ f (cons x xs x#xs) ys = cong (λ z → cons (f x) z tt#) (map-list-preserves-∙ f xs ys)

--------------------------
-- List preserves hsets --
--------------------------

-- The standard encode-decode proof
module _ {X : Set} where

  Code : List X → List X → Set
  Code [] [] = ⊤
  Code [] (cons x ys x#xs) = ⊥
  Code (cons x xs x#xs) [] = ⊥
  Code (cons x xs x#xs) (cons y ys y#ys) = x ≡ y × Code xs ys

  encodeRefl : (xs : List X) → Code xs xs
  encodeRefl [] = tt
  encodeRefl (cons x xs x#xs) = refl , encodeRefl xs

  encode : {xs ys : List X} → xs ≡ ys → Code xs ys
  encode refl = encodeRefl _

  decode : {xs ys : List X} → Code xs ys → xs ≡ ys
  decode {[]} {[]} tt = refl
  decode {cons x xs x#xs} {cons y ys x#xs₁} (x≡y , c) = WithIrr.cons-cong R⊤ (λ _ _ → refl) x≡y (decode c)

  decodeEncodeRefl : (xs : List X) → decode (encodeRefl xs) ≡ refl
  decodeEncodeRefl [] = refl
  decodeEncodeRefl (cons x xs x#xs) rewrite decodeEncodeRefl xs = cong (cong (cons x xs)) (lemma x#xs)
    where
      lemma : ∀ {x : X}{xs : List X} (x#xs : x # xs) → WithIrr.#-irrelevant (λ _ _ → ⊤) (λ _ _ → refl) x#xs x#xs ≡ refl
      lemma {x} {.[]} [] = refl
      lemma {x} {.(cons _ _ _)} (t ∷ x#xs) rewrite lemma x#xs = refl

  decodeEncode : {xs ys : List X} → (p : xs ≡ ys) → decode (encode p) ≡ p
  decodeEncode refl = decodeEncodeRefl _

  prop-Code : (prop-X : Irrelevant (_≡_ {A = X})) → Irrelevant Code
  prop-Code prop-X {[]} {[]} p q = refl
  prop-Code prop-X {cons x xs x#xs} {cons y ys y#ys} (p , p') (q , q') = cong₂ _,_ (prop-X p q) (prop-Code prop-X p' q')

  ListhSet : Irrelevant (_≡_ {A = X}) → Irrelevant (_≡_ {A = List X})
  ListhSet prop-X p q = begin
    p
      ≡⟨ sym (decodeEncode p) ⟩
    decode (encode p)
      ≡⟨ cong decode (prop-Code prop-X (encode p) (encode q)) ⟩
    decode (encode q)
      ≡⟨ decodeEncode q ⟩
    q
      ∎ where open ≡-Reasoning
