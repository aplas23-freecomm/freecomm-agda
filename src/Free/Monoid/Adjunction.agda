{-# OPTIONS --safe --without-K #-}

module Free.Monoid.Adjunction where

open import Axiom.Extensionality.Propositional

open import Algebra.Structures
open import Category.Base
open import Data.FreshList.InductiveInductive
open import Free.Monoid.Base
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Const

-------------------------
-- Category of monoids --
-------------------------

record Monoid : Set₁ where
  constructor Mon
  field
    Carrier : Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsMonoid  _≡_ _∙_ ε
    isSet : Irrelevant (_≡_ {A = Carrier})
open Monoid

record MonoidMorphism (A B : Monoid) : Set where
  constructor MonMorphism
  private
    module A = Monoid A
    module B = Monoid B
  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open MonoidMorphism

mon-id : ∀ {A} → MonoidMorphism A A
fun mon-id = Function.id
preserves-ε mon-id = refl
preserves-∙ mon-id _ _ = refl

mon-comp : ∀ {A B C} → MonoidMorphism A B → MonoidMorphism B C → MonoidMorphism A C
fun (mon-comp f g) = (fun g) ∘ (fun f)
preserves-ε (mon-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (mon-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)


eqMonMorphism : Extensionality _ _ →
                ∀ {A B} → {f g : MonoidMorphism A B} → fun f ≡ fun g → f ≡ g
eqMonMorphism ext {A} {B} {MonMorphism .f refl p∙} {MonMorphism f q q∙} refl
    = cong₂ (MonMorphism f) (uipB refl q) (ext λ x → ext (λ y → uipB (p∙ x y) (q∙ x y)))
    where
      uipB = isSet B


MON : Extensionality _ _ → Category
Category.Obj (MON ext) = Monoid
Category.Hom (MON ext) = MonoidMorphism
Category.id (MON ext) = mon-id
Category.comp (MON ext) = mon-comp
Category.assoc (MON ext) = eqMonMorphism ext refl
Category.identityˡ (MON ext) = eqMonMorphism ext refl
Category.identityʳ (MON ext) = eqMonMorphism ext refl


-----------------------
-- Forgetful functor --
-----------------------

open Functor

FORGET : (@0 ext : Extensionality _ _) → Functor (MON ext) HSET
act (FORGET _) X = hset (Carrier X) (isSet X)
fmap (FORGET _) f x = fun f x
identity (FORGET _) = refl
homomorphism (FORGET _) = refl


------------------
-- Free functor --
------------------

List' : hSet → Monoid
Carrier (List' X) = List (hSet.Carrier X)
_∙_ (List' X) = _++_
ε (List' X) = []
proof (List' X) = ListMonoid
isSet (List' X) = ListhSet (hSet.isSet X)

FREEMONOID : (ext : Extensionality _ _) → Functor HSET (MON ext)
act (FREEMONOID ext) = List'
fun (fmap (FREEMONOID ext) f) = map-list-fun f
preserves-ε (fmap (FREEMONOID ext) f) = refl
preserves-∙ (fmap (FREEMONOID ext) f) = map-list-preserves-∙ f
identity (FREEMONOID ext) {X} = eqMonMorphism ext (ext lem) where
  lem : ∀ xs → map-list-fun id xs ≡ xs
  lem [] = refl
  lem (cons x xs x#xs) = trans (cong (λ z → cons x z tt#) (lem xs)) (cong (cons x xs) (WithIrr.#-irrelevant R⊤ (λ {tt tt → refl}) tt# x#xs))
homomorphism (FREEMONOID ext) {X} {Y} {Z} {f} {g} = eqMonMorphism ext (ext lem) where
  lem : ∀ xs → map-list-fun (λ x → g (f x)) xs ≡ map-list-fun g (map-list-fun f xs)
  lem [] = refl
  lem (cons x xs x#xs) = cong (λ z → cons (g (f x)) z tt#) (lem xs)

----------------
-- Adjunction --
----------------

open Adjunction

fold-∙ : {A : Set} (B : Monoid) → (A → Carrier B) → List A → Carrier B
fold-∙ {A} B f = foldr (λ a b → _∙_ B (f a) b) (ε B)

fold-∙-preserves-∙ : {X : Set} (B : Monoid) (f : X → Carrier B) (x y : List X)
                   → fold-∙ B f (x ++ y) ≡ (B ∙ fold-∙ B f x) (fold-∙ B f y)
fold-∙-preserves-∙ (Mon _ _ _ p _) f [] y = sym $ proj₁ (IsMonoid.identity p) _
fold-∙-preserves-∙ B f (cons x xs x#xs) y = trans (cong (_∙_ B (f x)) (fold-∙-preserves-∙ B f xs y)) (sym $ (IsSemigroup.assoc $ IsMonoid.isSemigroup $ proof B) (f x) (fold-∙ B f xs) (fold-∙ B f y))


MonoidAdjunction : (ext : Extensionality _ _) → (FREEMONOID ext) ⊣ (FORGET ext)
to (MonoidAdjunction ext) f x = fun f (cons x [] [])
fun (from (MonoidAdjunction ext) {A} {B} f) = fold-∙ B f
preserves-ε (from (MonoidAdjunction ext) f) = refl
preserves-∙ (from (MonoidAdjunction ext) {A} {B} f) = fold-∙-preserves-∙ B f
left-inverse-of (MonoidAdjunction ext) {A} {B} h = eqMonMorphism ext (ext λ xs → foldr-universal (fun h) (λ a → _∙_ B (fun h (a ∷# []))) (ε B) (preserves-ε h) (λ a as a#as → trans (cong (fun h) (WithIrr.cons-cong R⊤ (λ p q → refl) refl refl)) (preserves-∙ h (a ∷# []) as)) xs)
right-inverse-of (MonoidAdjunction ext) {A} {B} k = ext (λ x → proj₂ (IsMonoid.identity $ proof B) (k x))
to-natural (MonoidAdjunction ext) f g = refl
