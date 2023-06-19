{-# OPTIONS --safe --without-K #-}
module Free.PointedSet.Adjunction where

open import Level
open import Algebra.Definitions
open import Algebra.Structures
open import Function
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Const

open import Data.FreshList.InductiveInductive
open import Free.PointedSet.Base
open import Free.PointedSet.Properties

open import Category.Base

open import Axiom.Extensionality.Propositional

-----------------------------
-- Category of pointed set --
-----------------------------

record PointedSet : Set₁ where
  constructor PSet
  field
    Carrier : Set
    ε : Carrier
    isSet : Irrelevant (_≡_ {A = Carrier})
open PointedSet

record PointedSetMorphism (A B : PointedSet) : Set where
  constructor PSetMorphism
  private
    module A = PointedSet A
    module B = PointedSet B
  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
open PointedSetMorphism

eqPsetMorphism : ∀ {A B} → {f g : PointedSetMorphism A B} → fun f ≡ fun g → f ≡ g
eqPsetMorphism {A} {B} {PSetMorphism .f refl} {PSetMorphism f q} refl
  = cong (PSetMorphism f) (isSet B refl q)

pset-id : ∀ {A} → PointedSetMorphism A A
PointedSetMorphism.fun pset-id = Function.id
PointedSetMorphism.preserves-ε pset-id = refl

pset-comp : ∀ {A B C} → PointedSetMorphism A B → PointedSetMorphism B C → PointedSetMorphism A C
PointedSetMorphism.fun (pset-comp f g) = (fun g) ∘ (fun f)
PointedSetMorphism.preserves-ε (pset-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)

PSET : Category
Category.Obj PSET = PointedSet
Category.Hom PSET = PointedSetMorphism
Category.id PSET = pset-id
Category.comp PSET = pset-comp
Category.assoc PSET = eqPsetMorphism refl
Category.identityˡ PSET = eqPsetMorphism refl
Category.identityʳ PSET = eqPsetMorphism refl


-----------------------
-- Forgetful functor --
-----------------------

open Functor

FORGET : Functor PSET HSET
act FORGET x = hset (Carrier x) (isSet x)
fmap FORGET f x = (fun f) x
identity FORGET = refl
homomorphism FORGET = refl


------------------
-- Free functor --
------------------

Maybe' : hSet → PointedSet
Carrier (Maybe' X) = Maybe (hSet.Carrier X)
ε (Maybe' X) = []
isSet (Maybe' X) = MaybehSet (hSet.isSet X)


fmap-maybe : {X Y : hSet} → (hSet.Carrier X → hSet.Carrier Y) → PointedSetMorphism (Maybe' X) (Maybe' Y)
fun (fmap-maybe f) = map-maybe f
preserves-ε (fmap-maybe f) = refl

MAYBE : (ext : Extensionality _ _) → Functor HSET PSET
act (MAYBE ext) X = Maybe' X
fmap (MAYBE ext) = fmap-maybe
identity (MAYBE ext) = eqPsetMorphism (ext (λ { [] → refl ; (just x) → refl}))
homomorphism (MAYBE ext) = eqPsetMorphism (ext (λ { [] → refl ; (just x) → refl}))


----------------
-- Adjunction --
----------------

open Adjunction

PSetAdjunction : (ext : Extensionality _ _) → (MAYBE ext) ⊣ FORGET
to (PSetAdjunction ext) f x = fun f (just x)
fun (from (PSetAdjunction ext) {B = B} f) [] = ε B
fun (from (PSetAdjunction ext) f) (just x) = f x
preserves-ε (from (PSetAdjunction ext) f) = refl
left-inverse-of (PSetAdjunction ext) h = eqPsetMorphism (ext  λ { [] → sym $ preserves-ε h ; (just x) → refl})
right-inverse-of (PSetAdjunction ext) k = refl
to-natural (PSetAdjunction ext) f g = refl
