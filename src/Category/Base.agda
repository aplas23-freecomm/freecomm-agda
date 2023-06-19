{-# OPTIONS --safe --without-K #-}
module Category.Base where

open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional
open import Function as Fun using (_∘′_)
open import Data.Product hiding (map)

----------------------------
-- Categories
----------------------------

-- We only consider "large" categories in this work
record Category : Set₂ where
  eta-equality

  field
    Obj : Set₁
    Hom : Obj -> Obj -> Set

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category

----------------------------
-- Functors
----------------------------

record Functor (C D : Category) : Set₁ where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {X Y} (f : C.Hom X Y) → D.Hom (act X) (act Y)

  field -- laws
    identity     : ∀ {X} → fmap (C.id {X}) ≡ D.id {act X}
    homomorphism : ∀ {X Y Z} {f : C.Hom X Y}{g : C.Hom Y Z} →
                   fmap (C.comp f g) ≡ D.comp (fmap f) (fmap g)
open Functor

{-
-- How to prove Functors equal
eqFunctor : {C D : Category}{F G : Functor C D} ->
            (p : act F ≡ act G) ->
            (∀ {A B} → subst (λ z → Hom C A B -> Hom D (z A) (z B)) p (fmap F) ≡ (fmap G {A} {B})) ->
            F ≡ G
eqFunctor {G = G} refl q with iext (λ {A} → iext (λ {B} → q {A} {B}))
  where
    postulate ext : ∀ {a b} → Extensionality a b
    iext : ∀ {a b} → ExtensionalityImplicit a b
    iext = implicit-extensionality ext
... | refl = eqFunctor' {G = G} (implicit-extensionality ext λ {A} → uip _ _) (iext (iext (iext (iext (iext (uip _ _))))))
  where
  postulate ext : ∀ {a b} → Extensionality a b
  iext : ∀ {a b} → ExtensionalityImplicit a b
  iext = implicit-extensionality ext
  eqFunctor' : ∀ {C} {D} {G : Functor C D}
               {identity' identity'' : {A : Obj C} → fmap G {A} (Category.id C) ≡ Category.id D}
               {homomorphism' homomorphism'' : {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} →
               (_≡_ {A = ∀ {A} → fmap G {A} (Category.id C) ≡ Category.id D} identity' identity'') ->
               (_≡_ {A = {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} homomorphism' homomorphism'') ->
             _≡_ {A = Functor C D} (record { act = act G; fmap = fmap G; identity = identity'; homomorphism = homomorphism' })
                                   (record { act = act G; fmap = fmap G; identity = identity''; homomorphism = homomorphism'' })
  eqFunctor' refl refl = refl
-}

idFunctor : {C : Category} -> Functor C C
act idFunctor X = X
fmap idFunctor f = f
identity idFunctor = refl
homomorphism idFunctor = refl

compFunctor : {A B C : Category} -> Functor A B → Functor B C → Functor A C
act (compFunctor F G) =  (act G) ∘′ (act F)
fmap (compFunctor F G) f = fmap G (fmap F f)
identity (compFunctor F G) = trans (cong (fmap G) (identity F)) (identity G)
homomorphism (compFunctor F G) = trans (cong (fmap G) (homomorphism F)) (homomorphism G)


Full : {A B : Category} → Functor A B → Set₁
Full {A} {B} S = ∀ {x y} {g : Category.Hom B (act S x) (act S y)} → Σ[ f ∈ Category.Hom A x y ] g ≡ (fmap S f)

Faithful : {A B : Category} → Functor A B → Set₁
Faithful {A} {B} S = ∀ {x y} {f g : Category.Hom A x y} → fmap S f ≡ fmap S g → f ≡ g

FullyFaithful : {A B : Category} → Functor A B → Set₁
FullyFaithful S = Full S × Faithful S


----------------------------
-- Natural transformations
----------------------------

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set₁ where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → D.Hom (F.act X) (G.act X)
    natural     : ∀ X Y (f : C.Hom X Y) →
                  D.comp (F.fmap f) (transform Y) ≡ D.comp (transform X) (G.fmap f)
open NaturalTransformation

{-
-- How to prove natural transformations equal
eqNatTrans : {C D : Category}{F G : Functor C D} ->
             (η ρ : NaturalTransformation F G) ->
             ((X : Category.Obj C) -> transform η X ≡ transform ρ X) ->
             η ≡ ρ
eqNatTrans {C} η ρ p with ext p
  where   postulate ext : Extensionality _ _
... | refl = eqNatTrans' η ρ refl (ext λ X → ext λ Y → ext λ f → uip _ _) where
  postulate ext : ∀ {a b} → Extensionality a b
  eqNatTrans' : {C D : Category}{F G : Functor C D} ->
                (η ρ : NaturalTransformation F G) ->
                (p : transform η ≡ transform ρ) ->
                subst (λ z → (X Y : Category.Obj C)(f : Category.Hom C X Y) → Category.comp D (fmap F f) (z Y) ≡ Category.comp D (z X) (fmap G f)) p (natural η) ≡ (natural ρ) ->
               η ≡ ρ
  eqNatTrans' η ρ refl refl = refl
-}

----------------------------
-- Adjunctions
----------------------------

record Adjunction {C D : Category}
                  (F : Functor C D)
                  (G : Functor D C) : Set₁ where

  open Category
  open Functor
  open NaturalTransformation

  field
    to   : {X : Obj C}{B : Obj D} -> Hom D (act F X)        B  -> Hom C X         (act G B)
    from : {X : Obj C}{B : Obj D} -> Hom C X         (act G B) -> Hom D (act F X)        B
    left-inverse-of : ∀ {X B} →  (h : Hom D (act F X) B) -> from (to h) ≡ h
    right-inverse-of : ∀ {X B} → (k : Hom C X (act G B)) -> to (from k) ≡ k

    to-natural : {X X' : Obj C}{B B' : Obj D} (f : Hom C X' X)(g : Hom D B B') ->
                   (λ h → comp C f (comp C h (fmap G g))) ∘′ (to {X} {B})
                     ≡
                   (to {X'} {B'}) ∘′ (λ k → comp D (fmap F f) (comp D k g))

_⊣_ = Adjunction

----------------------------
-- The category of Sets
----------------------------


-- Note: these are really wild categories, so TYPE is a category (not an ∞-category)
TYPE : Category
Category.Obj TYPE = Set
Category.Hom TYPE A B = A -> B
Category.id TYPE = Fun.id
Category.comp TYPE f g = g Fun.∘′ f
Category.assoc TYPE = refl
Category.identityˡ TYPE = refl
Category.identityʳ TYPE = refl

record hSet : Set₁ where
  constructor hset
  field
    Carrier : Set
    isSet : Irrelevant (_≡_ {A = Carrier})

HSET : Category
Category.Obj HSET = hSet
Category.Hom HSET A B = hSet.Carrier A → hSet.Carrier B
Category.id HSET = Fun.id
Category.comp HSET f g = g Fun.∘′ f
Category.assoc HSET = refl
Category.identityˡ HSET = refl
Category.identityʳ HSET = refl


----------------------------
-- Monads
----------------------------

record Monad (C : Category) : Set₁ where
  open Category C
  open Functor

  field
    functor : Functor C C

  private
    M = functor

  field
    returnNT : NaturalTransformation idFunctor M
    joinNT   : NaturalTransformation (compFunctor M M) M

  return = NaturalTransformation.transform returnNT
  join   = NaturalTransformation.transform joinNT

  field
    returnJoin : {X : Obj C}    -> comp C (return (act M X)) (join X) ≡ id C
    mapReturnJoin : {X : Obj C} -> comp C (fmap M (return X)) (join X)  ≡ id C
    joinJoin : {X : Obj C}      -> comp C (join (act M X)) (join X) ≡ comp C (fmap M (join X)) (join X)

  open Functor M


--------------------------------
-- Isomorphisms in a category --
--------------------------------

record Iso (C : Category)(X Y : Obj C) : Set₁ where
  field
    to : Hom C X Y
    from : Hom C Y X
    to-from : comp C to from ≡ id C
    from-to : comp C from to ≡ id C
