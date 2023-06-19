{-# OPTIONS --safe --without-K #-}
module Free.LeftRegularMonoid.Adjunction where

open import Data.Empty
open import Data.Sum
open import Data.Product

open import Relation.Nullary hiding (Irrelevant)
open import Relation.Binary
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)
open import Function

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs

open import Algebra.Structures
open import Algebra.Structure.OICM

open import Data.FreshList.InductiveInductive
open import Free.LeftRegularMonoid.Base
open import Free.LeftRegularMonoid.Properties

open import Category.Base

module _
  {X : Set}
  {_≠_ : X → X → Set}
  (≠-AR : IsPropDecApartnessRelation _≡_ _≠_)
  where

  leftregularBand : IsLeftRegularMonoidWithPropDecApartness _≡_ (λ x y → ¬ (x ≡ y)) (union ≠-AR) []
  IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup (IsLeftRegularMonoidWithPropDecApartness.isICM leftregularBand))) = ≡-isEquivalence
  IsMagma.∙-cong (IsSemigroup.isMagma (IsMonoid.isSemigroup (IsLeftRegularMonoidWithPropDecApartness.isICM leftregularBand))) = cong₂ (union ≠-AR)
  IsSemigroup.assoc (IsMonoid.isSemigroup (IsLeftRegularMonoidWithPropDecApartness.isICM leftregularBand)) = assoc ≠-AR
  IsMonoid.identity (IsLeftRegularMonoidWithPropDecApartness.isICM leftregularBand) = (unitˡ ≠-AR , unitʳ ≠-AR)
  IsLeftRegularMonoidWithPropDecApartness.leftregular leftregularBand = leftregular ≠-AR
  IsLeftRegularMonoidWithPropDecApartness.isApartness leftregularBand = denialApartness ≡-isEquivalence (WithIrr.lift-decEq _≠_ (IsPropDecApartnessRelation.prop ≠-AR) (_≟_ ≠-AR))

---------------------------------------------------------------------------
-- The Category of Left Regular Monoids with Decidable Apartness relations --
---------------------------------------------------------------------------

record LeftRegularMonoidWithPropDecApartness : Set₁ where
  constructor MkLrb
  field
    Carrier : Set
    _¬≈_ : Carrier → Carrier → Set
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    proof : IsLeftRegularMonoidWithPropDecApartness _≡_ _¬≈_ _∙_ ε
open LeftRegularMonoidWithPropDecApartness

record LrbMorphism (A B : LeftRegularMonoidWithPropDecApartness) : Set where
  constructor MkLrbMorphism
  private
    module A = LeftRegularMonoidWithPropDecApartness A
    module B = LeftRegularMonoidWithPropDecApartness B

  field
    fun : Carrier A → Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x) B.∙ (fun y)
open LrbMorphism

lrb-id : ∀ {A} → LrbMorphism A A
fun lrb-id = Function.id
preserves-ε lrb-id = refl
preserves-∙ lrb-id _ _ = refl

lrb-comp : ∀ {A B C} → LrbMorphism A B → LrbMorphism B C → LrbMorphism A C
fun (lrb-comp f g) = (fun g) ∘ (fun f)
preserves-ε (lrb-comp f g) = trans (cong (fun g) (preserves-ε f)) (preserves-ε g)
preserves-∙ (lrb-comp f g) _ _ = trans (cong (fun g) (preserves-∙ f _ _)) (preserves-∙ g _ _)


eqLrbMorphism : Extensionality _ _ → ∀ {A B} → {f g : LrbMorphism A B} → fun f ≡ fun g → f ≡ g
eqLrbMorphism ext {A} {B} {MkLrbMorphism .f refl p∙} {MkLrbMorphism f q q∙} refl
  = cong₂ (MkLrbMorphism f) (uipB refl q) ((ext λ x → ext λ y → uipB (p∙ x y) (q∙ x y)))
  where
    uipB : Irrelevant (_≡_ {A = Carrier B})
    uipB = Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-irrelevant decB
      where
        decB : Decidable (_≡_ {A = Carrier B})
        decB x y with IsLeftRegularMonoidWithPropDecApartness.dec (proof B) x y
        ... | inj₁ x≡y = yes x≡y
        ... | inj₂ x≠y = no λ x≡y → IsPropDecApartnessRelation.irrefl (IsLeftRegularMonoidWithPropDecApartness.isApartness (proof B)) x≡y x≠y

LRB : Extensionality _ _ → Category
Category.Obj (LRB ext) = LeftRegularMonoidWithPropDecApartness
Category.Hom (LRB ext) = LrbMorphism
Category.id (LRB ext) = lrb-id
Category.comp (LRB ext) = lrb-comp
Category.assoc (LRB ext) {A} {B} {C} {D} {f} {g} {h} = eqLrbMorphism ext refl
Category.identityˡ (LRB ext) {A} {B} {f} = eqLrbMorphism ext refl
Category.identityʳ (LRB ext) {A} {B} {f} = eqLrbMorphism ext refl


-------------------------------------------------------------
-- The Category of Propositional Decidable Apartness Types --
-------------------------------------------------------------

record DecApartnessType : Set₁ where
  constructor MkAT
  field
    Carrier : Set
    _¬≈_ : Carrier → Carrier → Set
    proof : IsPropDecApartnessRelation _≡_ _¬≈_
open DecApartnessType

AT : Category
Category.Obj AT = DecApartnessType
Category.Hom AT X Y = Carrier X → Carrier Y
Category.id AT = id
Category.comp AT f g = g ∘ f
Category.assoc AT = refl
Category.identityˡ AT = refl
Category.identityʳ AT = refl

---------------------------
-- The Forgetful Functor --
---------------------------

open Functor

FORGET : (@0 ext : Extensionality _ _) → Functor (LRB ext) AT
act (FORGET _) (MkLrb S _¬≈_ _∙_ ε lrb) = MkAT S _¬≈_ (IsLeftRegularMonoidWithPropDecApartness.isApartness lrb)
fmap (FORGET _) f = fun f
identity (FORGET _) = refl
homomorphism (FORGET _) = refl

----------------------
-- The Free Functor --
----------------------

UL-map : {X Y : DecApartnessType} → (Carrier X → Carrier Y) → UniqueList (proof X) → UniqueList (proof Y)
UL-map f [] = []
UL-map {X} {Y} f (cons x xs fx) = cons (f x) (_-[_] (proof Y) (UL-map {X} {Y} f xs) (f x) ) (remove-removes (proof Y) (UL-map {X} {Y} f xs) (f x))

map-remove : {X Y : DecApartnessType} →
             let _-[_]X = _-[_] (proof X)
                 _-[_]Y = _-[_] (proof Y) in
             (f : Carrier X → Carrier Y) → (xs : UniqueList (proof X)) → (y : Carrier X) →
             (UL-map {X} {Y} f (xs -[ y ]X)) -[ f y ]Y ≡ (UL-map {X} {Y} f xs) -[ f y ]Y
map-remove f [] y = refl
map-remove {X} {Y} f (cons x xs x#xs) y with IsPropDecApartnessRelation.dec (proof X) x y | IsPropDecApartnessRelation.dec (proof Y) (f x) (f y) in eqfxfy
... | inj₁ x≡y  | inj₁ fx≡fy  = cong (_-[_] (proof Y) (UL-map f xs)) (sym fx≡fy)
... | inj₁ x≡y  | inj₂ ¬fx≈fy = ⊥-elim (IsPropDecApartnessRelation.irrefl (proof Y) (cong f x≡y) ¬fx≈fy)
... | inj₂ ¬x≈y | inj₁ fx≡fy  rewrite eqfxfy = begin
  mapf (xs -[ y ]X) -[ f x ]Y
    ≡⟨ cong (λ z → mapf (xs -[ y ]X) -[ z ]Y) fx≡fy ⟩
  mapf (xs -[ y ]X) -[ f y ]Y
    ≡⟨ map-remove {X} {Y} f xs y ⟩
  mapf xs -[ f y ]Y
    ≡⟨ cong (λ z → mapf xs -[ z ]Y) (sym fx≡fy) ⟩
  mapf xs -[ f x ]Y
    ∎ where
      open ≡-Reasoning
      mapf = UL-map {X} {Y} f
      unionX = union (proof X)
      unionY = union (proof Y)
      _-[_]X = _-[_] (proof X)
      _-[_]Y = _-[_] (proof Y)

... | inj₂ ¬x≈y | inj₂ ¬fx≈fy rewrite eqfxfy = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof Y)) refl (begin
  (mapf (xs -[ y ]X) -[ f x ]Y) -[ f y ]Y
    ≡⟨ -[]-order-irrelevant (proof Y) (mapf (xs -[ y ]X)) (f x) (f y) ⟩
  (mapf (xs -[ y ]X) -[ f y ]Y) -[ f x ]Y
    ≡⟨ cong (_-[ f x ]Y) (map-remove {X} {Y} f xs y) ⟩
  (mapf xs -[ f y ]Y) -[ f x ]Y
    ≡⟨ -[]-order-irrelevant (proof Y) (mapf xs) (f y) (f x) ⟩
  (mapf xs -[ f x ]Y) -[ f y ]Y
    ∎) where
      open ≡-Reasoning
      mapf = UL-map {X} {Y} f
      unionX = union (proof X)
      unionY = union (proof Y)
      _-[_]X = _-[_] (proof X)
      _-[_]Y = _-[_] (proof Y)

map-union : {X Y : DecApartnessType} → (f : Carrier X → Carrier Y) → (xs ys : UniqueList (proof X)) →
            UL-map {X} {Y} f (union (proof X) xs ys) ≡ union (proof Y) (UL-map {X} {Y} f xs) (UL-map {X} {Y} f ys)
map-union f [] ys = refl
map-union {X} {Y} f (cons x xs x#xs) ys = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof Y)) refl (begin
  mapf (unionX xs ys -[ x ]X) -[ f x ]Y
    ≡⟨ cong (λ w → mapf w -[ f x ]Y) (remove-union (proof X) xs ys x)  ⟩
  mapf (unionX (xs -[ x ]X) (ys -[ x ]X)) -[ f x ]Y
    ≡⟨ cong (λ w → mapf (unionX w (ys -[ x ]X)) -[ f x ]Y) (remove-fresh-idempotent (proof X) xs x x#xs) ⟩
  mapf (unionX xs (ys -[ x ]X)) -[ f x ]Y
    ≡⟨ cong (_-[ f x ]Y) (map-union {X} {Y} f xs (ys -[ x ]X)) ⟩
  unionY (mapf xs) (mapf (ys -[ x ]X)) -[ f x ]Y
    ≡⟨ remove-union (proof Y) (mapf xs) (mapf (ys -[ x ]X)) (f x) ⟩
  unionY (mapf xs -[ f x ]Y) ((mapf (ys -[ x ]X)) -[ f x ]Y)
    ≡⟨ cong₂ unionY
             (sym (remove-fresh-idempotent (proof Y) (mapf xs -[ f x ]Y) (f x) (remove-removes (proof Y) (mapf xs) (f x))))
             (map-remove {X} {Y} f ys x) ⟩
  unionY (mapf xs -[ f x ]Y -[ f x ]Y) (mapf ys -[ f x ]Y)
    ≡⟨ sym (remove-union (proof Y) (mapf xs -[ f x ]Y) (mapf ys) (f x)) ⟩
  unionY (mapf xs -[ f x ]Y) (mapf ys) -[ f x ]Y
  ∎) where
    open ≡-Reasoning
    mapf = UL-map {X} {Y} f
    unionX = union (proof X)
    unionY = union (proof Y)
    _-[_]X = _-[_] (proof X)
    _-[_]Y = _-[_] (proof Y)

UNIQUELIST : (ext : Extensionality _ _) → Functor AT (LRB ext)
act (UNIQUELIST ext) (MkAT X _¬≈_ isAT) = MkLrb (UniqueList isAT) _ (union isAT) [] (leftregularBand isAT)
fmap (UNIQUELIST ext) {X} {Y} f = MkLrbMorphism (UL-map {X} {Y} f) refl (map-union {X} {Y} f)
identity (UNIQUELIST ext) {X} = eqLrbMorphism ext (ext lemma)
  where
    lemma : ∀ xs → UL-map id xs ≡ xs
    lemma [] = refl
    lemma (cons x xs x#xs) = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof X)) refl
                                               (trans (cong (λ w → _-[_] (proof X) w x) (lemma xs) )
                                                      (remove-fresh-idempotent (proof X) xs x x#xs))
homomorphism (UNIQUELIST ext) {X} {Y} {Z} {f} {g} = eqLrbMorphism ext (ext lemma)
  where
    lemma : ∀ xs → UL-map (λ x → g (f x)) xs ≡ UL-map g (UL-map f xs)
    lemma [] = refl
    lemma (cons x xs x#xs) = WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof Z)) refl
                                               (begin
                                                 mapgf  xs -[ g (f x) ]Z
                                                   ≡⟨ cong (_-[ g (f x) ]Z) (lemma xs) ⟩
                                                 mapg (mapf xs) -[ g (f x) ]Z
                                                   ≡⟨ sym (map-remove {Y} {Z} g (mapf xs) (f x)) ⟩
                                                 mapg (mapf xs -[ f x ]Y) -[ g (f x) ]Z
                                                   ∎)
     where
      open ≡-Reasoning
      mapf  = UL-map {X} {Y} f
      mapg  = UL-map {Y} {Z} g
      mapgf = UL-map {X} {Z} (λ x → g (f x))
      _-[_]Y = _-[_] (proof Y)
      _-[_]Z = _-[_] (proof Z)





-----------------------------------
-- The Free-Forgetful Adjunction --
-----------------------------------

open Adjunction

foldr-∙ : (X : DecApartnessType) → (B : LeftRegularMonoidWithPropDecApartness) →
          (h : Carrier X → Carrier B) →
          UniqueList (proof X) → Carrier B
foldr-∙ X B h = foldr (λ x b → _∙_ B (h x) b) (ε B)

foldr-∙-leftregular : (X : DecApartnessType) → (B : LeftRegularMonoidWithPropDecApartness) →
                      let _-[_]X = _-[_] (proof X) in
                      (h : Carrier X → Carrier B) →
                      (ys : UniqueList (proof X)) → (x : Carrier X) → (b : Carrier B) →
                      _∙_ B (_∙_ B (h x) b) (foldr-∙ X B h (ys -[ x ]X))  ≡ _∙_ B (_∙_ B (h x) b) (foldr-∙ X B h ys)
foldr-∙-leftregular X B h [] x b = refl
foldr-∙-leftregular X B h (cons y ys y#ys) x b with IsPropDecApartnessRelation.dec (proof X) y x
... | inj₁ refl = begin
  (h y ∙' b) ∙' foldr-∙' ys
    ≡⟨ cong (_∙' foldr-∙' ys) (sym (IsLeftRegularMonoidWithPropDecApartness.leftregular (proof B) (h y) b)) ⟩
  ((h y ∙' b) ∙' h y) ∙' foldr-∙' ys
    ≡⟨ IsLeftRegularMonoidWithPropDecApartness.assoc (proof B) (h y ∙' b) (h y) (foldr-∙' ys) ⟩
  (h y ∙' b) ∙' (h y ∙' foldr-∙' ys)
    ∎ where
        open ≡-Reasoning
        _∙'_ = _∙_ B
        foldr-∙' = foldr-∙ X B h
... | inj₂ ¬y≡x = begin
  (h x ∙' b) ∙' (h y ∙' foldr-∙' (ys -[ x ]X))
    ≡⟨ assocB (h x) b (h y ∙' foldr-∙' (ys -[ x ]X)) ⟩
  h x ∙' (b ∙' (h y ∙' foldr-∙' (ys -[ x ]X)))
    ≡⟨ cong (h x ∙'_) (sym (assocB b (h y) (foldr-∙' (ys -[ x ]X)))) ⟩
  h x ∙' ((b ∙' h y) ∙' foldr-∙' (ys -[ x ]X))
    ≡⟨ sym (assocB (h x) (b ∙' h y) (foldr-∙' (ys -[ x ]X))) ⟩
  (h x ∙' (b ∙' h y)) ∙' foldr-∙' (ys -[ x ]X)
    ≡⟨ foldr-∙-leftregular X B h ys x (b ∙' h y) ⟩
  (h x ∙' (b ∙' h y)) ∙' foldr-∙' ys
    ≡⟨ assocB (h x) (b ∙' h y) (foldr-∙' ys) ⟩
  h x ∙' ((b ∙' h y) ∙' foldr-∙' ys)
    ≡⟨ cong (h x ∙'_) (assocB b (h y) (foldr-∙' ys)) ⟩
  h x ∙' (b ∙' (h y ∙' foldr-∙' ys))
    ≡⟨ sym (assocB (h x) b (h y ∙' foldr-∙' ys)) ⟩
  (h x ∙' b) ∙' (h y ∙' foldr-∙' ys)
    ∎ where
        open ≡-Reasoning
        _∙'_ = _∙_ B
        foldr-∙' = foldr-∙ X B h
        _-[_]X = _-[_] (proof X)
        assocB = IsLeftRegularMonoidWithPropDecApartness.assoc (proof B)

foldr-∙-union : (X : DecApartnessType) → (B : LeftRegularMonoidWithPropDecApartness) →
                (h : Carrier X → Carrier B) →
                (xs ys : UniqueList (proof X)) →
                foldr-∙ X B h (union (proof X) xs ys) ≡ _∙_ B (foldr-∙ X B h xs) (foldr-∙ X B h ys)
foldr-∙-union X B h [] ys
  = sym (proj₁ (IsLeftRegularMonoidWithPropDecApartness.identity (proof B)) (foldr-∙ X B h ys))
foldr-∙-union X B h (cons x xs x#xs) ys = begin
  h x ∙' foldr-∙' (unionX xs ys -[ x ]X)
    ≡⟨ cong (λ w → h x ∙' foldr-∙' w) (remove-union-fresh (proof X) xs ys x x#xs) ⟩
  h x ∙' foldr-∙' (unionX xs (ys -[ x ]X))
    ≡⟨ cong (h x ∙'_) (foldr-∙-union X B h xs (ys -[ x ]X)) ⟩
  h x ∙' (foldr-∙' xs ∙' foldr-∙' (ys -[ x ]X))
      ≡⟨ sym (IsLeftRegularMonoidWithPropDecApartness.assoc (proof B) (h x) (foldr-∙' xs) (foldr-∙' (ys -[ x ]X))) ⟩
  (h x ∙' foldr-∙' xs) ∙' foldr-∙' (ys -[ x ]X)
    ≡⟨ foldr-∙-leftregular X B h ys x (foldr-∙' xs) ⟩
  (h x ∙' (foldr-∙' xs)) ∙' (foldr-∙' ys)
    ∎ where
        open ≡-Reasoning
        _∙'_ = _∙_ B
        foldr-∙' = foldr-∙ X B h
        _-[_]X = _-[_] (proof X)
        unionX = union (proof X)

UL-Adjunction : (ext : Extensionality _ _) → (UNIQUELIST ext) ⊣ (FORGET ext)
to (UL-Adjunction ext) f x = fun f (cons x [] [])
from (UL-Adjunction ext) {X} {B} h = MkLrbMorphism (foldr-∙ X B h) refl (foldr-∙-union X B h)
left-inverse-of (UL-Adjunction ext) {X} {B} h = eqLrbMorphism ext (ext lemma)
  where
    lemma : (xs : UniqueList (proof X)) → foldr (λ x → B ∙ fun h (cons x [] [])) (ε B) xs ≡ fun h xs
    lemma [] = sym (preserves-ε h)
    lemma (cons x xs x#xs) = begin
      fun h (cons x [] []) ∙' foldr-∙' xs
       ≡⟨ cong (fun h (cons x [] []) ∙'_) (lemma xs) ⟩
      fun h (cons x [] []) ∙' fun h xs
       ≡⟨ sym (preserves-∙ h (cons x [] []) xs) ⟩
      fun h (unionX (cons x [] []) xs)
       ≡⟨ cong (fun h) (WithIrr.cons-cong _ (IsPropDecApartnessRelation.prop (proof X)) refl (remove-fresh-idempotent (proof X) xs x x#xs)) ⟩
      fun h (cons x xs x#xs)
        ∎ where
        open ≡-Reasoning
        _∙'_ = _∙_ B
        foldr-∙' = foldr (λ x b → fun h (cons x [] []) ∙' b) (ε B)
        _-[_]X = _-[_] (proof X)
        unionX = union (proof X)
right-inverse-of (UL-Adjunction ext) {X} {B} f = ext (λ x → proj₂ (IsLeftRegularMonoidWithPropDecApartness.identity (proof B)) (f x))
to-natural (UL-Adjunction ext) f g = ext (λ _ → ext (λ _ → refl))
