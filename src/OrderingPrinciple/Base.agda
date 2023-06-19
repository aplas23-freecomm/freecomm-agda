{-# OPTIONS --safe --without-K  #-}
module OrderingPrinciple.Base where

open import Algebra
open import Function as F hiding (id)


{-

open import Data.Product hiding (map)
open import Data.Sum
open import Data.Empty
open import Data.Nat renaming (_<_ to _<N_)
open import Data.Nat.Induction
open import Induction.WellFounded

open import Relation.Binary hiding (NonEmpty; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

open import Data.FreshList.InductiveInductive
open import Free.IdempotentCommutativeMonoid.Base
import Free.IdempotentCommutativeMonoid.Properties as FICM
open import Category.Base

-}

open import Data.Product

open import Relation.Binary -- hiding (NonEmpty; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality renaming (isEquivalence to ≡-isEquivalence)

open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional

open import Category.Base

open import Algebra.Structure.OICM

open import Free.IdempotentCommutativeMonoid.Adjunction

--------------------------------
-- Equivalences of categories --
--------------------------------

NaturalIso : {C D : Category} → (F G : Functor C D) → Set₁
NaturalIso {C} {D} F G = Σ[ F⇒G ∈ NaturalTransformation F G ] Σ[ F⇐G ∈ NaturalTransformation G F ]
                           (∀ (X : Obj C) → comp D (transform F⇒G X) (transform F⇐G X) ≡ id D × comp D  (transform F⇐G X) (transform F⇒G X) ≡ id D)
  where
    open Category
    open NaturalTransformation

IsEquiv : {C D : Category} → Functor C D → Set₁
IsEquiv {C} {D} F = Σ[ G ∈ Functor D C ] (NaturalIso (compFunctor F G) (idFunctor {C}) × NaturalIso (compFunctor G F) (idFunctor {D}))
  where
    open Category
    open Functor

--------------------------
-- Forgetting the order --
--------------------------

module _ where

  open Functor

  FORGETSTO : Functor STO HSET
  act FORGETSTO (MkSto X _<_ proof) = hset X (Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-irrelevant (IsPropStrictTotalOrder._≟_ proof))
  fmap FORGETSTO f = f
  identity FORGETSTO = refl
  homomorphism FORGETSTO = refl

  FORGETOICM : (@0 ext : Extensionality _ _) → Functor (OICM ext) (ICM ext)
  act (FORGETOICM ext) (MkOicm X _<_ _∙_ ε proof) = MkIcm X _∙_ ε (Algebra.Structure.OICM.IsOrderedIdempotentCommutativeMonoid.isICM proof) (IsPropStrictTotalOrder.≈-prop (IsOrderedIdempotentCommutativeMonoid.isSTO proof))
  fmap (FORGETOICM ext) (MkOicmMorphism f preserves-ε preserves-∙) = MkIcmMorphism f preserves-ε preserves-∙
  identity (FORGETOICM ext) = refl
  homomorphism (FORGETOICM ext) = refl

------------------------
-- Ordering Principle --
------------------------

OrderingPrinciple : Set₁
OrderingPrinciple = (X : Set) → Irrelevant (_≡_ {A = X}) → Σ[ _<_ ∈ (X → X → Set) ] (IsPropStrictTotalOrder _≡_ _<_)

-------------------------------------------
-- Ordering Principle gives equivalences --
-------------------------------------------

module _ where

  open Functor

  FREE-STO : OrderingPrinciple → Functor HSET STO
  act (FREE-STO OP) (hset X X-set) =
    let (_<_ , proof) = OP X X-set in MkSto X _<_ proof
  fmap (FREE-STO OP) f = f
  identity (FREE-STO OP) = refl
  homomorphism (FREE-STO OP) = refl

  OP-gives-STO≃Set : OrderingPrinciple → IsEquiv FORGETSTO
  OP-gives-STO≃Set OP = FREE-STO OP ,
                        (record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                          record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                          λ X → refl , refl) ,
                        (record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                          record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                          λ X → refl , refl)


  FREE-OICM : (@0 ext : Extensionality _ _) → OrderingPrinciple → Functor (ICM ext) (OICM ext)
  act (FREE-OICM ext OP) (MkIcm X _∙_ ε isICM ≡-prop) =
    let (_<_ , isSTO) = OP X ≡-prop in MkOicm X _<_ _∙_ ε (record { isICM = isICM ; isSTO = isSTO })
  fmap (FREE-OICM ext OP) (MkIcmMorphism f preserves-ε preserves-∙) = MkOicmMorphism f preserves-ε preserves-∙
  identity (FREE-OICM ext OP) = refl
  homomorphism (FREE-OICM ext OP) = refl

  OP-gives-OICM≃ICM : (ext : Extensionality _ _) → OrderingPrinciple → IsEquiv (FORGETOICM ext)
  OP-gives-OICM≃ICM ext OP = FREE-OICM ext OP ,
                        (record { transform = λ X → MkOicmMorphism F.id refl (λ x y → refl) ; natural = λ X Y f → eqOicmMorphism ext refl } ,
                          record { transform = λ X → MkOicmMorphism F.id refl (λ x y → refl) ; natural = λ X Y f → eqOicmMorphism ext refl } ,
                          λ X → refl , refl) ,
                        (record { transform = λ X → MkIcmMorphism F.id refl (λ x y → refl) ; natural = λ X Y f → eqIcmMorphism ext refl } ,
                          record { transform = λ X → MkIcmMorphism F.id refl (λ x y → refl) ; natural = λ X Y f → eqIcmMorphism ext refl } ,
                          λ X → refl , refl)



------------------------------------------
-- Equivalence gives Ordering Principle --
-----------------------------------------

STO≃Set-gives-OP : IsEquiv FORGETSTO → OrderingPrinciple
STO≃Set-gives-OP (FORGETSTO⁻¹ , ((η , (η⁻¹ , η-inv)) , (ε , (ε⁻¹ , ε-inv)))) X X-set = _<_ , proof
    where
      open NaturalTransformation
      XX = hset X X-set
      X' = PropStrictTotalOrder.Carrier (Functor.act FORGETSTO⁻¹ XX)
      _<'_ = PropStrictTotalOrder._<_ (Functor.act FORGETSTO⁻¹ XX)
      proof' = PropStrictTotalOrder.proof (Functor.act FORGETSTO⁻¹ XX)
      isSTO' = IsPropStrictTotalOrder.isSTO proof'
      _<_ : X → X → Set
      x < y = transform ε⁻¹ XX x <' transform ε⁻¹ XX y
      proof : IsPropStrictTotalOrder _≡_ _<_
      IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO proof) = ≡-isEquivalence
      IsStrictTotalOrder.trans (IsPropStrictTotalOrder.isSTO proof) {i} i<j j<k = IsStrictTotalOrder.trans isSTO' i<j j<k
      IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO proof) x y with IsStrictTotalOrder.compare isSTO' (transform ε⁻¹ XX x) (transform ε⁻¹ XX y)
      ... | tri< x<y ¬x=y' ¬y<x = tri< x<y (λ x=y → ¬x=y' (cong (transform ε⁻¹ XX) x=y)) ¬y<x
      ... | tri≈ ¬x<y x=y' ¬y<x = tri≈ ¬x<y (trans (sym (cong (_$ x) (proj₂ (ε-inv XX)))) (trans (cong (transform ε XX) x=y') (cong (_$ y) (proj₂ (ε-inv XX))))) ¬y<x
      ... | tri> ¬x<y ¬x=y' y<x = tri> ¬x<y (λ x=y → ¬x=y' (cong (transform ε⁻¹ XX) x=y)) y<x
      IsPropStrictTotalOrder.≈-prop proof = X-set
      IsPropStrictTotalOrder.<-prop proof = IsPropStrictTotalOrder.<-prop proof'

-------------------------------------------------------------
-- A version of the Ordering Principle for arbitrary types --
-------------------------------------------------------------

OrderingPrinciple' : Set₁
OrderingPrinciple' = (X : Set) → Σ[ _<_ ∈ (X → X → Set) ] (IsPropStrictTotalOrder _≡_ _<_)

-- This version is equivalent to the forgetful functor from STO to TYPE having an inverse

FORGETSTO' : Functor STO TYPE
Functor.act FORGETSTO' (MkSto X _<_ proof) = X
Functor.fmap FORGETSTO' f = f
Functor.identity FORGETSTO' = refl
Functor.homomorphism FORGETSTO' = refl


FREE-STO' : OrderingPrinciple' → Functor TYPE STO
Functor.act (FREE-STO' op) X =
  let (_<_ , proof) = op X in MkSto X _<_ proof
Functor.fmap (FREE-STO' op) f = f
Functor.identity (FREE-STO' op) = refl
Functor.homomorphism (FREE-STO' op) = refl

OP-gives-STO≃Set' : OrderingPrinciple' → IsEquiv FORGETSTO'
OP-gives-STO≃Set' OP = FREE-STO' OP ,
                      (record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                        record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                        λ X → refl , refl) ,
                      (record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                        record { transform = λ X → F.id ; natural = λ X Y f → refl } ,
                        λ X → refl , refl)

STO≃Set-gives-OP' : IsEquiv FORGETSTO' → OrderingPrinciple'
STO≃Set-gives-OP' (FORGETSTO⁻¹ , ((η , (η⁻¹ , η-inv)) , (ε , (ε⁻¹ , ε-inv)))) X = _<_ , proof
    where
      open NaturalTransformation
      X' = PropStrictTotalOrder.Carrier (Functor.act FORGETSTO⁻¹ X)
      _<'_ = PropStrictTotalOrder._<_ (Functor.act FORGETSTO⁻¹ X)
      proof' = PropStrictTotalOrder.proof (Functor.act FORGETSTO⁻¹ X)
      isSTO' = IsPropStrictTotalOrder.isSTO proof'
      _<_ : X → X → Set
      x < y = transform ε⁻¹ X x <' transform ε⁻¹ X y
      proof : IsPropStrictTotalOrder _≡_ _<_
      IsStrictTotalOrder.isEquivalence (IsPropStrictTotalOrder.isSTO proof) = ≡-isEquivalence
      IsStrictTotalOrder.trans (IsPropStrictTotalOrder.isSTO proof) {i} i<j j<k = IsStrictTotalOrder.trans isSTO' i<j j<k
      IsStrictTotalOrder.compare (IsPropStrictTotalOrder.isSTO proof) x y with IsStrictTotalOrder.compare isSTO' (transform ε⁻¹ X x) (transform ε⁻¹ X y)
      ... | tri< x<y ¬x=y' ¬y<x = tri< x<y (λ x=y → ¬x=y' (cong (transform ε⁻¹ X) x=y)) ¬y<x
      ... | tri≈ ¬x<y x=y' ¬y<x = tri≈ ¬x<y (trans (sym (cong (_$ x) (proj₂ (ε-inv X)))) (trans (cong (transform ε X) x=y') (cong (_$ y) (proj₂ (ε-inv X))))) ¬y<x
      ... | tri> ¬x<y ¬x=y' y<x = tri> ¬x<y (λ x=y → ¬x=y' (cong (transform ε⁻¹ X) x=y)) y<x
      IsPropStrictTotalOrder.≈-prop proof {x} {y} p q = lemma (IsPropStrictTotalOrder.≈-prop proof' (cong (transform ε⁻¹ X) p) (cong (transform ε⁻¹ X) q))
        where
          whisker : ∀ p → p ≡ trans (sym (cong (_$ x) (proj₂ (ε-inv X)))) (trans (cong (transform ε X) (cong (transform ε⁻¹ X) p)) (cong (_$ y) (proj₂ (ε-inv X))))
          whisker refl = sym (trans-symˡ (cong (_$ x) (proj₂ (ε-inv X))))
          lemma : cong (transform ε⁻¹ X) p ≡ cong (transform ε⁻¹ X) q → p ≡ q
          lemma p=q' = begin
            p
              ≡⟨ whisker p ⟩
            trans (sym (cong (_$ x) (proj₂ (ε-inv X)))) (trans (cong (transform ε X) (cong (transform ε⁻¹ X) p)) (cong (_$ y) (proj₂ (ε-inv X))))
              ≡⟨ cong (λ z → trans (sym (cong (_$ x) (proj₂ (ε-inv X)))) (trans (cong (transform ε X) z) (cong (_$ y) (proj₂ (ε-inv X))))) p=q' ⟩
            trans (sym (cong (_$ x) (proj₂ (ε-inv X)))) (trans (cong (transform ε X) (cong (transform ε⁻¹ X) q)) (cong (_$ y) (proj₂ (ε-inv X))))
              ≡⟨ sym (whisker q) ⟩
            q
              ∎ where open ≡-Reasoning
      IsPropStrictTotalOrder.<-prop proof = IsPropStrictTotalOrder.<-prop proof'
