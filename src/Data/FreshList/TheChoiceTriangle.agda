{-# OPTIONS --type-in-type #-}

module Util.SortedList.TheChoiceTriangle where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤; tt)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; ≢-sym; subst; cong) renaming (isEquivalence to ≡-isEq)
open import Relation.Nullary

open import Function

open import Util.SortedList.FreeCommMon renaming (PropDecTotalOrder to DTO-obj)
open import Util.SortedList.FreeForgetful-NoMonotonicity renaming (StrictTotalOrder to STO-obj)
open import Util.SortedList.WithDupes
open import Util.Category
open import Util.Category.Adjunctions
open import Util.OICM


{-

-- Show that:
  -- (1) DTO and STO are equivalent
  -- (2) DTO/STO being equivalent to Set would imply LEM. This is obvious, since trichotomy implies dec eq, and dec eq is explicity included in DTO.
  --     Other direction is interesting though - is LEM enough to linearly order any set, or do you need some choice principle?
  -- (3) OCM and OICM are not equivalent. Trivial. [a,a] is an obj in OCM but not OICM. Also not really interesting.

-- The category of sets with decidable equality.
DecSet : Category
Category.Obj DecSet = Σ[ X ∈ Set ] Decidable (_≡_ {A = X})
Category.Hom DecSet (A , _) (B , _) = A → B
Category.id DecSet = id
Category.comp DecSet f g = g ∘ f
Category.assoc DecSet = refl
Category.identityˡ DecSet = refl
Category.identityʳ DecSet = refl

-- TODO : prove DecSet is a subcat of Set, but that they aren't equivalent.
-- We can get this for cheap without talking about morphisms at all;
-- it's enough that the inclusion functor DecSet->Set is not full.

-- Clearly PDTO and STO are not equivalent to Set - their objects have decidable equality, but not all sets do.
-- So what about DecSet? Totality and antisymmetry foil the obvious attempts at free orders. Empty order and diagonal order are not total, and the complete order is not antisymmetric.

-- "There exists a set that can't be linearly ordered" is equivalent to the negation of the axiom of choice (according to unsourced internet, at least. need to verify)
-- (Is the constructively weaker "¬ (all sets can be linearly ordered)" also anti-choice?)
-- Agda obviously doesn't validate full-fat choice, but I think it also doesn't it refute it? (I know that countable choice is a theorem)
-- So we shouldn't be able to show that such a non-linearly-orderable set does not exist.
-- But, this statement may still require classical logic, even if it is anti-choice.
-- So we may be able to show that it implies LEM?

-- Foundational questions :
--
-- 1) DecSet is clearly a strict category. Is Set? Not constructively, right? Does strict constructively mean exactly "has decidable equality on objects"?
-- 2)
-}


-- Want to show that:
  -- (1) DTO and STO are equivalent categories.
  -- (2) DTO/STO being equivalent to Set would imply LEM. This is obvious, since trichotomy implies dec eq, and dec eq is explicity included in DTO.
  --     Other direction is interesting though - is LEM enough to linearly order any set, or do you need some choice principle?
  --     If the answer is "no, LEM is enough", then we should additionally be able to prove that they are equivalent to DecSet.
  -- (3) OCM and OICM are not equivalent. Trivial. [a,a] is an obj in OCM but not OICM. Also not really interesting.

-----------------------
-- PART 1: DTO ≅ STO --
-----------------------

-- Remember: These are weird categories. The morphisms are just functions on the underlying sets, and don't preserve any of the ordering.

≤→< : DTO-obj → STO-obj
STO-obj.Carrier (≤→< R) = DTO-obj.Carrier R
STO-obj._<_ (≤→< R) a b = (DTO-obj._≤_ R a b) × (a ≢ b)
IsStrictTotalOrder.isEquivalence (STO-obj.proof (≤→< R)) = ≡-isEq
IsStrictTotalOrder.trans (STO-obj.proof (≤→< R)) (i≤j , i≢j) (j≤k , j≢k) = (trans $ DTO-obj.proof R) i≤j j≤k , λ { refl → i≢j ((antisym $ DTO-obj.proof R) i≤j j≤k)} where open IsPropDecTotalOrder
IsStrictTotalOrder.compare (STO-obj.proof (≤→< R)) x y with (total $ DTO-obj.proof R) x y | (_≟_ $ DTO-obj.proof R) x y
... | p | yes refl = tri≈ (λ p → proj₂ p refl) refl (λ p → proj₂ p refl)
... | inj₁ x≤y | no x≢y = tri< (x≤y , x≢y) x≢y (λ p → x≢y $ (antisym $ DTO-obj.proof R) x≤y (proj₁ p))  where open IsPropDecTotalOrder
... | inj₂ y≤x | no x≢y = tri> (λ p → x≢y ((antisym $ DTO-obj.proof R) (proj₁ p) y≤x)) x≢y (y≤x , ≢-sym x≢y) where open IsPropDecTotalOrder

<→≤ : STO-obj → DTO-obj
DTO-obj.Carrier (<→≤ R) = STO-obj.Carrier R
DTO-obj._≤_ (<→≤ R) a b = (STO-obj._<_ R a b) ⊎ (a ≡ b)
IsPreorder.isEquivalence (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R)))))) = ≡-isEq
IsPreorder.reflexive (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R)))))) refl = inj₂ refl
IsPreorder.trans (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R)))))) (inj₁ i<j) (inj₁ j<k) = inj₁ ((trans $ STO-obj.proof R) i<j j<k) where open IsStrictTotalOrder
IsPreorder.trans (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R)))))) (inj₁ i<j) (inj₂ refl) = inj₁ i<j
IsPreorder.trans (IsPartialOrder.isPreorder (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R)))))) (inj₂ refl) q = q
IsPartialOrder.antisym (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R))))) (inj₁ i<j) (inj₁ j<i) = ⊥-elim ((asym $ STO-obj.proof R) i<j j<i) where open IsStrictTotalOrder
IsPartialOrder.antisym (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R))))) (inj₁ x) (inj₂ refl) = refl
IsPartialOrder.antisym (IsTotalOrder.isPartialOrder (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R))))) (inj₂ refl) q = refl
IsTotalOrder.total (IsDecTotalOrder.isTotalOrder (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R)))) x y with IsStrictTotalOrder.compare (STO-obj.proof R) x y 
... | tri< a ¬b ¬c = inj₁ (inj₁ a)
... | tri≈ ¬a b ¬c = inj₁ (inj₂ b)
... | tri> ¬a ¬b c = inj₂ (inj₁ c)
IsDecTotalOrder._≟_ (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R))) = IsStrictTotalOrder._≟_  (STO-obj.proof R)
IsDecTotalOrder._≤?_ (IsPropDecTotalOrder.isDTO (DTO-obj.proof (<→≤ R))) x y with IsStrictTotalOrder.compare (STO-obj.proof R) x y
... | tri< a ¬b ¬c = yes $ inj₁ a
... | tri≈ ¬a b ¬c = yes $ inj₂ b
... | tri> ¬a ¬b c = no (λ { (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b})
IsPropDecTotalOrder.≤-prop (DTO-obj.proof (<→≤ R)) = {!!}
-- did a silly thing, built the truncation into the SList type via erasure, rather than into the relations. So this is a problem for now. Need to clean up and change a lot probably.

eqDTO : (A B : DTO-obj)
      → (eqCarrier : DTO-obj.Carrier A ≡ DTO-obj.Carrier B)                                                            -- If they have the same carriers
      → ((x y : DTO-obj.Carrier A) → DTO-obj._≤_ A x y ≡ DTO-obj._≤_ B (subst id eqCarrier x) (subst id eqCarrier y))  -- and the same relation (after some subst hell)
      → A ≡ B                                                                                                          -- then they are the same.
eqDTO (MkTo X R p) (MkTo .X S q) refl eqRel rewrite ext (λ i → ext (λ j → eqRel i j)) = cong (MkTo X S) {!!} -- true if IsPropDecTotalOrder is propositional? See OICM.agda >> PDTO-irrelevant

eqSTO : (A B : STO-obj)
      → (eqCarrier : STO-obj.Carrier A ≡ STO-obj.Carrier B) -- if they have the same carriers
      → ((x y : STO-obj.Carrier A) → STO-obj._<_ A x y ≡ STO-obj._<_ B (subst id eqCarrier x) (subst id eqCarrier y))  -- and the same relation (after some subst hell)
      → A ≡ B -- then they are the same
eqSTO (MkSto X R p) (MkSto .X S q) refl eqRel rewrite ext (λ i → ext (λ j → eqRel i j)) = cong (MkSto X S) {!!}

-- -- They are inverse in both directions.
-- ≤→<→≤ : ∀ x → <→≤ (≤→< x) ≃ x
-- ≤→<→≤ x = ?

-- eqDTO (<→≤ (≤→< x)) x refl lem where
--   lem : (A B : DTO-obj.Carrier x) → (<→≤ (≤→< x) DTO-obj.≤ A) B ≡ (x DTO-obj.≤ subst id refl A) (subst id refl B)
--   lem A B = {!(x DTO-obj.≤ A) B!} -- can prove up to iso, for sure. Does that give us propositional equality in this case? Probably not, because

<→≤→< : ∀ x → ≤→< (<→≤ x) ≡ x
<→≤→< x = eqSTO (≤→< (<→≤ x)) x refl lem where
  lem : (A B : STO-obj.Carrier x) → (≤→< (<→≤ x) STO-obj.< A) B ≡ (x STO-obj.< subst id refl A) (subst id refl B)
  lem A B = {!!}


DTO→STO : Functor PDTO STO
Functor.act DTO→STO = ≤→<
Functor.fmap DTO→STO = id
Functor.identity DTO→STO = refl
Functor.homomorphism DTO→STO = refl

STO→DTO : Functor STO PDTO
Functor.act STO→DTO = <→≤
Functor.fmap STO→DTO = id
Functor.identity STO→DTO = refl
Functor.homomorphism STO→DTO = refl

-- DTO≅STO : PDTO ≅ STO
-- _≅_.S DTO≅STO = DTO→STO
-- _≅_.T DTO≅STO = STO→DTO
-- _≅_.idL DTO≅STO = eqFunctor (ext ≤→<→≤) (ext (λ f → ext (λ x → {!!})))
-- _≅_.idR DTO≅STO = eqFunctor (ext <→≤→<) {!!}
