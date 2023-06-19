{-# OPTIONS --safe --without-K #-}
module Free.PointedSet.Properties where

open import Data.FreshList.InductiveInductive
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Const

open import Data.Unit
open import Data.Empty

open import Free.PointedSet.Base

---------------------------
-- Maybe preserves hsets --
---------------------------

module _ {X : Set} where

  Code : Maybe X → Maybe X → Set
  Code [] [] = ⊤
  Code [] (just y) = ⊥
  Code (just x) [] = ⊥
  Code (just x) (just y) = x ≡ y

  encodeRefl : (x : Maybe X) → Code x x
  encodeRefl [] = tt
  encodeRefl (just x) = refl

  encode : {x y : Maybe X} → x ≡ y → Code x y
  encode refl = encodeRefl _

  decode : {x y : Maybe X} → Code x y → x ≡ y
  decode {[]} {[]} tt = refl
  decode {[]} {just y} ()
  decode {just x} {just y} x≡y = cong just x≡y

  decodeEncodeRefl : (x : Maybe X) → decode (encodeRefl x) ≡ refl
  decodeEncodeRefl [] = refl
  decodeEncodeRefl (just x) = refl

  decodeEncode : {x y : Maybe X} → (p : x ≡ y) → decode (encode p) ≡ p
  decodeEncode refl = decodeEncodeRefl _

  prop-Code : Irrelevant (_≡_ {A = X}) → Irrelevant Code
  prop-Code prop-X {[]} {[]} p q = refl
  prop-Code prop-X {[]} {just x} ()
  prop-Code prop-X {just x} {just y} p q = prop-X p q

  MaybehSet : Irrelevant (_≡_ {A = X}) → Irrelevant (_≡_ {A = Maybe X})
  MaybehSet prop-X p q = begin
    p
      ≡⟨ sym (decodeEncode p) ⟩
    decode (encode p)
      ≡⟨ cong decode (prop-Code prop-X (encode p) (encode q)) ⟩
    decode (encode q)
      ≡⟨ decodeEncode q ⟩
    q
      ∎ where open ≡-Reasoning
