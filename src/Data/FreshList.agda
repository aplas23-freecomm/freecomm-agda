{-# OPTIONS --without-K --safe #-}

-- A module for things that should probably be in the standard library but arent.
module Data.FreshList where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty
open import Data.Unit
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nary using (⌊_⌋)
open import Relation.Nullary
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (⌊_⌋)

open import Data.List.Fresh renaming (List# to List#') public
open import Data.List.Fresh.Relation.Unary.All using (All; []; _∷_; all?) renaming (map to all-map) public
open import Data.List.Fresh.Relation.Unary.Any using (Any; here; there; any?) renaming (map to any-map) public

-- The erasure notation is annoying, so this is the only place we will use it.
List# : {X : Set} {R : X -> X -> Set} (R? : Decidable R) -> Set
List# {X} R? = List#' X ⌊ R? ⌋



-- Everything else implicitly needs the freshness relation
module _ {X : Set} {R : X -> X -> Set} {R? : Decidable R} where

  -- _∈_ : X -> List# R? -> Set
  -- x ∈ xs = Any (x ≡_) xs

  -- _∉_ : X -> List# R? -> Set
  -- x ∉ xs = ¬ (Any (x ≡_) xs)


  -- We can turn a proof of All into the "fresh" proof
  -- required by the List# type
  all→fresh : {x : X} {xs : List# R?} -> All (R x) xs -> x # xs
  all→fresh {xs = []} [] = lift tt
  all→fresh {a} {cons x xs f} (px ∷ pxs) with R? a x
  ... | yes p = lift tt , (all→fresh pxs)
  ... | no ¬p = ⊥-elim (¬p px)

  -- If y is fresh for (x ∷ xs), then it's fresh for xs
  fresh-weaken : {x y : X} {xs : List# R?} {fx : x # xs}
               -> y # (cons x xs fx)
               -> y # xs
  fresh-weaken (lift a , b) = b

  -- The inverse to all→fresh; given a fresh, we can make an all
  fresh→all : {x : X} {xs : List# R?} -> x # xs -> All (R x) xs
  fresh→all {xs = []} (lift tt) = []
  fresh→all {x} {cons y ys fy} (lift a , ps) with R? x y
  fresh→all {x} {cons y ys fy} (lift () , ps) | no ¬p
  ... | yes p = p ∷ fresh→all (fresh-weaken {x = y} {y = x} {xs = ys} {fx = fy} ((lift (fromWitness p)) , ps))


  -- Any two freshness proofs for the same x and xs are equal.
  fresh-irrelevant : {x : X}  {xs : List# R?} -> (f g : x # xs) -> f ≡ g
  fresh-irrelevant {xs = []} f g = refl
  fresh-irrelevant {x} {cons x' xs fx} (lift p , ps) (lift q , qs)
    = cong₂ _,_ (cong lift (T<-irrelevant p q)) (fresh-irrelevant ps qs) where
    T<-irrelevant : ∀ {x y} -> (v w : True (R? x y)) -> v ≡ w
    T<-irrelevant {x} {y} v w with R? x y
    ... | yes lt = refl
    T<-irrelevant {x} {y} v () | no ¬lt

  -- If we assume that x≡y and xs≡ys, then we can use our preexisting freshness proof.
  fresh-infer : {x y : X} {xs ys : List# R?} -> x ≡ y -> xs ≡ ys -> x # xs -> y # ys
  fresh-infer refl refl fx = fx

  -- cong₂ doesn't work for dependent functions in general, so here are some specialised versions.
  -- Although there should also be a version which does work in general when the 2nd element
  -- (ie, the freshness/gluability proof here) is propositional.
  cons-cong : {xs ys : List# R?} (x : X) { fx : x # xs } { fy : x # ys } -> xs ≡ ys -> List#'.cons x xs fx ≡ cons x ys fy
  cons-cong x {fx} {fy} refl with fresh-irrelevant fx fy
  ... | refl = refl

  cons-subst : {x : X}  {xs ys : List# R?} {P : List# R? -> Set} (fx : x # xs) (fy : x # ys) -> (eq : xs ≡ ys) -> P (cons x xs fx) -> (P (cons x ys fy))
  cons-subst fx fy refl z with fresh-irrelevant fy fx
  ... | refl = z

  #-trans : Transitive R → (a x : X) (xs : List#' X R) → R a x → x # xs → a # xs
  #-trans R-trans a x [] Rax x#xs = lift tt
  #-trans R-trans a x (cons y ys y#ys) Rax (Rxy , x#ys) = R-trans Rax Rxy , #-trans R-trans a x ys Rax x#ys

  -- If R is transitive, then consing is easier
  cons-trans : Transitive R → (a x : X) (xs : List#' X R) (x#xs : x # xs) (p : R a x) → List#' X R
  cons-trans R-trans a x xs x#xs p = cons a (cons x xs x#xs) (p , #-trans R-trans a x xs p x#xs)

  -- ∈-weaken : ∀ {a x} {xs : List# R?} {fx : x # xs} -> a ≢ x -> a ∈ (cons x xs fx) -> a ∈ xs
  -- ∈-weaken {a} {x} a≢x (here a≡x) = ⊥-elim (a≢x a≡x)
  -- ∈-weaken {a} {x} a≢x (there a∈xs) = a∈xs

  -- Definitions which require decidable equality on X
  module _ (_≟_ : Decidable {A = X} _≡_) where
    -- _∈?_ : (x : X) (xs : List# R?) -> Dec (x ∈ xs)
    -- x ∈? xs = any? (x ≟_) xs

    _≟L_ : (xs ys : List# R?) -> Dec (xs ≡ ys)
    [] ≟L [] = yes refl
    [] ≟L cons y ys fy = no λ ()
    cons x xs fx ≟L [] = no λ ()
    cons x xs fx ≟L cons y ys fy with x ≟ y | xs ≟L ys
    ... | no x≢y   | _        = no λ { refl → x≢y refl}
    ... | _        | no xs≢ys = no λ { refl → xs≢ys refl }
    ... | yes refl | yes refl with fresh-irrelevant fx fy
    ... | refl = yes refl
