{-# OPTIONS --safe --without-K #-}
module Free.PointedSet.Base where

open import Data.FreshList.InductiveInductive
open import Relation.Const

-- free functor
Maybe : Set → Set
Maybe X = List# {A = X} R⊥

pattern just x = cons x [] []

map-maybe : {X Y : Set} → (X → Y) → Maybe X → Maybe Y
map-maybe f [] = []
map-maybe f (just x) = just (f x)
-- Note Agda is clever enough to not consider `cons x xs x#xs`, because x#xs : ⊥
