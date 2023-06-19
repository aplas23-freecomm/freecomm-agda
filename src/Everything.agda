{-# OPTIONS --safe --without-K #-}
module Everything where

-- Definitions of various variations on ordered monoids
open import Algebra.Structure.OICM

-- Constantly true and constantly false relations
open import Relation.Const

-- Definitions of categories, functors, adjunctions
open import Category.Base

-- Freshlists for a strict total order
open import Free.IdempotentCommutativeMonoid.Base
open import Free.IdempotentCommutativeMonoid.Properties
open import Free.IdempotentCommutativeMonoid.Adjunction

-- Freshlists for a reflexive total order
open import Free.CommutativeMonoid.Base
open import Free.CommutativeMonoid.Properties
open import Free.CommutativeMonoid.Adjunction

-- Freshlists for an apartness relation
open import Free.LeftRegularMonoid.Base
open import Free.LeftRegularMonoid.Properties
open import Free.LeftRegularMonoid.Adjunction

-- Freshlists for constantly true relation
open import Free.Monoid.Base
open import Free.Monoid.Adjunction

-- Freshlists for constantly false relation
open import Free.PointedSet.Base
open import Free.PointedSet.Properties
open import Free.PointedSet.Adjunction

-- Freshlists for equality relation
open import Free.MysteryStructure.Base

-- Equivalence between Ordering Principle and Set ≃ STO
open import OrderingPrinciple.Base
