{-# OPTIONS --without-K --sized-types #-}

module Instances.ConcurrentMonoid where

open import Size
open import Data.Nat as Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Function.Equivalence using (_⇔_)
open import Data.Sum

open import CoNaturalsS
open import Structures.ConcurrentMonoid

eq-∼ : IsEquivalence ([ ∞ ]_∼_)
eq-∼ = record { refl = reflexive-∼ _
             ; sym = symmetric-∼
             ; trans = transitive-∼ }

partial-≤ : IsPartialOrder ([ ∞ ]_∼_) ([ ∞ ]_≤_)
partial-≤ = record { isPreorder = 
                   record { isEquivalence = eq-∼ 
                           ; reflexive = ∼→≤
                           ; trans = transitive-≤ } 
                   ; antisym = antisymmetric-≤ }

conatConcurrent : ConcurrentMonoid (Conat ∞)
conatConcurrent = makeConcurrentMonoid
                    ([ ∞ ]_∼_)
                    eq-∼ 
                    ([ ∞ ]_≤_)
                    partial-≤
                    zero
                    _+_
                    (λ x y z w → _+-mono_ {∞} {x} {z} {y} {w})
                    +-left-identity
                    +-right-identity
                    (λ x y z → +-assoc x {y} {z} {∞})
                    max
                    (λ x y z w → _max-mono_ {∞} {x} {z} {y} {w})
                    (max-left-identity {∞})
                    (max-right-identity {∞})
                    (max-assoc {∞})
                    max-comm
                    interchange