{-# OPTIONS --without-K --sized-types #-}

module CoNaturalInstances.ConcurrentMonoidD where

open import Size
open import Data.Nat as Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Function.Equivalence using (_⇔_)
open import Data.Sum

open import CoNaturalsD
open import Structures.ConcurrentMonoid

∼eq : IsEquivalence ([ ∞ ]_∼_)
∼eq = record { refl = reflexive-∼ _
             ; sym = symmetric-∼
             ; trans = transitive-∼ }

∼preord : IsPreorder ([ ∞ ]_∼_) ([ ∞ ]_≤_)
∼preord = record { isEquivalence = ∼eq
                 ; reflexive = ∼→≤
                 ; trans = transitive-≤ }

conaturalsD : ConcurrentMonoid (Conat ∞)
conaturalsD = makeConcurrentMonoid
                ([ ∞ ]_∼_)
                ∼eq
                ([ ∞ ]_≤_)
                ∼preord
                zero
                _+_
                +-left-identity
                +-right-identity
                (λ x y z → +-assoc x {y} {z} {∞})
                max
                (max-left-identity {∞})
                (max-right-identity {∞})
                (max-assoc {∞})
                interchange
