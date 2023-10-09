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

∼partord : IsPartialOrder ([ ∞ ]_∼_) ([ ∞ ]_≤_)
∼partord = record { isPreorder = 
                   record { isEquivalence = ∼eq
                           ; reflexive = ∼→≤
                           ; trans = transitive-≤ } 
                 ; antisym = antisymmetric-≤ }

-- force≤suc : {x : Conat′ ∞} {y : Conat ∞} → [ ∞ ] suc x ≤ y → [ ∞ ] force x ≤ y 
-- force≤suc {x} {suc y} (suc fx≤sy) with force x 
-- ...                                | zero = zero
-- ...                                | suc x₁ = suc λ { .force → force≤suc {x₁} {force y} (force fx≤sy) }

-- +compatible : (x y z w : Conat ∞) → [ ∞ ] x ≤ z → [ ∞ ] y ≤ w → [ ∞ ] x + y ≤ z + w 
-- +compatible zero     zero     z        w  x≤z        y≤w = zero
-- +compatible zero     (suc y)  zero     w  x≤z        y≤w = y≤w
-- +compatible zero     (suc y)  (suc z)  w  x≤z        y≤w = suc (λ { .force → +compatible zero (force y) (force z) w zero (force≤suc y≤w) }) 
-- +compatible (suc x)  zero     (suc z)  w  (suc x≤z)  y≤w = suc (λ { .force → +compatible (force x) zero (force z) w (force x≤z) zero })
-- +compatible (suc x)  (suc y)  (suc z)  w  (suc x≤z)  y≤w = suc (λ { .force → +compatible (force x) (suc y) (force z) w (force x≤z) y≤w })

-- maxcompatible : (x y z w : Conat ∞) → [ ∞ ] x ≤ z → [ ∞ ] y ≤ w → [ ∞ ] max x y ≤ max z w 
-- maxcompatible zero     zero z w x≤z y≤w = zero
-- maxcompatible zero (suc y) zero w x≤z y≤w = y≤w
-- maxcompatible zero (suc y) (suc z) (suc w) x≤z (suc y≤w) = suc (λ { .force → maxcompatible zero (force y) (force z) (force w) zero (force y≤w) })
-- maxcompatible (suc x) zero (suc z) w (suc x≤z) y≤w = suc (λ { .force → maxcompatible (force x) zero (force z) (pred w) (force x≤z) zero })
-- maxcompatible (suc x) (suc y) (suc z) (suc w) (suc x≤z) (suc y≤w) = suc (λ { .force → maxcompatible (force x) (force y) (force z) (force w) (force x≤z) (force y≤w) })

conaturalsD : ConcurrentMonoid (Conat ∞)
conaturalsD = makeConcurrentMonoid
                ([ ∞ ]_∼_)
                ∼eq
                ([ ∞ ]_≤_)
                ∼partord
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
