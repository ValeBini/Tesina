open import Relation.Binary.Structures

module Structures.Monoid where

  record Monoid (M : Set) : Set₁ where
    constructor
      makeMonoid
    field
      _≅ₘ_    : M → M → Set
      eqₘ     : IsEquivalence _≅ₘ_
      zeroₘ   : M
      _+ₘ_    : M → M → M
      idl     : (x : M) → (zeroₘ +ₘ x) ≅ₘ x
      idr     : (x : M) → (x +ₘ zeroₘ) ≅ₘ x
      assoc   : (x : M) (y : M) (z : M) → (x +ₘ (y +ₘ z)) ≅ₘ ((x +ₘ y) +ₘ z)

  open Monoid public