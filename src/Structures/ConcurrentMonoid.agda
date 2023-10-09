{-# OPTIONS --without-K #-}

open import Data.Product as Prod
open import Data.Unit
open import Relation.Binary.Structures

module Structures.ConcurrentMonoid where

  record ConcurrentMonoid (M : Set) : Set₁ where
    constructor
      makeConcurrentMonoid
    field
      _≅ₘ_    : M → M → Set
      eqₘ     : IsEquivalence _≅ₘ_
      _≲ₘ_    : M → M → Set 
      porderₘ : IsPartialOrder _≅ₘ_ _≲ₘ_
      zeroₘ   : M
      _+ₘ_    : M → M → M
      scomp≲ₘ : (x y z w : M) → x ≲ₘ z → y ≲ₘ w → (x +ₘ y) ≲ₘ (z +ₘ w)
      sidl    : (x : M) → (zeroₘ +ₘ x) ≅ₘ x
      sidr    : (x : M) → (x +ₘ zeroₘ) ≅ₘ x
      sassoc  : (x : M) (y : M) (z : M) → (x +ₘ (y +ₘ z)) ≅ₘ ((x +ₘ y) +ₘ z)
      maxₘ    : M → M → M
      mcomp≲ₘ : (x y z w : M) → x ≲ₘ z → y ≲ₘ w → (maxₘ x y) ≲ₘ (maxₘ z w)
      midl    : (x : M) → (maxₘ zeroₘ x) ≅ₘ x
      midr    : (x : M) → (maxₘ x zeroₘ) ≅ₘ x
      massoc  : (x : M) (y : M) (z : M) → ((maxₘ (maxₘ x y) z) ≅ₘ (maxₘ x (maxₘ y z)))
      mcomm   : (x y : M) → (maxₘ x y) ≅ₘ (maxₘ y x)
      ichange : (x : M) (y : M) (z : M) (w : M) 
                 → (maxₘ (x +ₘ y) (z +ₘ w)) ≲ₘ ((maxₘ x z) +ₘ (maxₘ y w))

  open ConcurrentMonoid public