open import Data.Product as Prod
open import Data.Unit

module Structures.Monoidal where

  record Monoidal (M : Set → Set) : Set₁ where
    constructor
      makeMonoidal
    field
      _≅ₘ_   : ∀ {A} → M A → M A → Set
      unit   : M ⊤
      merge  : ∀ {A B : Set} → M A → M B → M (A × B)
      fmap   : ∀ {A B : Set} → (A → B) → M A → M B
      idr    : ∀ {A : Set} → (a : M A) → (merge a unit) ≅ₘ (fmap (λ a → (a , tt)) a)
      idl    : ∀ {B : Set} → (b : M B) → (merge unit b) ≅ₘ (fmap (λ b → (tt , b)) b)
      assoc  : ∀ {A B C : Set} → (a : M A) (b : M B) (c : M C) 
                → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) ≅ₘ (merge a (merge b c))
      -- comm   : ∀ {A B : Set} → (a : M A) (b : M B) → merge a b ≅ₘ fmap swap (merge b a)
      
  open Monoidal public
