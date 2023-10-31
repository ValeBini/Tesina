open import Data.Product as Prod
open import Data.Unit
open import Relation.Binary.Structures

module Structures.MonoidalFunctor where

  record MonoidalFunctor (M : Set → Set) : Set₁ where
    constructor
      makeMonoidalFunctor
    field
      _≅ₘ_   : ∀ {A} → M A → M A → Set
      eqₘ    : ∀ {A} → IsEquivalence (_≅ₘ_ {A})
      unit   : M ⊤
      merge  : ∀ {A B : Set} → M A → M B → M (A × B)
      fmap   : ∀ {A B : Set} → (A → B) → M A → M B
      idr    : ∀ {A : Set} → (a : M A) 
              → (merge a unit) ≅ₘ (fmap (λ a → (a , tt)) a)
      idl    : ∀ {B : Set} → (b : M B) 
              → (merge unit b) ≅ₘ (fmap (λ b → (tt , b)) b)
      assoc  : ∀ {A B C : Set} → (a : M A) (b : M B) (c : M C) 
              → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) 
                                                          ≅ₘ (merge a (merge b c))
      -- comm : ∀ {A B : Set} → (a : M A) (b : M B) 
      --          → merge a b ≅ₘ fmap swap (merge b a)
      
  open MonoidalFunctor public
