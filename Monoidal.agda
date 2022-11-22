module Monoidal where

  record Monoidal (M : Set → Set) : Set₁ where
    constructor
      makeMonoidal
    field
      _≅ₘ_   : ∀ {A} → M A → M A → Set
      unit   : ⊤
      merge  : ∀ {A B : Set} → M A → M B → M (A × B)
      idr    : ∀ {A : Set} → (a : M A) → (merge a unit) ≅ₘ (fmap (λ a → (a , tt)) a)
      assoc  : ∀ {A B C : Set} → (a : M A) (b : M B) (c : M C) 
                → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) ≅ₘ (merge a (merge b c))
      
  open Monoidal public

-- fmap lo defino como un campo mas??
-- la id es solo a la derecha??