open import Data.Product as Prod
open import Data.Unit

module Concurrent where

  record Concurrent (M : Set → Set) : Set₁ where
    constructor
      makeConcurrent
    field
      _≅ₘ_   : ∀ {A} → M A → M A → Set
      return : ∀ {A : Set} → A → M A
      _>>=_  : ∀ {A B : Set} → M B → (B → M A) → M A
      monad₁ : ∀ {A B : Set} → (x : B) (f : B → M A)
                             → (((return x) >>= f) ≅ₘ (f x))
      monad₂ : ∀ {A} → (t : M A) → (t >>= return) ≅ₘ t
      monad₃ : ∀ {A B C : Set} → (t : M C) (f : C → M B) (g : B → M A)
                             → ((t >>= f) >>= g) ≅ₘ (t >>= (λ x → f x >>= g))
      unit   : M ⊤
      merge  : ∀ {A B : Set} → M A → M B → M (A × B)
      idr    : ∀ {A : Set} → (a : M A) → (merge a unit) ≅ₘ (a >>= (λ a → return (a , tt)))
      idl    : ∀ {B : Set} → (b : M B) → (merge unit b) ≅ₘ (b >>= (λ b → return (tt , b)))
      assoc  : ∀ {A B C : Set} → (a : M A) (b : M B) (c : M C) 
                → ((merge (merge a b) c) >>= (λ {((a , b) , c) → return (a , (b , c))})) ≅ₘ (merge a (merge b c))
      

  open Concurrent public
