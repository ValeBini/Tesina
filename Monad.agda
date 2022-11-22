module Monad where

  record Monad (M : Set → Set) : Set₁ where
    constructor
      makeMonad
    field
      _≅ₘ_   : ∀ {A} → M A → M A → Set
      return : ∀ {A : Set} → A → M A
      _>>=_  : ∀ {A B : Set} → M B → (B → M A) → M A
      law₁   : ∀ {A B : Set} → (x : B) (f : B → M A)
                             → (((return x) >>= f) ≅ₘ (f x))
      law₂   : ∀ {A} → (t : M A) → (t >>= return) ≅ₘ t
      law₃   : ∀ {A B C : Set} → (t : M C) (f : C → M B) (g : B → M A)
                             → ((t >>= f) >>= g) ≅ₘ (t >>= (λ x → f x >>= g))

  open Monad public
