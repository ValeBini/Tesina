{-# OPTIONS --without-K #-}

open import Data.Product as Prod
open import Data.Unit
open import Relation.Binary.Structures

module Structures.ConcurrentMonad where

  record ConcurrentMonad (M : Set → Set) : Set₁ where
    constructor
      makeConcurrentMonad
    field
      _≅ₘ_    : ∀ {A} → M A → M A → Set
      eqₘ     : ∀ {A} → IsEquivalence (_≅ₘ_ {A})
      _≲ₘ_    : ∀ {A} → M A → M A → Set 
      porderₘ : ∀ {A} → IsPartialOrder (_≅ₘ_ {A}) (_≲ₘ_ {A})
      return  : ∀ {A : Set} → A → M A
      _>>=_   : ∀ {A B : Set} → M B → (B → M A) → M A
      comp≲ₘ  : ∀ {A B : Set} → (a₁ a₂ : M A) → (f₁ f₂ : A → M B) 
                  → a₁ ≲ₘ a₂ → (∀ (a : A) → (f₁ a) ≲ₘ (f₂ a)) → (a₁ >>= f₁) ≲ₘ (a₂ >>= f₂) 
      monad₁  : ∀ {A B : Set} → (x : B) (f : B → M A)
                              → (((return x) >>= f) ≅ₘ (f x))
      monad₂  : ∀ {A} → (t : M A) → (t >>= return) ≅ₘ t
      monad₃  : ∀ {A B C : Set} → (t : M C) (f : C → M B) (g : B → M A)
                              → ((t >>= f) >>= g) ≅ₘ (t >>= (λ x → f x >>= g))
      unit    : M ⊤
      merge   : ∀ {A B : Set} → M A → M B → M (A × B)
      mcomp≲ₘ : ∀ {A B : Set} → (a₁ a₂ : M A) → (b₁ b₂ : M B) → a₁ ≲ₘ a₂ → b₁ ≲ₘ b₂ 
                  → (merge a₁ b₁) ≲ₘ (merge a₂ b₂)
      idr     : ∀ {A : Set} → (a : M A) → (merge a unit) ≅ₘ (a >>= (λ a → return (a , tt)))
      idl     : ∀ {B : Set} → (b : M B) → (merge unit b) ≅ₘ (b >>= (λ b → return (tt , b)))
      assoc   : ∀ {A B C : Set} → (a : M A) (b : M B) (c : M C) 
                 → ((merge (merge a b) c) >>= (λ {((a , b) , c) → return (a , (b , c))})) ≅ₘ (merge a (merge b c))
      comm    : ∀ {A B : Set} → (a : M A) (b : M B) → (merge a b) ≅ₘ ((merge b a) >>= (λ {(a , b) → return (b , a)}))
      ichange : ∀ {A B C D : Set} → (a : M A) (b : M B) (f : A → M C) (g : B → M D) 
                 → (merge (a >>= f) (b >>= g)) ≲ₘ ((merge a b) >>= (λ { (a , b) → (merge (f a) (g b)) }))

  open ConcurrentMonad public
