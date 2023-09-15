\begin{code}
{-# OPTIONS --guardedness #-}

module Structures where

open import Relation.Binary.Structures
open import Data.Unit
open import Data.Product as Prod
\end{code}

%<*monoid>
\begin{code}
record Monoid (M : Set) : Set₁ where
  constructor
    makeMonoid
  field
    _≅ₘ_    : M → M → Set
    eqₘ     : IsEquivalence _≅ₘ_
    zeroₘ   : M
    _+ₘ_    : M → M → M
    idl    : (x : M) → (zeroₘ +ₘ x) ≅ₘ x
    idr    : (x : M) → (x +ₘ zeroₘ) ≅ₘ x
    assoc  : (x : M) (y : M) (z : M) → (x +ₘ (y +ₘ z)) ≅ₘ ((x +ₘ y) +ₘ z)

open Monoid public
\end{code}
%</monoid>

%<*monad>
\begin{code}
record Monad (M : Set → Set) : Set₁ where
  constructor
    makeMonad
  field
    _≅ₘ_   : ∀ {A} → M A → M A → Set
    eqₘ    : ∀ {A} → IsEquivalence (_≅ₘ_ {A})
    return : ∀ {A : Set} → A → M A
    _≫=_  : ∀ {A B : Set} → M A → (A → M B) → M B
    law₁   : ∀ {A B : Set} → (x : A) (f : A → M B)
                            → (((return x) ≫= f) ≅ₘ (f x))
    law₂   : ∀ {A} → (t : M A) → (t ≫= return) ≅ₘ t
    law₃   : ∀ {A B C : Set} → (t : M A) (f : A → M B) (g : B → M C)
                            → ((t ≫= f) ≫= g) ≅ₘ (t ≫= (λ x → f x ≫= g))

open Monad public
\end{code}
%</monad>

%<*monoidal>
\begin{code}
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
\end{code}
%</monoidal>