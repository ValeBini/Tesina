\begin{code}
module Structures.Monad where

open import Relation.Binary.Structures
\end{code}

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