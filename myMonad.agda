module myMonad {A : Set} where

  record MyMonad (M : Set → Set) : Set₁ where
    constructor
      makeMonad
    field
      _≅ₘ_   : M A → M A → Set
      return : ∀ {A : Set} → A → M A 
      _>>=_  : ∀ {A B : Set} → M B → (B → M A) → M A 
      law₁   : ∀ {B : Set} → (x : B) (f : B → M A) 
                             → (((return x) >>= f) ≅ₘ (f x))
      law₂   : (t : M A) → (t >>= return) ≅ₘ t
      law₃   : ∀ {B C : Set} → (t : M C) (f : C → M B) (g : B → M A) 
                             → ((t >>= f) >>= g) ≅ₘ (t >>= (λ x → f x >>= g))

  open MyMonad public

 