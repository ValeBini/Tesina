module myMonad where

  open import Data.Bool.Base using (Bool; false; true)
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Product as Prod hiding (map)
  open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
  open import Function.Base
  open import Function.Bundles using (_⇔_; mk⇔)
  open import Level using (Level; _⊔_)
  open import Relation.Binary as B hiding (Rel)
  import Relation.Binary.Properties.Setoid as SetoidProperties
  open import Relation.Binary.PropositionalEquality as P using (_≡_)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable hiding (map)
  open import Relation.Nullary.Negation

  open import Codata.Musical.Notation

  private
    variable
      A B C : Set
      
  record MyMonad (M : Set → Set) : Set₁ where
    constructor
      makeMonad
    field
      _≅ₘ_ : ∀ {A : Set} → M A → M A → Set
      return : A → M A 
      _>>=_ : M A → (A → M B) → M B 
      law₁ : (x : A) (f : A → M B) 
              → (((return x) >>= f) ≅ₘ (f x))
      law₂ : (t : M A) 
              → (t >>= return) ≅ₘ t
      law₃ : (t : M _) (f : A → M B) (g : B → M C) 
              → ((t >>= f) >>= g) ≅ₘ (t >>= (λ x → f x >>= g))

  open MyMonad public

