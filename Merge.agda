open import Data.Product as Prod 
open import Codata.Musical.Notation
open import Data.Bool.Base
open import Relation.Binary as B hiding (Rel)

open import Partiality

private
    variable
        A B C : Set

merge : A ⊥ → B ⊥ → (A × B) ⊥
merge (now a)   (now b)   = now (a , b)
merge (now a)   (later b) = later (♯ (merge (now a) (♭ b)))
merge (later a) (now b)   = later (♯ (merge (♭ a) (now b)))
merge (later a) (later b) = later (♯ (merge (♭ a) (♭ b)))

norm-prod⊥ : ((A × B) × C) ⊥ → (A × B × C) ⊥ 
norm-prod⊥ (now ((a , b) , c)) = now (a , b , c)
norm-prod⊥ (later x) = later (♯ (norm-prod⊥ (♭ x)))


module ProdEquality {A B C : Set} {_∼A_ : A → A → Set} {_∼B_ : B → B → Set} {_∼C_ : C → C → Set} where

  data Rel : A × B × C → A × B × C → Set where
      assoc≡ : ∀ {a₁ a₂ b₁ b₂ c₁ c₂} (a₁∼a₂ : a₁ ∼A a₂) (b₁∼b₂ : b₁ ∼B b₂) (c₁∼c₂ : c₁ ∼C c₂) →
                Rel (a₁ , b₁ , c₁) (a₂ , b₂ , c₂) 

  _assoc×-≡_ :  A × B × C → A × B × C → Set
  _assoc×-≡_ = Rel

  refl : Reflexive _∼A_ → Reflexive _∼B_ → Reflexive _∼C_ → Reflexive _assoc×-≡_ 
  refl ra rb rc = assoc≡ ra rb rc 

  sym : Symmetric _∼A_ → Symmetric _∼B_ → Symmetric _∼C_ → Symmetric _assoc×-≡_ 
  sym sa sb sc (assoc≡ a₁∼a₂ b₁∼b₂ c₁∼c₂) = assoc≡ (sa a₁∼a₂) (sb b₁∼b₂) (sc c₁∼c₂)

  trans : Transitive _∼A_ → Transitive _∼B_ → Transitive _∼C_ → Transitive _assoc×-≡_ 
  trans ta tb tc (assoc≡ a₁∼a₂ b₁∼b₂ c₁∼c₂) (assoc≡ a₂∼a₃ b₂∼b₃ c₂∼c₃) = 
                  assoc≡ (ta a₁∼a₂ a₂∼a₃) (tb b₁∼b₂ b₂∼b₃) (tc c₁∼c₂ c₂∼c₃)

module WeakMergeAssoc {A B C : Set} {_∼A_ : A → A → Set} {_∼B_ : B → B → Set} {_∼C_ : C → C → Set} where

  open ProdEquality {A} {B} {C} {_∼A_} {_∼B_} {_∼C_}
  open Equality {A × B × C} _assoc×-≡_ using (_≈_)
  open Equality.Rel

  rec : ∀ {A} → A ⊥ → A ⊥
  rec (now x) = now x
  rec (later x) = ♭ x

  associative : Reflexive _∼A_ → Reflexive _∼B_ → Reflexive _∼C_ 
                               → (a : A ⊥) (b : B ⊥) (c : C ⊥) 
                               → (norm-prod⊥ (merge (merge a b) c)) ≈ (merge a (merge b c))
  associative ra rb rc (now a)   (now b)   (now c)   = now (refl ra rb rc)
  associative ra rb rc (now a)   (now b)   (later c) = later (♯ (associative ra rb rc (now a) (now b) (♭ c)))
  associative ra rb rc (now a)   (later b) (now c)   = later (♯ (associative ra rb rc (now a) (♭ b) (now c)))
  associative ra rb rc (now a)   (later b) (later c) = later (♯ (associative ra rb rc (now a) (♭ b) (♭ c)))
  associative ra rb rc (later a) (now b)   (now c)   = later (♯ (associative ra rb rc (♭ a) (now b) (now c)))
  associative ra rb rc (later a) (now b)   (later c) = later (♯ (associative ra rb rc (♭ a) (now b) (♭ c)))
  associative ra rb rc (later a) (later b) (now c)   = later (♯ (associative ra rb rc (♭ a) (♭ b) (now c)))
  associative ra rb rc (later a) (later b) (later c) = later (♯ (associative ra rb rc (♭ a) (♭ b) (♭ c))) 
