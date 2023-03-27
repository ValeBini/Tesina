{-# OPTIONS --guardedness #-}

module Instances.Monoidal where

open import Data.Product as Prod
open import Codata.Musical.Notation
open import Data.Bool.Base
open import Relation.Binary as B hiding (Rel)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to prefl)

open import Partiality

private
    variable
        A B C : Set

merge : A ⊥ → B ⊥ → (A × B) ⊥
merge (now a)   (now b)   = now (a , b)
merge (now a)   (later b) = later (♯ (merge (now a) (♭ b)))
merge (later a) (now b)   = later (♯ (merge (♭ a) (now b)))
merge (later a) (later b) = later (♯ (merge (♭ a) (♭ b)))

fmap : ∀ {A B : Set} → (A → B) → (A ⊥ → B ⊥)
fmap f (now x)   = now (f x)
fmap f (later x) = later (♯ (fmap f (♭ x)))

unit : ⊤ ⊥
unit = now tt


module Weak (_∼_ : ∀ {A} → A → A → Set) (refl∼ : ∀ {A} → Reflexive (_∼_ {A})) where

    module _ {A B C : Set} {_∼_ : A × B × C → A × B × C → Set} (reflABC : Reflexive _∼_) where

      open Equality {A × B × C} _∼_ using (_≈_)
      open Equality.Rel

      associative : (a : A ⊥) (b : B ⊥) (c : C ⊥)
                    → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) ≈ (merge a (merge b c))
      associative (now a)   (now b)   (now c)   = now reflABC
      associative (now a)   (now b)   (later c) = later (♯ (associative (now a) (now b) (♭ c)))
      associative (now a)   (later b) (now c)   = later (♯ (associative (now a) (♭ b) (now c)))
      associative (now a)   (later b) (later c) = later (♯ (associative (now a) (♭ b) (♭ c)))
      associative (later a) (now b)   (now c)   = later (♯ (associative (♭ a) (now b) (now c)))
      associative (later a) (now b)   (later c) = later (♯ (associative (♭ a) (now b) (♭ c)))
      associative (later a) (later b) (now c)   = later (♯ (associative (♭ a) (♭ b) (now c)))
      associative (later a) (later b) (later c) = later (♯ (associative (♭ a) (♭ b) (♭ c)))
  

    module _ {A : Set} {_∼_ : (A × ⊤) → (A × ⊤) → Set} (reflA×⊤ : Reflexive _∼_) where

      open Equality {A × ⊤} _∼_ using (_≈_)
      open Equality.Rel

      rid : (a : A ⊥) → (merge a unit) ≈ (fmap (λ a → (a , tt)) a)
      rid (now x)   = now reflA×⊤
      rid (later x) = later (♯ (rid (♭ x)))

    module _ {A : Set} {_∼_ : (⊤ × A) → (⊤ × A) → Set} (refl⊤×A : Reflexive _∼_) where

      open Equality {⊤ × A} _∼_ using (_≈_)
      open Equality.Rel

      lid : (a : A ⊥) → (merge unit a) ≈ (fmap (λ a → (tt , a)) a)
      lid (now x)   = now refl⊤×A
      lid (later x) = later (♯ (lid (♭ x)))

    open import Structures.Monoidal hiding (unit; merge; fmap)

    _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})

    monoidalPartiality : Monoidal _⊥
    monoidalPartiality = makeMonoidal 
                          _≈⊥_ 
                          unit 
                          merge 
                          fmap 
                          (rid refl∼)
                          (lid refl∼) 
                          (associative refl∼)


module Strong (_∼_ : ∀ {A} → A → A → Set) (refl∼ : ∀ {A} → Reflexive (_∼_ {A})) where

    module _ {A B C : Set} {_∼_ : A × B × C → A × B × C → Set} (reflABC : Reflexive _∼_) where

      open Equality {A × B × C} _∼_ using (_≅_)
      open Equality.Rel

      associative : (a : A ⊥) (b : B ⊥) (c : C ⊥)
                    → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) ≅ (merge a (merge b c))
      associative (now a)   (now b)   (now c)   = now reflABC
      associative (now a)   (now b)   (later c) = later (♯ (associative (now a) (now b) (♭ c)))
      associative (now a)   (later b) (now c)   = later (♯ (associative (now a) (♭ b) (now c)))
      associative (now a)   (later b) (later c) = later (♯ (associative (now a) (♭ b) (♭ c)))
      associative (later a) (now b)   (now c)   = later (♯ (associative (♭ a) (now b) (now c)))
      associative (later a) (now b)   (later c) = later (♯ (associative (♭ a) (now b) (♭ c)))
      associative (later a) (later b) (now c)   = later (♯ (associative (♭ a) (♭ b) (now c)))
      associative (later a) (later b) (later c) = later (♯ (associative (♭ a) (♭ b) (♭ c)))
  

    module _ {A : Set} {_∼_ : (A × ⊤) → (A × ⊤) → Set} (reflA×⊤ : Reflexive _∼_) where

      open Equality {A × ⊤} _∼_ using (_≅_)
      open Equality.Rel

      rid : (a : A ⊥) → (merge a unit) ≅ (fmap (λ a → (a , tt)) a)
      rid (now x)   = now reflA×⊤
      rid (later x) = later (♯ (rid (♭ x)))

    module _ {A : Set} {_∼_ : (⊤ × A) → (⊤ × A) → Set} (refl⊤×A : Reflexive _∼_) where

      open Equality {⊤ × A} _∼_ using (_≅_)
      open Equality.Rel

      lid : (a : A ⊥) → (merge unit a) ≅ (fmap (λ a → (tt , a)) a)
      lid (now x)   = now refl⊤×A
      lid (later x) = later (♯ (lid (♭ x)))

    open import Structures.Monoidal hiding (unit; merge; fmap)

    _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≅⊥_ {A} = Equality._≅_ {A} (_∼_ {A})

    monoidalPartiality : Monoidal _⊥
    monoidalPartiality = makeMonoidal 
                          _≅⊥_ 
                          unit 
                          merge 
                          fmap 
                          (rid refl∼)
                          (lid refl∼) 
                          (associative refl∼)


{-
module ProdEquality {A B : Set} {_∼A_ : A → A → Set} {_∼B_ : B → B → Set} where

  data Rel : A × B → A × B → Set where
      prod≡ : ∀ {a₁ a₂ b₁ b₂} (a₁∼a₂ : a₁ ∼A a₂) (b₁∼b₂ : b₁ ∼B b₂) →
                Rel (a₁ , b₁) (a₂ , b₂)

  _×-≡_ :  A × B → A × B → Set
  _×-≡_ = Rel

  refl : Reflexive _∼A_ → Reflexive _∼B_ → Reflexive _×-≡_
  refl ra rb = prod≡ ra rb

  sym : Symmetric _∼A_ → Symmetric _∼B_ → Symmetric _×-≡_
  sym sa sb (prod≡ a₁∼a₂ b₁∼b₂) = prod≡ (sa a₁∼a₂) (sb b₁∼b₂)

  trans : Transitive _∼A_ → Transitive _∼B_ → Transitive _×-≡_
  trans ta tb (prod≡ a₁∼a₂ b₁∼b₂) (prod≡ a₂∼a₃ b₂∼b₃) = prod≡ (ta a₁∼a₂ a₂∼a₃) (tb b₁∼b₂ b₂∼b₃)
-}
{-}
module WeakMergeAssoc {A B C : Set} {_∼A_ : A → A → Set} {_∼B_ : B → B → Set} {_∼C_ : C → C → Set} where

  open ProdEquality {B} {C} {_∼B_} {_∼C_} renaming (_×-≡_ to _b×c-≡_ ; refl to b×c-refl)
  open ProdEquality {A} {B × C} {_∼A_} {_b×c-≡_}
  open Equality {A × B × C} _×-≡_ using (_≈_)
  open Equality.Rel

  associative : Reflexive _∼A_ → Reflexive _∼B_ → Reflexive _∼C_
                  → (a : A ⊥) (b : B ⊥) (c : C ⊥)
                  → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) ≈ (merge a (merge b c))
  associative ra rb rc (now a)   (now b)   (now c)   = now (refl ra (b×c-refl rb rc))
  associative ra rb rc (now a)   (now b)   (later c) = later (♯ (associative ra rb rc (now a) (now b) (♭ c)))
  associative ra rb rc (now a)   (later b) (now c)   = later (♯ (associative ra rb rc (now a) (♭ b) (now c)))
  associative ra rb rc (now a)   (later b) (later c) = later (♯ (associative ra rb rc (now a) (♭ b) (♭ c)))
  associative ra rb rc (later a) (now b)   (now c)   = later (♯ (associative ra rb rc (♭ a) (now b) (now c)))
  associative ra rb rc (later a) (now b)   (later c) = later (♯ (associative ra rb rc (♭ a) (now b) (♭ c)))
  associative ra rb rc (later a) (later b) (now c)   = later (♯ (associative ra rb rc (♭ a) (♭ b) (now c)))
  associative ra rb rc (later a) (later b) (later c) = later (♯ (associative ra rb rc (♭ a) (♭ b) (♭ c)))


module StrongMergeAssoc {A B C : Set} {_∼A_ : A → A → Set} {_∼B_ : B → B → Set} {_∼C_ : C → C → Set} where

  open ProdEquality {B} {C} {_∼B_} {_∼C_} renaming (_×-≡_ to _b×c-≡_ ; refl to b×c-refl)
  open ProdEquality {A} {B × C} {_∼A_} {_b×c-≡_}
  open Equality {A × B × C} _×-≡_ using (_≅_)
  open Equality.Rel

  associative : Reflexive _∼A_ → Reflexive _∼B_ → Reflexive _∼C_
                  → (a : A ⊥) (b : B ⊥) (c : C ⊥)
                  → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) ≅ (merge a (merge b c))
  associative ra rb rc (now a)   (now b)   (now c)   = now (refl ra (b×c-refl rb rc))
  associative ra rb rc (now a)   (now b)   (later c) = later (♯ (associative ra rb rc (now a) (now b) (♭ c)))
  associative ra rb rc (now a)   (later b) (now c)   = later (♯ (associative ra rb rc (now a) (♭ b) (now c)))
  associative ra rb rc (now a)   (later b) (later c) = later (♯ (associative ra rb rc (now a) (♭ b) (♭ c)))
  associative ra rb rc (later a) (now b)   (now c)   = later (♯ (associative ra rb rc (♭ a) (now b) (now c)))
  associative ra rb rc (later a) (now b)   (later c) = later (♯ (associative ra rb rc (♭ a) (now b) (♭ c)))
  associative ra rb rc (later a) (later b) (now c)   = later (♯ (associative ra rb rc (♭ a) (♭ b) (now c)))
  associative ra rb rc (later a) (later b) (later c) = later (♯ (associative ra rb rc (♭ a) (♭ b) (♭ c)))


module WeakUnitMerge {A : Set} {_∼_ : A → A → Set} where

  open ProdEquality {A} {⊤} {_∼_} {_≡_}
  open Equality {A × ⊤} _×-≡_ using (_≈_)
  open Equality.Rel

  merge-unit : Reflexive _∼_ → (a : A ⊥) → (merge a unit) ≈ (fmap (λ a → (a , tt)) a)
  merge-unit ra (now x)   = now (refl ra prefl)
  merge-unit ra (later x) = later (♯ (merge-unit ra (♭ x)))

module StrongUnitMerge {A : Set} {_∼_ : A → A → Set} where

  open ProdEquality {A} {⊤} {_∼_} {_≡_}
  open Equality {A × ⊤} _×-≡_ using (_≅_)
  open Equality.Rel

  merge-unit : Reflexive _∼_ → (a : A ⊥) → (merge a unit) ≅ (fmap (λ a → (a , tt)) a)
  merge-unit ra (now x)   = now (refl ra prefl)
  merge-unit ra (later x) = later (♯ (merge-unit ra (♭ x)))
-}