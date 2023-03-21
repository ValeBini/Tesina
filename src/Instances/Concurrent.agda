{-# OPTIONS --guardedness #-}

module Instances.Concurrent where

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

bind : A ⊥ → (A → B ⊥) → B ⊥
bind (now x)   f = f x
bind (later x) f = later (♯ (bind (♭ x) f))

merge : A ⊥ → B ⊥ → (A × B) ⊥
merge (now a)   (now b)   = now (a , b)
merge (now a)   (later b) = later (♯ (merge (now a) (♭ b)))
merge (later a) (now b)   = later (♯ (merge (♭ a) (now b)))
merge (later a) (later b) = later (♯ (merge (♭ a) (♭ b)))

unit : ⊤ ⊥
unit = now tt


module Weak (_∼_ : ∀ {A} → A → A → Set) (refl∼ : ∀ {A} → Reflexive (_∼_ {A})) where

    module _ {A : Set} {_∼_ : A → A → Set} (refl∼ : Reflexive _∼_) where

      open Equality _∼_ using (_≈_)
      open Equality.Rel
      open Equivalence using (refl)

      left-identity : (x : B) (f : B → A ⊥) → bind (now x) f ≈ f x
      left-identity x f = refl refl∼

      right-identity : (t : A ⊥) → bind t now ≈ t
      right-identity (now   x) = refl refl∼
      right-identity (later x) = later (♯ (right-identity (♭ x)))

      bind-associative : (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥)
                      → bind (bind x f) g ≈ bind x (λ y → bind (f y) g)
      bind-associative (now   x) f g = refl refl∼
      bind-associative (later x) f g = later (♯ bind-associative (♭ x) f g)

  
    module _ {A B C : Set} {_∼_ : A × B × C → A × B × C → Set} (reflABC : Reflexive _∼_) where

      open Equality {A × B × C} _∼_ using (_≈_)
      open Equality.Rel

      merge-associative : (a : A ⊥) (b : B ⊥) (c : C ⊥)
                    → (bind (merge (merge a b) c) (λ {((a , b) , c) → now (a , (b , c))}) ) ≈ (merge a (merge b c))
      merge-associative (now a)   (now b)   (now c)   = now reflABC
      merge-associative (now a)   (now b)   (later c) = later (♯ (merge-associative (now a) (now b) (♭ c)))
      merge-associative (now a)   (later b) (now c)   = later (♯ (merge-associative (now a) (♭ b) (now c)))
      merge-associative (now a)   (later b) (later c) = later (♯ (merge-associative (now a) (♭ b) (♭ c)))
      merge-associative (later a) (now b)   (now c)   = later (♯ (merge-associative (♭ a) (now b) (now c)))
      merge-associative (later a) (now b)   (later c) = later (♯ (merge-associative (♭ a) (now b) (♭ c)))
      merge-associative (later a) (later b) (now c)   = later (♯ (merge-associative (♭ a) (♭ b) (now c)))
      merge-associative (later a) (later b) (later c) = later (♯ (merge-associative (♭ a) (♭ b) (♭ c)))
  

    module _ {A : Set} {_∼_ : (A × ⊤) → (A × ⊤) → Set} (reflA×⊤ : Reflexive _∼_) where

      open Equality {A × ⊤} _∼_ using (_≈_)
      open Equality.Rel

      rid : (a : A ⊥) → (merge a unit) ≈ (bind a (λ a → now (a , tt)))
      rid (now x)   = now reflA×⊤
      rid (later x) = later (♯ (rid (♭ x)))

    module _ {A : Set} {_∼_ : (⊤ × A) → (⊤ × A) → Set} (refl⊤×A : Reflexive _∼_) where

      open Equality {⊤ × A} _∼_ using (_≈_)
      open Equality.Rel

      lid : (a : A ⊥) → (merge unit a) ≈ (bind a (λ a → now (tt , a)))
      lid (now x)   = now refl⊤×A
      lid (later x) = later (♯ (lid (♭ x)))

    _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})

    open import Records.Concurrent hiding (unit; merge)

    partiality : Concurrent _⊥
    partiality = makeConcurrent 
                    _≈⊥_ 
                    now 
                    bind 
                    (left-identity refl∼) 
                    (right-identity refl∼) 
                    (bind-associative refl∼)
                    unit
                    merge
                    (rid refl∼)
                    (lid refl∼)
                    (merge-associative refl∼)

    
module Strong (_∼_ : ∀ {A} → A → A → Set) (refl∼ : ∀ {A} → Reflexive (_∼_ {A})) where

    module _ {A : Set} {_∼_ : A → A → Set} (refl∼ : Reflexive _∼_) where

      open Equality _∼_ using (_≅_)
      open Equality.Rel
      open Equivalence using (refl)

      left-identity : (x : B) (f : B → A ⊥) → bind (now x) f ≅ f x
      left-identity x f = refl refl∼

      right-identity : (t : A ⊥) → bind t now ≅ t
      right-identity (now   x) = refl refl∼
      right-identity (later x) = later (♯ (right-identity (♭ x)))

      bind-associative : (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥)
                      → bind (bind x f) g ≅ bind x (λ y → bind (f y) g)
      bind-associative (now   x) f g = refl refl∼
      bind-associative (later x) f g = later (♯ bind-associative (♭ x) f g)

  
    module _ {A B C : Set} {_∼_ : A × B × C → A × B × C → Set} (reflABC : Reflexive _∼_) where

      open Equality {A × B × C} _∼_ using (_≅_)
      open Equality.Rel

      merge-associative : (a : A ⊥) (b : B ⊥) (c : C ⊥)
                    → (bind (merge (merge a b) c) (λ {((a , b) , c) → now (a , (b , c))}) ) ≅ (merge a (merge b c))
      merge-associative (now a)   (now b)   (now c)   = now reflABC
      merge-associative (now a)   (now b)   (later c) = later (♯ (merge-associative (now a) (now b) (♭ c)))
      merge-associative (now a)   (later b) (now c)   = later (♯ (merge-associative (now a) (♭ b) (now c)))
      merge-associative (now a)   (later b) (later c) = later (♯ (merge-associative (now a) (♭ b) (♭ c)))
      merge-associative (later a) (now b)   (now c)   = later (♯ (merge-associative (♭ a) (now b) (now c)))
      merge-associative (later a) (now b)   (later c) = later (♯ (merge-associative (♭ a) (now b) (♭ c)))
      merge-associative (later a) (later b) (now c)   = later (♯ (merge-associative (♭ a) (♭ b) (now c)))
      merge-associative (later a) (later b) (later c) = later (♯ (merge-associative (♭ a) (♭ b) (♭ c)))
  

    module _ {A : Set} {_∼_ : (A × ⊤) → (A × ⊤) → Set} (reflA×⊤ : Reflexive _∼_) where

      open Equality {A × ⊤} _∼_ using (_≅_)
      open Equality.Rel

      rid : (a : A ⊥) → (merge a unit) ≅ (bind a (λ a → now (a , tt)))
      rid (now x)   = now reflA×⊤
      rid (later x) = later (♯ (rid (♭ x)))

    module _ {A : Set} {_∼_ : (⊤ × A) → (⊤ × A) → Set} (refl⊤×A : Reflexive _∼_) where

      open Equality {⊤ × A} _∼_ using (_≅_)
      open Equality.Rel

      lid : (a : A ⊥) → (merge unit a) ≅ (bind a (λ a → now (tt , a)))
      lid (now x)   = now refl⊤×A
      lid (later x) = later (♯ (lid (♭ x)))

    _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≅⊥_ {A} = Equality._≅_ {A} (_∼_ {A})

    open import Records.Concurrent hiding (unit; merge)

    partiality : Concurrent _⊥
    partiality = makeConcurrent 
                    _≅⊥_ 
                    now 
                    bind 
                    (left-identity refl∼) 
                    (right-identity refl∼) 
                    (bind-associative refl∼)
                    unit
                    merge
                    (rid refl∼)
                    (lid refl∼)
                    (merge-associative refl∼)