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


module Weak (_∼_ : ∀ {A} → A → A → Set) (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where

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

    open import Structures.MonoidalFunctor hiding (unit; merge; fmap)

    _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})

    open Equivalence using (refl; sym; trans) 
  
    eq≈⊥ : ∀ {A} → IsEquivalence (_≈⊥_ {A})
    eq≈⊥ = record 
            { refl = refl (IsEquivalence.refl eq∼) ; 
              sym = sym (IsEquivalence.sym eq∼) tt ; 
              trans = trans (IsEquivalence.trans eq∼) }

    monoidalPartiality : MonoidalFunctor _⊥
    monoidalPartiality = makeMonoidalFunctor 
                          _≈⊥_ 
                          eq≈⊥
                          unit 
                          merge 
                          fmap 
                          (rid (IsEquivalence.refl eq∼))
                          (lid (IsEquivalence.refl eq∼)) 
                          (associative (IsEquivalence.refl eq∼))


module Strong (_∼_ : ∀ {A} → A → A → Set) (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where

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

    open import Structures.MonoidalFunctor hiding (unit; merge; fmap)

    _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≅⊥_ {A} = Equality._≅_ {A} (_∼_ {A})

    open Equivalence using (refl; sym; trans) 
  
    eq≅⊥ : ∀ {A} → IsEquivalence (_≅⊥_ {A})
    eq≅⊥ = record 
            { refl = refl (IsEquivalence.refl eq∼) ; 
              sym = sym (IsEquivalence.sym eq∼) tt ; 
              trans = trans (IsEquivalence.trans eq∼) }

    monoidalPartiality : MonoidalFunctor _⊥
    monoidalPartiality = makeMonoidalFunctor 
                          _≅⊥_ 
                          eq≅⊥
                          unit 
                          merge 
                          fmap 
                          (rid (IsEquivalence.refl eq∼))
                          (lid (IsEquivalence.refl eq∼)) 
                          (associative (IsEquivalence.refl eq∼))

