module Instances.Monad where

open import Codata.Musical.Notation
open import Relation.Binary as B hiding (Rel)
open import Partiality
open import Agda.Builtin.Unit

private
  variable
    A B C : Set

bind : A ⊥ → (A → B ⊥) → B ⊥
bind (now x)   f = f x
bind (later x) f = later (♯ (bind (♭ x) f))

module Weak (_∼_ : ∀ {A} → A → A → Set) (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where

  module _ {A : Set} {_∼_ : A → A → Set} (refl∼ : Reflexive _∼_) where

    open Equality _∼_ using (_≈_)
    open Equality.Rel
    open Equivalence using (refl)

    left-identity : (x : B) (f : B → A ⊥) → bind (now x) f ≈ f x
    left-identity x f = refl refl∼

    right-identity : (t : A ⊥) → bind t now ≈ t
    right-identity (now   x) = refl refl∼
    right-identity (later x) = later (♯ (right-identity (♭ x)))

    associative : (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥)
                  → bind (bind x f) g ≈ bind x (λ y → bind (f y) g)
    associative (now   x) f g = refl refl∼
    associative (later x) f g = later (♯ associative (♭ x) f g)

  _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
  _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})

  open Equivalence using (refl; sym; trans) 
  
  eq≈⊥ : ∀ {A} → IsEquivalence (_≈⊥_ {A})
  eq≈⊥ = record 
          { refl = refl (IsEquivalence.refl eq∼) ; 
            sym = sym (IsEquivalence.sym eq∼) tt ; 
            trans = trans (IsEquivalence.trans eq∼) }

  open import Structures.Monad

  partiality : Monad _⊥
  partiality = makeMonad 
                _≈⊥_ 
                eq≈⊥
                now 
                bind 
                (left-identity (IsEquivalence.refl eq∼)) 
                (right-identity (IsEquivalence.refl eq∼)) 
                (associative (IsEquivalence.refl eq∼))


module Strong (_∼_ : ∀ {A} → A → A → Set) (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where

  module _ {A : Set} {_∼_ : A → A → Set} (refl∼ : Reflexive _∼_) where

    open Equality _∼_ using (_≅_)
    open Equality.Rel
    open Equivalence using (refl)

    left-identity : (x : B) (f : B → A ⊥) → bind (now x) f ≅ f x
    left-identity x f = refl refl∼

    right-identity : (t : A ⊥) → bind t now ≅ t
    right-identity (now   x) = refl refl∼
    right-identity (later x) = later (♯ (right-identity (♭ x)))

    associative : (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥)
                  → bind (bind x f) g ≅ bind x (λ y → bind (f y) g)
    associative (now x)   f g = refl refl∼
    associative (later x) f g = later (♯ (associative (♭ x) f g))

  open import Structures.Monad

  _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
  _≅⊥_ {A} = Equality._≅_ {A} (_∼_ {A})

  open Equivalence using (refl; sym; trans) 
  
  eq≅⊥ : ∀ {A} → IsEquivalence (_≅⊥_ {A})
  eq≅⊥ = record 
          { refl = refl (IsEquivalence.refl eq∼) ; 
            sym = sym (IsEquivalence.sym eq∼) tt ; 
            trans = trans (IsEquivalence.trans eq∼) }


  partiality : Monad _⊥
  partiality = makeMonad 
                _≅⊥_ 
                eq≅⊥
                now 
                bind 
                (left-identity (IsEquivalence.refl eq∼)) 
                (right-identity (IsEquivalence.refl eq∼)) 
                (associative (IsEquivalence.refl eq∼))

