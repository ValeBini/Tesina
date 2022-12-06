open import Codata.Musical.Notation
open import Relation.Binary as B hiding (Rel)
open import Partiality

private
  variable
    A B C : Set

bind : A ⊥ → (A → B ⊥) → B ⊥
bind (now x)   f = f x
bind (later x) f = later (♯ (bind (♭ x) f))

module WeakMonad (_∼_ : ∀ {A} → A → A → Set) (refl∼ : ∀ {A} → Reflexive (_∼_ {A})) where

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

  open import Monad

  partiality : Monad _⊥
  partiality = makeMonad 
                _≈⊥_ 
                now 
                bind 
                (left-identity refl∼) 
                (right-identity refl∼) 
                (associative refl∼)


module StrongMonad (_∼_ : ∀ {A} → A → A → Set) (refl∼ : ∀ {A} → Reflexive (_∼_ {A})) where

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

  open import Monad

  _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
  _≅⊥_ {A} = Equality._≅_ {A} (_∼_ {A})

  partiality : Monad _⊥
  partiality = makeMonad 
                _≅⊥_ 
                now 
                bind 
                (left-identity refl∼) 
                (right-identity refl∼) 
                (associative refl∼)

