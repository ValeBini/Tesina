\begin{code}
--{-# OPTIONS --guardedness #-}

module Instances.Monoidal where

open import Data.Product as Prod
open import Codata.Musical.Notation
open import Data.Bool.Base
open import Relation.Binary as B hiding (Rel)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to prefl)

open import Delay

private
    variable
        A B C : Set
\end{code}

%<*merge>
\begin{code}
merge : A ⊥ → B ⊥ → (A × B) ⊥
merge (now a)   (now b)    = now (a , b)
merge (now a)   (later b)  = later (♯ (merge (now a) (♭ b)))
merge (later a) (now b)    = later (♯ (merge (♭ a) (now b)))
merge (later a) (later b)  = later (♯ (merge (♭ a) (♭ b)))
\end{code}
%</merge>

%<*fmap>
\begin{code}
fmap : ∀ {A B : Set} → (A → B) → (A ⊥ → B ⊥)
fmap f (now x)    = now (f x)
fmap f (later x)  = later (♯ (fmap f (♭ x)))
\end{code}
%</fmap> 

%<*unit>
\begin{code}
unit : ⊤ ⊥
unit = now tt
\end{code}
%</unit>

%<*module>
\begin{code}
module Weak (_∼_ : ∀ {A} → A → A → Set) 
            (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where
\end{code}
%</module>

%<*associative>
\begin{code}
    module _ {A B C : Set} {_∼_ : A × B × C → A × B × C → Set} 
             (reflABC : Reflexive _∼_) where

      open Equality {A × B × C} _∼_ using (_≈_)
      open Equality.Rel

      associative : (a : A ⊥) (b : B ⊥) (c : C ⊥)
                    → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) 
                                                               ≈ (merge a (merge b c))
      associative (now a)    (now b)    (now c)    = now reflABC
      associative (now a)    (now b)    (later c)  = later (♯ (associative (now a) (now b) (♭ c)))
      associative (now a)    (later b)  (now c)    = later (♯ (associative (now a) (♭ b) (now c)))
      associative (now a)    (later b)  (later c)  = later (♯ (associative (now a) (♭ b) (♭ c)))
      associative (later a)  (now b)    (now c)    = later (♯ (associative (♭ a) (now b) (now c)))
      associative (later a)  (now b)    (later c)  = later (♯ (associative (♭ a) (now b) (♭ c)))
      associative (later a)  (later b)  (now c)    = later (♯ (associative (♭ a) (♭ b) (now c)))
      associative (later a)  (later b)  (later c)  = later (♯ (associative (♭ a) (♭ b) (♭ c)))
\end{code}
%</associative>

%<*rid>
\begin{code}
    module _ {A : Set} {_∼_ : (A × ⊤) → (A × ⊤) → Set} 
             (reflA×⊤ : Reflexive _∼_) where

      open Equality {A × ⊤} _∼_ using (_≈_)
      open Equality.Rel

      rid : (a : A ⊥) → (merge a unit) ≈ (fmap (λ a → (a , tt)) a)
      rid (now x)    = now reflA×⊤
      rid (later x)  = later (♯ (rid (♭ x)))
\end{code}
%</rid>

%<*lid>
\begin{code}
    module _ {A : Set} {_∼_ : (⊤ × A) → (⊤ × A) → Set} 
             (refl⊤×A : Reflexive _∼_) where

      open Equality {⊤ × A} _∼_ using (_≈_)
      open Equality.Rel

      lid : (a : A ⊥) → (merge unit a) ≈ (fmap (λ a → (tt , a)) a)
      lid (now x)    = now refl⊤×A
      lid (later x)  = later (♯ (lid (♭ x)))
\end{code}
%</lid> 

%<*eq>
\begin{code}
    _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})

    open Equivalence using (refl; sym; trans) 
  
    eq≈⊥ : ∀ {A} → IsEquivalence (_≈⊥_ {A})
    eq≈⊥ = record 
            { refl = refl (IsEquivalence.refl eq∼) ; 
              sym = sym (IsEquivalence.sym eq∼) tt ; 
              trans = trans (IsEquivalence.trans eq∼) }
\end{code}
%</eq>

%<*instance>
\begin{code}
    open import Structures.MonoidalFunctor hiding (unit; merge; fmap)

    delayMonoidal : MonoidalFunctor _⊥
    delayMonoidal = makeMonoidalFunctor 
                          _≈⊥_ 
                          eq≈⊥
                          unit 
                          merge 
                          fmap 
                          (rid (IsEquivalence.refl eq∼))
                          (lid (IsEquivalence.refl eq∼)) 
                          (associative (IsEquivalence.refl eq∼))
\end{code}
%</instance>

%<*strong>
\begin{code}
module Strong (_∼_ : ∀ {A} → A → A → Set) 
              (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where

  module _ {A B C : Set} {_∼_ : A × B × C → A × B × C → Set} 
            (reflABC : Reflexive _∼_) where

    open Equality {A × B × C} _∼_ using (_≅_)
    open Equality.Rel

    associative : (a : A ⊥) (b : B ⊥) (c : C ⊥)
                  → (fmap (λ {((a , b) , c) → (a , (b , c))}) (merge (merge a b) c)) 
                                                              ≅ (merge a (merge b c))
    associative (now a)   (now b)   (now c)   = now reflABC
    associative (now a)   (now b)   (later c) = later (♯ (associative (now a) (now b) (♭ c)))
    associative (now a)   (later b) (now c)   = later (♯ (associative (now a) (♭ b) (now c)))
    associative (now a)   (later b) (later c) = later (♯ (associative (now a) (♭ b) (♭ c)))
    associative (later a) (now b)   (now c)   = later (♯ (associative (♭ a) (now b) (now c)))
    associative (later a) (now b)   (later c) = later (♯ (associative (♭ a) (now b) (♭ c)))
    associative (later a) (later b) (now c)   = later (♯ (associative (♭ a) (♭ b) (now c)))
    associative (later a) (later b) (later c) = later (♯ (associative (♭ a) (♭ b) (♭ c)))


  module _ {A : Set} {_∼_ : (A × ⊤) → (A × ⊤) → Set} 
            (reflA×⊤ : Reflexive _∼_) where

    open Equality {A × ⊤} _∼_ using (_≅_)
    open Equality.Rel

    rid : (a : A ⊥) → (merge a unit) ≅ (fmap (λ a → (a , tt)) a)
    rid (now x)   = now reflA×⊤
    rid (later x) = later (♯ (rid (♭ x)))

  module _ {A : Set} {_∼_ : (⊤ × A) → (⊤ × A) → Set} 
            (refl⊤×A : Reflexive _∼_) where

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

  delayMonoidal : MonoidalFunctor _⊥
  delayMonoidal = makeMonoidalFunctor 
                        _≅⊥_ 
                        eq≅⊥
                        unit 
                        merge 
                        fmap 
                        (rid (IsEquivalence.refl eq∼))
                        (lid (IsEquivalence.refl eq∼)) 
                        (associative (IsEquivalence.refl eq∼))
\end{code}
%</strong>
