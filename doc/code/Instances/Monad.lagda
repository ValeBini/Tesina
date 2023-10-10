\begin{code}
module Instances.Monad where

open import Codata.Musical.Notation
open import Relation.Binary as B hiding (Rel)
open import Agda.Builtin.Unit
open import Delay

private
  variable
    A B C : Set
\end{code}

%<*bind>
\begin{code}
bind : A ⊥ → (A → B ⊥) → B ⊥
bind (now x)   f = f x
bind (later x) f = later (♯ (bind (♭ x) f))
\end{code}
%</bind> 

%<*module>
\begin{code} 
module Weak (_∼_ : ∀ {A} → A → A → Set) 
            (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where
\end{code}
%</module>

%<*props>
\begin{code}
  module _ {A : Set} {_∼_ : A → A → Set} (refl∼ : Reflexive _∼_) where

    open Equality _∼_ using (_≈_)
    open Equality.Rel
    open Equivalence using (refl)
\end{code}
%</props>

%<*left-identity>
\begin{code} 
    left-identity : (x : B) (f : B → A ⊥) → bind (now x) f ≈ f x
    left-identity x f = refl refl∼
\end{code}
%</left-identity> 

%<*right-identity>
\begin{code} 
    right-identity : (t : A ⊥) → bind t now ≈ t
    right-identity (now   x) = refl refl∼
    right-identity (later x) = later (♯ (right-identity (♭ x)))
\end{code}
%</right-identity> 

%<*associative>
\begin{code} 
    associative : (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥)
                  → bind (bind x f) g ≈ bind x (λ y → bind (f y) g)
    associative (now   x) f g = refl refl∼
    associative (later x) f g = later (♯ associative (♭ x) f g)
\end{code}
%</associative> 

%<*eq>
\begin{code}
  _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
  _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})
\end{code}
%</eq>

%<*equivalence>
\begin{code} 
  open Equivalence using (refl; sym; trans) 
  
  eq≈⊥ : ∀ {A} → IsEquivalence (_≈⊥_ {A})
  eq≈⊥ = record 
          { refl = refl (IsEquivalence.refl eq∼) ; 
            sym = sym (IsEquivalence.sym eq∼) tt ; 
            trans = trans (IsEquivalence.trans eq∼) }
\end{code}
%</equivalence>

%<*instance>
\begin{code} 
  open import Structures.Monad

  delayMonad : Monad _⊥
  delayMonad = makeMonad 
                _≈⊥_ 
                eq≈⊥
                now 
                bind 
                (left-identity (IsEquivalence.refl eq∼)) 
                (right-identity (IsEquivalence.refl eq∼)) 
                (associative (IsEquivalence.refl eq∼))
\end{code}
%</instance> 

%<*strong>
\begin{code} 
module Strong (_∼_ : ∀ {A} → A → A → Set) 
              (eq∼ : ∀ {A} → IsEquivalence (_∼_ {A})) where

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


  delayMonad : Monad _⊥
  delayMonad = makeMonad 
                _≅⊥_ 
                eq≅⊥
                now 
                bind 
                (left-identity (IsEquivalence.refl eq∼)) 
                (right-identity (IsEquivalence.refl eq∼)) 
                (associative (IsEquivalence.refl eq∼))
\end{code}
%</strong>