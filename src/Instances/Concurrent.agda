{-# OPTIONS --guardedness #-}

module Instances.Concurrent where

open import Data.Product as Prod
open import Codata.Musical.Notation
open import Data.Bool.Base
open import Function.Base
open import Relation.Binary as B hiding (Rel)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect) renaming (refl to prefl)
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

    
    module _ {A B C D : Set} {_∼C_ : C → C → Set} {_∼D_ : D → D → Set} (reflC : Reflexive _∼C_) (reflD : Reflexive _∼D_) where

      open ProdEquality {C} {D} {_∼C_} {_∼D_} renaming (_×-≡_ to _c×d-≡_ ; refl to reflCD) using (prod≡)
      open Equality {C} _∼C_ renaming (_≅_ to _≅C_; _≳_ to _≳C_; now to nowC; later to laterC) 
      open Equality {D} _∼D_ renaming (_≅_ to _≅D_; _≳_ to _≳D_; now to nowD; later to laterD) 
      open Equality {C × D} _c×d-≡_ using (_≳_)
      open Equality.Rel

      merge-ext : (c₁ c₂ : C ⊥) (d₁ d₂ : D ⊥) → (c₁ ≅C c₂) → (d₁ ≅D d₂) → merge c₁ d₁ ≳ merge c₂ d₂ 
      merge-ext (now c₁)   (now c₂)   (now d₁)   (now d₂)   (now c₁∼c₂)   (now d₁∼d₂)   = now (prod≡ c₁∼c₂ d₁∼d₂)
      merge-ext (now c₁)   (now c₂)   (later d₁) (later d₂) pc            (later d₁∼d₂) = later (♯ (merge-ext (now c₁) (now c₂) (♭ d₁) (♭ d₂) pc (♭ d₁∼d₂)))
      merge-ext (later c₁) (later c₂) (now d₁)   (now d₂)   (later c₁∼c₂) pd            = later (♯ (merge-ext (♭ c₁) (♭ c₂) (now d₁) (now d₂) (♭ c₁∼c₂) pd))
      merge-ext (later c₁) (later c₂) (later d₁) (later d₂) (later c₁∼c₂) (later d₁∼d₂) = later (♯ (merge-ext (♭ c₁) (♭ c₂) (♭ d₁) (♭ d₂) (♭ c₁∼c₂) (♭ d₁∼d₂)))

      merge-refl : (c : C ⊥) (d : D ⊥) → merge c d ≳ merge c d 
      merge-refl (now c)   (now d)   = now (reflCD reflC reflD)
      merge-refl (now c)   (later d) = later (♯ (merge-refl (now c) (♭ d)))
      merge-refl (later c) (now d)   = later (♯ (merge-refl (♭ c) (now d)))
      merge-refl (later c) (later d) = later (♯ (merge-refl (♭ c) (♭ d)))

      ≡⇒≅C : (c₁ c₂ : C ⊥) → (c₁ ≡ c₂) → c₁ ≅C c₂
      ≡⇒≅C (now c₁)   (now .c₁)   prefl = now reflC
      ≡⇒≅C (later c₁) (later .c₁) prefl = later (♯ (≡⇒≅C (♭ c₁) (♭ c₁) prefl))

      ≡⇒≅D : (d₁ d₂ : D ⊥) → (d₁ ≡ d₂) → d₁ ≅D d₂
      ≡⇒≅D (now d₁)   (now .d₁)   prefl = now reflD
      ≡⇒≅D (later d₁) (later .d₁) prefl = later (♯ (≡⇒≅D (♭ d₁) (♭ d₁) prefl))

      lema₁ : (a : A) (b : ∞ (B ⊥)) (c : C) (f : A → C ⊥) (g : B → D ⊥) → (p : (now c) ≡ (f a))
              → (merge (now c) (bind (♭ b) g)) ≳ (bind (merge (now a) (♭ b)) (λ { (a , b) → merge (f a) (g b)}))
      lema₁ a b c f g p  with ♭ b
      ...                   | now b₁   = merge-ext (now c) (f a) (g b₁) (g b₁) (≡⇒≅C (now c) (f a) p) (≡⇒≅D (g b₁) (g b₁) prefl)
      ...                   | later b₂ = later (♯ {!   !})

      interchange : (a : A ⊥) (b : B ⊥) (f : A → C ⊥) (g : B → D ⊥)
                    → (merge (bind a f) (bind b g)) ≳ (bind (merge a b) (λ { (a , b) → merge (f a) (g b) } ))
      interchange (now a)   (now b)   f g  = merge-refl (f a) (g b) 
      interchange (now a)   (later b) f g  with f a | inspect f a
      ... | now x | Relation.Binary.PropositionalEquality.[ eq ] = {! eq  !}
      ... | later x | y = {!   !}
      -- ...                                     | later c₁ = {!   !}
      {-with f a      | ♭ b 
      ...                                     | now c    | now b₁   = later (♯ {!  !})
      ...                                     | now c    | later b₂ = later (♯ {!   !}) 
      ...                                     | later c₁ | now b₁   = {!   !} -- laterʳ⁻¹ {C × D} {_∼_} {geq} {(merge (bind (now a) (λ _ → now c)) (bind (later b) g))} {♯ (bind (merge (now a) (later b)) (λ { (a , b) → merge (f a) (g b)}))} (later (♯ (interchange (now a) {! !} (λ _ → now c) g))) --(later (♯ (interchange (now a) (♭ b) (λ _ → now c) g)))
      ...                                     | later c₁ | later b₂ = later (♯ {!   !}) -- laterʳ⁻¹ (later (♯ (interchange (now a) (♭ b) (λ _ → ♭ c₁) g)))-}
      interchange (later a) (now b)   f g  with g b 
      ...                                     | now d    = {!   !} -- laterʳ⁻¹ (later (♯ (interchange (♭ a) (now b) f (λ _ → now d))))
      ...                                     | later d₁ = {!   !} -- laterʳ⁻¹ (later (♯ (interchange (♭ a) (now b) f (λ _ → ♭ d₁))))
      interchange (later a) (later b) f g = {!   !} -- laterʳ⁻¹ (later (♯ (interchange (♭ a) (♭ b) f g)))

    _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})

    _≲⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set 
    _≲⊥_ {A} = Equality._≲_ {A} (_∼_ {A})

    open import Structures.Concurrent hiding (unit; merge)

    partiality : Concurrent _⊥
    partiality = makeConcurrent 
                    _≈⊥_
                    _≲⊥_ 
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
                    {!   !}
    
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

    _≲⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set 
    _≲⊥_ {A} = Equality._≲_ {A} (_∼_ {A})

    open import Structures.Concurrent hiding (unit; merge)

    partiality : Concurrent _⊥
    partiality = makeConcurrent 
                    _≅⊥_ 
                    _≲⊥_
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
                    {!   !}    