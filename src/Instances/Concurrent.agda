{-# OPTIONS --guardedness #-}

module Instances.Concurrent where

open import Data.Product as Prod
open import Codata.Musical.Notation
open import Data.Bool.Base
open import Function.Base
open import Relation.Binary as B hiding (Rel)
open import Data.Unit
open import Relation.Binary.PropositionalEquality renaming (refl to prefl; sym to psym; trans to ptrans)
open import Delay


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

fmap : ∀ {A B : Set} → (A → B) → (A ⊥ → B ⊥)
fmap f (now x)    = now (f x)
fmap f (later x)  = later (♯ (fmap f (♭ x)))

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

      lema₁ : (a : A) (b : ∞ (B ⊥)) (c : C) (f : A → C ⊥) (g : B → D ⊥) → (p : (f a) ≡ (now c))
              → (bind (merge (now a) (♭ b)) (λ { (a , b) → merge (f a) (g b)})) ≳ (merge (now c) (bind (♭ b) g))
      lema₁ a b c f g p  with ♭ b
      ...                   | now b₁   = merge-ext (f a) (now c) (g b₁) (g b₁) ((≡⇒≅C (f a) (now c) p)) ((≡⇒≅D (g b₁) (g b₁) prefl)) 
      ...                   | later b₂ = later (♯ lema₁ a b₂ c f g p)

      interchange : (a : A ⊥) (b : B ⊥) (f : A → C ⊥) (g : B → D ⊥)
                    → (bind (merge a b) (λ { (a , b) → merge (f a) (g b) } )) ≳ (merge (bind a f) (bind b g))
      interchange (now a)   (now b)   f g  = merge-refl (f a) (g b) 
      interchange (now a)   (later b) f g  with f a | inspect f a
      ... | now c | Relation.Binary.PropositionalEquality.[ eq ] = later (♯ (lema₁ a b c f g eq))
      ... | later c | Relation.Binary.PropositionalEquality.[ eq ] = later (♯ {!   !})
      interchange (later a) (now b)   f g  with g b 
      ...                                     | now d    = {!   !} -- laterʳ⁻¹ (later (♯ (interchange (♭ a) (now b) f (λ _ → now d))))
      ...                                     | later d₁ = {!   !} -- laterʳ⁻¹ (later (♯ (interchange (♭ a) (now b) f (λ _ → ♭ d₁))))
      interchange (later a) (later b) f g = {!   !} -- laterʳ⁻¹ (later (♯ (interchange (♭ a) (♭ b) f g)))

    _≈⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≈⊥_ {A} = Equality._≈_ {A} (_∼_ {A})

    _≲⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set 
    _≲⊥_ {A} = Equality._≲_ {A} (_∼_ {A})

    open Equivalence using (refl; sym; trans)

    eq≈⊥ : ∀ {A} → IsEquivalence (_≈⊥_ {A})
    eq≈⊥ = record 
            { refl = refl (IsEquivalence.refl eq∼) ; 
              sym = sym (IsEquivalence.sym eq∼) tt ; 
              trans = trans (IsEquivalence.trans eq∼) }

    porder≲⊥ : ∀ {A} → IsPartialOrder (_≈⊥_ {A}) (_≲⊥_ {A})
    porder≲⊥ {A} = record 
                { isPreorder = record 
                               { isEquivalence = eq≈⊥ ; 
                                 reflexive = {!   !} ; 
                                 trans = {!   !} } ; 
                  antisym = {!   !} }

    open import Structures.ConcurrentMonad hiding (unit; merge)

    partiality : ConcurrentMonad _⊥
    partiality = makeConcurrentMonad 
                    _≈⊥_
                    eq≈⊥
                    _≲⊥_ 
                    {!   !}
                    now 
                    bind 
                    {!   !}
                    (left-identity (IsEquivalence.refl eq∼)) 
                    (right-identity (IsEquivalence.refl eq∼)) 
                    (bind-associative (IsEquivalence.refl eq∼))
                    merge
                    {!   !}
                    (rid (IsEquivalence.refl eq∼))
                    (lid (IsEquivalence.refl eq∼))
                    (merge-associative (IsEquivalence.refl eq∼))
                    {!   !}
                    {!   !}
    
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

      bind-associative : (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥)
                      → bind (bind x f) g ≅ bind x (λ y → bind (f y) g)
      bind-associative (now   x) f g = refl refl∼
      bind-associative (later x) f g = later (♯ bind-associative (♭ x) f g)

    module _ {A B : Set} {_∼A_ : A → A → Set} {_∼B_ : B → B → Set} (eqA : IsEquivalence _∼A_) (eqB : IsEquivalence _∼B_) where

      open Equality {A} _∼A_ renaming (_≅_ to _≅A_; _≲_ to _≲A_; now to nowA; later to laterA)
      open Equality {B} _∼B_ renaming (_≅_ to _≅B_; _≲_ to _≲B_; now to nowB; later to laterB) 
      open Equality.Rel 

      bind-compatible : (a₁ a₂ : A ⊥) (f₁ f₂ : A → B ⊥) → a₁ ≲A a₂ → (∀ (a : A) → f₁ a ≲B f₂ a) → bind a₁ f₁ ≲B bind a₂ f₂
      bind-compatible (now a₁) (now a₂) f₁ f₂ (now a₂∼a₁) f₁≲f₂ = {!   !}
      bind-compatible (now x) (later x₁) f₁ f₂ a₁≲a₂ f₁≲f₂ = {!   !}
      bind-compatible (later x) a₂ f₁ f₂ a₁≲a₂ f₁≲f₂ = {!   !} 
  
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

    module _ {A B : Set} {_∼A_ : A → A → Set} {_∼B_ : B → B → Set}
             (eqA : IsEquivalence _∼A_) (eqB : IsEquivalence _∼B_) where

      open ProdEquality {A} {B} {_∼A_} {_∼B_} renaming (_×-≡_ to _a×b-≡_ ; refl to reflAB) using (prod≡)
      open Equality {A} _∼A_ renaming (_≅_ to _≅A_; _≲_ to _≲A_; now to nowA; later to laterA)
      open Equality {B} _∼B_ renaming (_≅_ to _≅B_; _≲_ to _≲B_; now to nowB; later to laterB) 
      open Equality {A × B} _a×b-≡_ using (_≲_)
      open Equality.Rel renaming (laterˡ to rlaterˡ)

      merge-compatible : (a₁ a₂ : A ⊥) (b₁ b₂ : B ⊥) → a₁ ≲A a₂ → b₁ ≲B b₂ → merge a₁ b₁ ≲ merge a₂ b₂
      merge-compatible (now a₁) (now a₂) (now b₁) (now b₂) (now a∼) (now b∼)                  = now (prod≡ a∼ b∼)
      merge-compatible (now a₁) (now a₂) (later b₁) (later b₂) (now a∼) (later b≲)            = later (♯ merge-compatible (now a₁) (now a₂) (♭ b₁) (♭ b₂) (now a∼) (♭ b≲))
      merge-compatible (now a₁) (now a₂) (now b₁) (later b₂) (now a∼) (rlaterˡ b≲)            = rlaterˡ (merge-compatible (now a₁) (now a₂) (now b₁) (♭ b₂) (now a∼) b≲)
      merge-compatible (now a₁) (now a₂) (later b₁) (later b₂) (now a∼) (rlaterˡ b≲)          = later (♯ (merge-compatible (now a₁) (now a₂) (♭ b₁) (♭ b₂) (now a∼) (laterʳ⁻¹ b≲)))
      merge-compatible (later a₁) (later a₂) (now b₁) (now b₂) (later a≲) (now b∼)            = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (now b₁) (now b₂) (♭ a≲) (now b∼)))
      merge-compatible (later a₁) (later a₂) (later b₁) (later b₂) (later a≲) (later b≲)      = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (♭ a≲) (♭ b≲)))
      merge-compatible (later a₁) (later a₂) (now b₁) (later b₂) (later a≲) (rlaterˡ b≲)      = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (now b₁) (♭ b₂) (♭ a≲) b≲))
      merge-compatible (later a₁) (later a₂) (later b₁) (later b₂) (later a≲) (rlaterˡ b≲)    = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (♭ a≲) (laterʳ⁻¹ b≲)))
      merge-compatible (now a₁) (later a₂) (now b₁) (now b₂) (rlaterˡ a≲) (now b∼)            = rlaterˡ (merge-compatible (now a₁) (♭ a₂) (now b₁) (now b₂) a≲ (now b∼))
      merge-compatible (later a₁) (later a₂) (now b₁) (now b₂) (rlaterˡ a≲) (now b∼)          = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (now b₁) (now b₂) (laterʳ⁻¹ a≲) (now b∼)))
      merge-compatible (now a₁) (later a₂) (later b₁) (later b₂) (rlaterˡ a≲) (later b≲)      = later (♯ (merge-compatible (now a₁) (♭ a₂) (♭ b₁) (♭ b₂) a≲ (♭ b≲)))
      merge-compatible (later a₁) (later a₂) (later b₁) (later b₂) (rlaterˡ a≲) (later b≲)    = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (laterʳ⁻¹ a≲) (♭ b≲)))
      merge-compatible (now a₁) (later a₂) (now b₁) (later b₂) (rlaterˡ a≲) (rlaterˡ b≲)      = rlaterˡ (merge-compatible (now a₁) (♭ a₂) (now b₁) (♭ b₂) a≲ b≲)
      merge-compatible (now a₁) (later a₂) (later b₁) (later b₂) (rlaterˡ a≲) (rlaterˡ b≲)    = later (♯ (merge-compatible (now a₁) (♭ a₂) (♭ b₁) (♭ b₂) a≲ (laterʳ⁻¹ b≲)))
      merge-compatible (later a₁) (later a₂) (now b₁) (later b₂) (rlaterˡ a≲) (rlaterˡ b≲)    = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (now b₁) (♭ b₂) (laterʳ⁻¹ a≲) b≲))
      merge-compatible (later a₁) (later a₂) (later b₁) (later b₂) (rlaterˡ a≲) (rlaterˡ b≲)  = later (♯ (merge-compatible (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (laterʳ⁻¹ a≲) (laterʳ⁻¹ b≲)))

    _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
    _≅⊥_ {A} = Equality._≅_ {A} (_∼_ {A})

    _≲⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set 
    _≲⊥_ {A} = Equality._≲_ {A} (_∼_ {A})

    open Equivalence using (refl; sym; trans; antisym)

    eq≅⊥ : ∀ {A} → IsEquivalence (_≅⊥_ {A})
    eq≅⊥ = record 
            { refl = refl (IsEquivalence.refl eq∼) ; 
              sym = sym (IsEquivalence.sym eq∼) tt ; 
              trans = trans (IsEquivalence.trans eq∼) }

    porder≲⊥ : ∀ {A} → IsPartialOrder (_≅⊥_ {A}) (_≲⊥_ {A})
    porder≲⊥ {A} = record 
                { isPreorder = record 
                               { isEquivalence = eq≅⊥ ; 
                                 reflexive = ≅⊥⇒≲⊥ ; 
                                 trans = trans≲⊥ (trans (IsEquivalence.trans eq∼)) } ; 
                  antisym = antisym≲⊥ antisym }
      where 
        ≅⊥⇒≲⊥ : ∀ {A} → _≅⊥_ {A} ⇒ _≲⊥_ {A}
        ≅⊥⇒≲⊥ (Equality.now   nowx∼nowy) = Equality.now ((IsEquivalence.sym eq∼) nowx∼nowy)
        ≅⊥⇒≲⊥ (Equality.later x∼y) = Equality.later (♯ (≅⊥⇒≲⊥ (♭ x∼y)))
        trans≲⊥ : ∀ {A} → Transitive (Equality._≳_ {A} (_∼_ {A})) → Transitive (_≲⊥_ {A})
        trans≲⊥ trans≳ ij jk = flip trans≳ ij jk
        antisym≲⊥ : ∀ {A} → Antisymmetric _≅⊥_ (Equality._≳_ {A} (_∼_ {A})) → Antisymmetric (_≅⊥_ {A}) (_≲⊥_ {A}) 
        antisym≲⊥ antisym≳ ij ji = flip antisym≳ ij ji

    module _ {A B C D : Set} {_∼C_ : C → C → Set} {_∼D_ : D → D → Set} (reflC : Reflexive _∼C_) (reflD : Reflexive _∼D_) where

      open ProdEquality {C} {D} {_∼C_} {_∼D_} renaming (_×-≡_ to _c×d-≡_ ; refl to reflCD) using (prod≡)
      open Equality {C} _∼C_ renaming (_≅_ to _≅C_; _≳_ to _≳C_; now to nowC; later to laterC) 
      open Equality {D} _∼D_ renaming (_≅_ to _≅D_; _≳_ to _≳D_; now to nowD; later to laterD) 
      open Equality {C × D} _c×d-≡_ using (_≳_)
      open Equality.Rel
      open Equivalence 

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

      lema₁ : (a : A) (b : ∞ (B ⊥)) (c : C) (f : A → C ⊥) (g : B → D ⊥) → (p : (f a) ≡ (now c))
              → (bind (merge (now a) (♭ b)) (λ { (a , b) → merge (f a) (g b)})) ≳ (merge (now c) (bind (♭ b) g))
      lema₁ a b c f g p  with ♭ b
      ...                   | now b₁   = merge-ext (f a) (now c) (g b₁) (g b₁) ((≡⇒≅C (f a) (now c) p)) ((≡⇒≅D (g b₁) (g b₁) prefl)) 
      ...                   | later b₂ = later (♯ lema₁ a b₂ c f g p)

      interchange : (a : A ⊥) (b : B ⊥) (f : A → C ⊥) (g : B → D ⊥)
                      → (bind (merge a b) (λ { (a , b) → merge (f a) (g b) } )) ≳ (merge (bind a f) (bind b g))
      interchange (now a) (now b) f g = refl (ProdEquality.prod≡ reflC reflD)
      interchange (now a) (later b) f g with f a | inspect f a
      ... | now c | Relation.Binary.PropositionalEquality.[ eq ] = later (♯ lema₁ a b c f g eq)
      ... | later c | Relation.Binary.PropositionalEquality.[ eq ] = later (♯ {!   !})
      interchange (later a) b f g = {!   !} 

    open import Structures.ConcurrentMonad hiding (unit; merge)

    partiality : ConcurrentMonad _⊥
    partiality = makeConcurrentMonad 
                    _≅⊥_
                    eq≅⊥ 
                    _≲⊥_
                    porder≲⊥
                    now 
                    bind 
                    {!   !}
                    (left-identity (IsEquivalence.refl eq∼)) 
                    (right-identity (IsEquivalence.refl eq∼)) 
                    (bind-associative (IsEquivalence.refl eq∼))
                    merge
                    {!  merge-compatible !}
                    (rid (IsEquivalence.refl eq∼))
                    (lid (IsEquivalence.refl eq∼))
                    (merge-associative (IsEquivalence.refl eq∼))
                    {!   !}
                    {!   !}    


module StrongProp where 

  module _ {A : Set} where
      
    open Equality {A} _≡_ using (_≅_)
    open Equality.Rel 
    open Equivalence 

    left-identity : (x : B) (f : B → A ⊥) → bind (now x) f ≅ f x
    left-identity x f = refl prefl

    right-identity : (t : A ⊥) → bind t now ≅ t
    right-identity (now    x) = refl prefl
    right-identity (later  x) = later (♯ (right-identity (♭ x)))

    bind-assoc : (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥)
                    → bind (bind x f) g ≅ bind x (λ y → bind (f y) g)
    bind-assoc (now    x) f g = refl prefl
    bind-assoc (later  x) f g = later (♯ bind-assoc (♭ x) f g)


  module _ {A B : Set} where

    open Equality {A} _≡_ 
         renaming (_≅_ to _≅A_ ; _≲_ to _≲A_ ; now to nowA ; later to laterA)
    open Equality {B} _≡_ 
         renaming (_≅_ to _≅B_ ; _≲_ to _≲B_ ; now to nowB ; later to laterB) 
    open Equality.Rel renaming (laterˡ to ≲laterˡ)

    bind-comp : (a₁ a₂ : A ⊥) (f₁ f₂ : A → B ⊥) → a₁ ≲A a₂ 
                    → (∀ (a : A) → f₁ a ≲B f₂ a) → bind a₁ f₁ ≲B bind a₂ f₂
    bind-comp (now a₁) (now .a₁) f₁ f₂ (now prefl) f₁≲f₂ = f₁≲f₂ a₁
    bind-comp (now a₁) (later a₂) f₁ f₂ (≲laterˡ a₁≲a₂) f₁≲f₂ = 
                              ≲laterˡ (bind-comp (now a₁) (♭ a₂) f₁ f₂ a₁≲a₂ f₁≲f₂)
    bind-comp (later a₁) (later a₂) f₁ f₂ (later a₁≲a₂) f₁≲f₂ = 
                              later (♯ (bind-comp (♭ a₁) (♭ a₂) f₁ f₂ (♭ a₁≲a₂) f₁≲f₂))
    bind-comp (later a₁) (later a₂) f₁ f₂ (≲laterˡ a₁≲a₂) f₁≲f₂ = 
                              later (♯ (bind-comp (♭ a₁) (♭ a₂) f₁ f₂ (laterʳ⁻¹ a₁≲a₂) f₁≲f₂)) 


  module _ {A B : Set} where 
    open Equality {B} _≡_ using (_≅_) 
    open Equality.Rel

    fmap∼bind : (f : A → B) → (a : A ⊥) 
              → (fmap f a) ≅ ((λ ma → bind ma (λ a → now (f a))) a )
    fmap∼bind f (now a)    = now prefl
    fmap∼bind f (later a)  = later (♯ (fmap∼bind f (♭ a))) 


  module _ {A B C : Set} where

    open Equality {A × B × C} _≡_ using (_≅_)
    open Equality.Rel

    merge-assoc : (a : A ⊥) (b : B ⊥) (c : C ⊥)
                  → (bind (merge (merge a b) c) (λ {((a , b) , c) → now (a , (b , c))}) ) 
                                                                  ≅ (merge a (merge b c))
    merge-assoc (now a)    (now b)    (now c)    = now prefl
    merge-assoc (now a)    (now b)    (later c)  = later (♯ (merge-assoc (now a) (now b) (♭ c)))
    merge-assoc (now a)    (later b)  (now c)    = later (♯ (merge-assoc (now a) (♭ b) (now c)))
    merge-assoc (now a)    (later b)  (later c)  = later (♯ (merge-assoc (now a) (♭ b) (♭ c)))
    merge-assoc (later a)  (now b)    (now c)    = later (♯ (merge-assoc (♭ a) (now b) (now c)))
    merge-assoc (later a)  (now b)    (later c)  = later (♯ (merge-assoc (♭ a) (now b) (♭ c)))
    merge-assoc (later a)  (later b)  (now c)    = later (♯ (merge-assoc (♭ a) (♭ b) (now c)))
    merge-assoc (later a)  (later b)  (later c)  = later (♯ (merge-assoc (♭ a) (♭ b) (♭ c)))


  module _ {A : Set} where

    open Equality {A × ⊤} _≡_ using (_≅_)
    open Equality.Rel

    rid : (a : A ⊥) → (merge a unit) ≅ (bind a (λ a → now (a , tt)))
    rid (now x)   = now prefl
    rid (later x) = later (♯ (rid (♭ x)))


  module _ {A : Set} where

    open Equality {⊤ × A} _≡_ using (_≅_)
    open Equality.Rel

    lid : (a : A ⊥) → (merge unit a) ≅ (bind a (λ a → now (tt , a)))
    lid (now x)   = now prefl
    lid (later x) = later (♯ (lid (♭ x)))


  module _ {A B : Set} where

    open Equality {A} _≡_ 
         renaming (_≅_ to _≅A_; _≲_ to _≲A_; now to nowA; later to laterA)
    open Equality {B} _≡_ 
         renaming (_≅_ to _≅B_; _≲_ to _≲B_; now to nowB; later to laterB) 
    open Equality {A × B} _≡_ using (_≲_ ; _≅_)
    open Equality.Rel renaming (laterˡ to ≲laterˡ)

    merge-comp : (a₁ a₂ : A ⊥) (b₁ b₂ : B ⊥) → a₁ ≲A a₂ → b₁ ≲B b₂ 
                        → merge a₁ b₁ ≲ merge a₂ b₂
    merge-comp (now a₁) (now .a₁) (now b₁) (now .b₁) (now prefl) (now prefl) = now prefl
    merge-comp (now a₁) (now a₂) (later b₁) (later b₂) (now a∼) (later b≲) = 
               later (♯ merge-comp (now a₁) (now a₂) (♭ b₁) (♭ b₂) (now a∼) (♭ b≲))
    merge-comp (now a₁) (now a₂) (now b₁) (later b₂) (now a∼) (≲laterˡ b≲) = 
               ≲laterˡ (merge-comp (now a₁) (now a₂) (now b₁) (♭ b₂) (now a∼) b≲)
    merge-comp (now a₁) (now a₂) (later b₁) (later b₂) (now a∼) (≲laterˡ b≲) = 
               later (♯ (merge-comp (now a₁) (now a₂) (♭ b₁) (♭ b₂) (now a∼) (laterʳ⁻¹ b≲)))
    merge-comp (later a₁) (later a₂) (now b₁) (now b₂) (later a≲) (now b∼) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (now b₁) (now b₂) (♭ a≲) (now b∼)))
    merge-comp (later a₁) (later a₂) (later b₁) (later b₂) (later a≲) (later b≲) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (♭ a≲) (♭ b≲)))
    merge-comp (later a₁) (later a₂) (now b₁) (later b₂) (later a≲) (≲laterˡ b≲) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (now b₁) (♭ b₂) (♭ a≲) b≲))
    merge-comp (later a₁) (later a₂) (later b₁) (later b₂) (later a≲) (≲laterˡ b≲) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (♭ a≲) (laterʳ⁻¹ b≲)))
    merge-comp (now a₁) (later a₂) (now b₁) (now b₂) (≲laterˡ a≲) (now b∼) = 
               ≲laterˡ (merge-comp (now a₁) (♭ a₂) (now b₁) (now b₂) a≲ (now b∼))
    merge-comp (later a₁) (later a₂) (now b₁) (now b₂) (≲laterˡ a≲) (now b∼) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (now b₁) (now b₂) (laterʳ⁻¹ a≲) (now b∼)))
    merge-comp (now a₁) (later a₂) (later b₁) (later b₂) (≲laterˡ a≲) (later b≲) = 
               later (♯ (merge-comp (now a₁) (♭ a₂) (♭ b₁) (♭ b₂) a≲ (♭ b≲)))
    merge-comp (later a₁) (later a₂) (later b₁) (later b₂) (≲laterˡ a≲) (later b≲) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (laterʳ⁻¹ a≲) (♭ b≲)))
    merge-comp (now a₁) (later a₂) (now b₁) (later b₂) (≲laterˡ a≲) (≲laterˡ b≲) = 
               ≲laterˡ (merge-comp (now a₁) (♭ a₂) (now b₁) (♭ b₂) a≲ b≲)
    merge-comp (now a₁) (later a₂) (later b₁) (later b₂) (≲laterˡ a≲) (≲laterˡ b≲) = 
               later (♯ (merge-comp (now a₁) (♭ a₂) (♭ b₁) (♭ b₂) a≲ (laterʳ⁻¹ b≲)))
    merge-comp (later a₁) (later a₂) (now b₁) (later b₂) (≲laterˡ a≲) (≲laterˡ b≲) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (now b₁) (♭ b₂) (laterʳ⁻¹ a≲) b≲))
    merge-comp (later a₁) (later a₂) (later b₁) (later b₂) (≲laterˡ a≲) (≲laterˡ b≲) = 
               later (♯ (merge-comp (♭ a₁) (♭ a₂) (♭ b₁) (♭ b₂) (laterʳ⁻¹ a≲) (laterʳ⁻¹ b≲)))


    merge-comm : (a : A ⊥) → (b : B ⊥) 
                → merge a b ≅ bind (merge b a) (λ { (a , b) → now (b , a) })
    merge-comm (now a)   (now b)   = now prefl
    merge-comm (now a)   (later b) = later (♯ (merge-comm (now a) (♭ b)))
    merge-comm (later a) (now b)   = later (♯ (merge-comm (♭ a) (now b)))
    merge-comm (later a) (later b) = later (♯ (merge-comm (♭ a) (♭ b)))


  _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
  _≅⊥_ {A} = Equality._≅_ {A} _≡_

  _≲⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set 
  _≲⊥_ {A} = Equality._≲_ {A} _≡_


  open Equivalence using (refl; sym; trans; antisym)

  eq≅⊥ : ∀ {A} → IsEquivalence (_≅⊥_ {A})
  eq≅⊥ = record 
          { refl = refl prefl ; 
            sym = sym psym tt ; 
            trans = trans ptrans }

  porder≲⊥ : ∀ {A} → IsPartialOrder (_≅⊥_ {A}) (_≲⊥_ {A})
  porder≲⊥ {A} = record 
              { isPreorder = record 
                              { isEquivalence = eq≅⊥ ; 
                                reflexive = ≅⊥⇒≲⊥ ; 
                                trans = trans≲⊥ (trans ptrans) } ; 
                antisym = antisym≲⊥ antisym }
    where 
      ≅⊥⇒≲⊥ : ∀ {A} → _≅⊥_ {A} ⇒ _≲⊥_ {A}
      ≅⊥⇒≲⊥ (Equality.now   nowx∼nowy) = Equality.now (psym nowx∼nowy)
      ≅⊥⇒≲⊥ (Equality.later x∼y) = Equality.later (♯ (≅⊥⇒≲⊥ (♭ x∼y)))
      trans≲⊥ : ∀ {A} → Transitive (Equality._≳_ {A} _≡_) → Transitive (_≲⊥_ {A})
      trans≲⊥ trans≳ ij jk = flip trans≳ ij jk
      antisym≲⊥ : ∀ {A} → Antisymmetric _≅⊥_ (Equality._≳_ {A} _≡_) 
                → Antisymmetric (_≅⊥_ {A}) (_≲⊥_ {A}) 
      antisym≲⊥ antisym≳ ij ji = flip antisym≳ ij ji


  module _ {A B C D : Set} where

    open Equality {C} _≡_ 
         renaming (_≅_ to _≅C_; _≳_ to _≳C_; now to nowC; later to laterC) 
    open Equality {D} _≡_ 
         renaming (_≅_ to _≅D_; _≳_ to _≳D_; now to nowD; later to laterD) 
    open Equality {C × D} _≡_ using (_≳_)
    open Equality.Rel renaming (laterˡ to ≲laterˡ)
    open Equivalence 

    merge-ext : (c₁ c₂ : C ⊥) (d₁ d₂ : D ⊥) → (c₁ ≅C c₂) → (d₁ ≅D d₂) 
                → merge c₁ d₁ ≳ merge c₂ d₂ 
    merge-ext (now c₁) (now .c₁) (now d₁) (now .d₁) (now prefl) (now prefl) = now prefl
    merge-ext (now c₁) (now c₂) (later d₁) (later d₂) pc (later d₁∼d₂) = 
                        later (♯ (merge-ext (now c₁) (now c₂) (♭ d₁) (♭ d₂) pc (♭ d₁∼d₂)))
    merge-ext (later c₁) (later c₂) (now d₁) (now d₂) (later c₁∼c₂) pd = 
                        later (♯ (merge-ext (♭ c₁) (♭ c₂) (now d₁) (now d₂) (♭ c₁∼c₂) pd))
    merge-ext (later c₁) (later c₂) (later d₁) (later d₂) (later c₁∼c₂) (later d₁∼d₂) = 
                        later (♯ (merge-ext (♭ c₁) (♭ c₂) (♭ d₁) (♭ d₂) (♭ c₁∼c₂) (♭ d₁∼d₂)))

    ≡⇒≅C : (c₁ c₂ : C ⊥) → (c₁ ≡ c₂) → c₁ ≅C c₂
    ≡⇒≅C (now c₁)   (now .c₁)   prefl = now prefl
    ≡⇒≅C (later c₁) (later .c₁) prefl = later (♯ (≡⇒≅C (♭ c₁) (♭ c₁) prefl))

    ≡⇒≅D : (d₁ d₂ : D ⊥) → (d₁ ≡ d₂) → d₁ ≅D d₂
    ≡⇒≅D (now d₁)   (now .d₁)   prefl = now prefl
    ≡⇒≅D (later d₁) (later .d₁) prefl = later (♯ (≡⇒≅D (♭ d₁) (♭ d₁) prefl))

    lema₁ : (a : A) (b : ∞ (B ⊥)) (c : C) (f : A → C ⊥) (g : B → D ⊥) → (p : (f a) ≡ (now c))
            → (bind (merge (now a) (♭ b)) (λ { (a , b) → merge (f a) (g b)})) 
                                                             ≳ (merge (now c) (bind (♭ b) g))
    lema₁ a b c f g p  with ♭ b
    ...                   | now b₁   = 
                          merge-ext (f a) (now c) (g b₁) (g b₁) 
                                    ((≡⇒≅C (f a) (now c) p)) ((≡⇒≅D (g b₁) (g b₁) prefl)) 
    ...                   | later b₂ = later (♯ lema₁ a b₂ c f g p)

    lema₂ : (a : A) (b : ∞ (B ⊥)) (y : ∞ (C ⊥)) (f : A → C ⊥) (g : B → D ⊥) 
            → (p : (f a) ≡ (later y)) 
            → (bind (merge (now a) (♭ b)) (λ { (a , b) → merge (f a) (g b) })) 
                                                ≳ (merge (♭ y) (bind (♭ b) g))
    lema₂ a b y f g p with ♭ b 
    ...                    | now b₁ with g b₁ 
    ...                                | now b₃ = laterʳ⁻¹ (merge-ext (f a) (later y) (now b₃) (now b₃) (≡⇒≅C (f a) (later y) p) (refl prefl)) 
    ...                                | later b₄ = merge-comp (♭ y) (f a) (later b₄) (later b₄) (laterʳ⁻¹ ((IsPartialOrder.reflexive porder≲⊥) (≡⇒≅C (later y) (f a) (psym p)))) (refl prefl)
    lema₂ a b y f g p      | later b₂ with ♭ y    | inspect ♭ y
    lema₂ a b y f g p      | later b₂    | now c₁   | [ eq ] = later (♯ lema₂ a b₂ (♯ now c₁) f g (ptrans p {!   !}))
    lema₂ a b y f g p      | later b₂    | later c₂ | [ eq ] = {!   !}

    interchange : (a : A ⊥) (b : B ⊥) (f : A → C ⊥) (g : B → D ⊥)
                    → (bind (merge a b) (λ { (a , b) → merge (f a) (g b) } )) 
                                              ≳ (merge (bind a f) (bind b g))
    interchange (now a) (now b)   f g = refl prefl
    interchange (now a) (later b) f g with f a | inspect f a
    ...  | now x   | [ eq ] = later (♯ lema₁ a b x f g eq)
    ...  | later y | [ eq ] = later (♯ lema₂ a b y f g eq)
    interchange (later a) b f g = {!   !}

  open import Structures.ConcurrentMonad hiding (unit; merge)

  delayConcurrent : ConcurrentMonad _⊥
  delayConcurrent = makeConcurrentMonad 
                      _≅⊥_
                      eq≅⊥ 
                      _≲⊥_
                      porder≲⊥
                      now 
                      bind 
                      bind-comp
                      left-identity 
                      right-identity
                      bind-assoc
                      merge
                      merge-comp
                      rid
                      lid
                      merge-assoc
                      merge-comm
                      {!   !}    

-- Equality problems
≡♯♭ : ∀ {S : Set} → (s : S ⊥) → (♭ (♯ s)) ≡ s 
≡♯♭ s = prefl

≡♭♯ : ∀ {S : Set} → (s : ∞ (S ⊥)) → (♯ (♭ s)) ≡ s 
≡♭♯ s = {!  prefl !}

≡⇒♯≡ : ∀ {S : Set} → (s₁ s₂ : S ⊥) → s₁ ≡ s₂ → (♯ s₁) ≡ (♯ s₂)
≡⇒♯≡ s₁ .s₁ prefl = {! prefl  !}