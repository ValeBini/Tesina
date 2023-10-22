\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

module Instances.ConcurrentMonad where

open import Data.Product as Prod
open import Codata.Musical.Notation
open import Data.Bool.Base
open import Function.Base
open import Relation.Binary as B hiding (Rel)
open import Data.Unit
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
\end{code}

%<*propeq>
\begin{code}
open import Relation.Binary.PropositionalEquality 
     renaming (refl to prefl; sym to psym; trans to ptrans)
\end{code}
%</propeq>

%<*module>
\begin{code}
module Strong where 
\end{code}
%</module> 

%<*bindprops>
\begin{code}
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
\end{code}
%</bindprops>

%<*bindcomp>
\begin{code}
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
\end{code}
%</bindcomp>

%<*fmapbind>
\begin{code}
  module _ {A B : Set} where 
    open Equality {B} _≡_ using (_≅_) 
    open Equality.Rel

    fmap∼bind : (f : A → B) → (a : A ⊥) 
              → (fmap f a) ≅ ((λ ma → bind ma (λ a → now (f a))) a )
    fmap∼bind f (now a)    = now prefl
    fmap∼bind f (later a)  = later (♯ (fmap∼bind f (♭ a))) 
\end{code}
%</fmapbind>

%<*mergeassoc>
\begin{code}
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
\end{code}
%</mergeassoc>
 
%<*mergerid>
\begin{code}
  module _ {A : Set} where

    open Equality {A × ⊤} _≡_ using (_≅_)
    open Equality.Rel

    rid : (a : A ⊥) → (merge a unit) ≅ (bind a (λ a → now (a , tt)))
    rid (now x)   = now prefl
    rid (later x) = later (♯ (rid (♭ x)))
\end{code}
%</mergerid>

%<*mergelid>
\begin{code}
  module _ {A : Set} where

    open Equality {⊤ × A} _≡_ using (_≅_)
    open Equality.Rel

    lid : (a : A ⊥) → (merge unit a) ≅ (bind a (λ a → now (tt , a)))
    lid (now x)   = now prefl
    lid (later x) = later (♯ (lid (♭ x)))
\end{code}
%</mergelid>

%<*mergecomp>
\begin{code}
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
\end{code}
%</mergecomp>

%<*mergecomm>
\begin{code}
    merge-comm : (a : A ⊥) → (b : B ⊥) 
                → merge a b ≅ bind (merge b a) (λ { (a , b) → now (b , a) })
    merge-comm (now a)   (now b)   = now prefl
    merge-comm (now a)   (later b) = later (♯ (merge-comm (now a) (♭ b)))
    merge-comm (later a) (now b)   = later (♯ (merge-comm (♭ a) (now b)))
    merge-comm (later a) (later b) = later (♯ (merge-comm (♭ a) (♭ b)))
\end{code}
%</mergecomm>

%<*rels>
\begin{code}
  _≅⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set
  _≅⊥_ {A} = Equality._≅_ {A} _≡_

  _≲⊥_ : ∀ {A} → A ⊥ → A ⊥ → Set 
  _≲⊥_ {A} = Equality._≲_ {A} _≡_
\end{code}
%</rels>

%<*eqpartial>
\begin{code}
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
\end{code}
%</eqpartial>

%<*ichangemodule>
\begin{code}
  module _ {A B C D : Set} where

    open Equality {C} _≡_ 
         renaming (_≅_ to _≅C_; _≳_ to _≳C_; now to nowC; later to laterC) 
    open Equality {D} _≡_ 
         renaming (_≅_ to _≅D_; _≳_ to _≳D_; now to nowD; later to laterD) 
    open Equality {C × D} _≡_ using (_≳_)
    open Equality.Rel renaming (laterˡ to ≲laterˡ)
    open Equivalence 
\end{code}
%</ichangemodule>

%<*mergeext>
\begin{code}
    merge-ext : (c₁ c₂ : C ⊥) (d₁ d₂ : D ⊥) → (c₁ ≅C c₂) → (d₁ ≅D d₂) 
                → merge c₁ d₁ ≳ merge c₂ d₂ 
    merge-ext (now c₁) (now .c₁) (now d₁) (now .d₁) (now prefl) (now prefl) = now prefl
    merge-ext (now c₁) (now c₂) (later d₁) (later d₂) pc (later d₁∼d₂) = 
                        later (♯ (merge-ext (now c₁) (now c₂) (♭ d₁) (♭ d₂) pc (♭ d₁∼d₂)))
    merge-ext (later c₁) (later c₂) (now d₁) (now d₂) (later c₁∼c₂) pd = 
                        later (♯ (merge-ext (♭ c₁) (♭ c₂) (now d₁) (now d₂) (♭ c₁∼c₂) pd))
    merge-ext (later c₁) (later c₂) (later d₁) (later d₂) (later c₁∼c₂) (later d₁∼d₂) = 
                        later (♯ (merge-ext (♭ c₁) (♭ c₂) (♭ d₁) (♭ d₂) (♭ c₁∼c₂) (♭ d₁∼d₂)))
\end{code}
%</mergeext>

%<*equivimplicancias>
\begin{code} 
    ≡⇒≅C : (c₁ c₂ : C ⊥) → (c₁ ≡ c₂) → c₁ ≅C c₂
    ≡⇒≅C (now c₁)   (now .c₁)   prefl = now prefl
    ≡⇒≅C (later c₁) (later .c₁) prefl = later (♯ (≡⇒≅C (♭ c₁) (♭ c₁) prefl))

    ≡⇒≅D : (d₁ d₂ : D ⊥) → (d₁ ≡ d₂) → d₁ ≅D d₂
    ≡⇒≅D (now d₁)   (now .d₁)   prefl = now prefl
    ≡⇒≅D (later d₁) (later .d₁) prefl = later (♯ (≡⇒≅D (♭ d₁) (♭ d₁) prefl))
\end{code} 
%</equivimplicancias>

%<*lemas>
\begin{code}
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
    ...                                | now b₃ = 
      laterʳ⁻¹ (merge-ext (f a) (later y) (now b₃) (now b₃) (≡⇒≅C (f a) (later y) p) (refl prefl)) 
    ...                                | later b₄ = 
      merge-comp (♭ y) (f a) (later b₄) (later b₄) (laterʳ⁻¹ 
      ((IsPartialOrder.reflexive porder≲⊥) (≡⇒≅C (later y) (f a) (psym p)))) (refl prefl)
    lema₂ a b y f g p      | later b₂ with ♭ y    | inspect ♭ y
    lema₂ a b y f g p      | later b₂  | now c₁   | [ eq ] = 
      later (♯ lema₂ a b₂ (♯ now c₁) f g (ptrans p {!   !}))
    lema₂ a b y f g p      | later b₂  | later c₂ | [ eq ] = {!   !}
\end{code}
%</lemas>

%<*interchange>
\begin{code}
    interchange : (a : A ⊥) (b : B ⊥) (f : A → C ⊥) (g : B → D ⊥)
                    → (bind (merge a b) (λ { (a , b) → merge (f a) (g b) } )) 
                                              ≳ (merge (bind a f) (bind b g))
    interchange (now a) (now b)   f g = refl prefl
    interchange (now a) (later b) f g with f a | inspect f a
    ...  | now x   | [ eq ] = later (♯ lema₁ a b x f g eq)
    ...  | later y | [ eq ] = later (♯ lema₂ a b y f g eq)
    interchange (later a) b f g = {!   !}
\end{code}
%</interchange>

%<*instance>
\begin{code}
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
\end{code}
%</instance> 

%<*problems>
\begin{code}
≡♯♭ : ∀ {S : Set} → (s : S ⊥) → (♭ (♯ s)) ≡ s 
≡♯♭ s = prefl

≡♭♯ : ∀ {S : Set} → (s : ∞ (S ⊥)) → (♯ (♭ s)) ≡ s 
≡♭♯ s = {!  prefl !}

≡⇒♯≡ : ∀ {S : Set} → (s₁ s₂ : S ⊥) → s₁ ≡ s₂ → (♯ s₁) ≡ (♯ s₂)
≡⇒♯≡ s₁ .s₁ prefl = {! prefl  !}
\end{code}
%</problems>

\begin{code}
module _ {A : Set} where

  open Equality {A} _≡_ 

  ≳now : (a : A) (a⊥ : A ⊥) → ((a⊥ ⇓) → (a⊥ ⇓ a)) → a⊥ ≳ (now a)
  ≳now a (now x) f = {!   !}
  ≳now a (later x) f = laterˡ {!   !}

  -- never≳ : (a : A ⊥) → never ≳ a 
  -- never≳ (now x) = laterˡ (never≳ ((now x)))
  -- never≳ (later x) = later (♯ (never≳ (♭ x))) 
\end{code}