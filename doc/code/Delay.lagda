\begin{code}
module Delay where 

open import Data.Bool.Base using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod hiding (map)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Binary as B hiding (Rel)
import Relation.Binary.Properties.Setoid as SetoidProperties
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Negation
open import Codata.Musical.Notation

private
  variable
    A B C : Set
\end{code}

%<*bottom>
\begin{code}
data _⊥ (A : Set) : Set where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥
\end{code}
%</bottom>

%<*never>
\begin{code}
never : A ⊥
never = later (♯ never)
\end{code}
%</never>

%<*kind>
\begin{code}
data OtherKind : Set where
  geq weak : OtherKind

data Kind : Set where
  strong : Kind
  other  : (k : OtherKind) → Kind
\end{code}
%</kind>

%<*deckind>
\begin{code}
infix 4 _≟-Kind_

_≟-Kind_ : Decidable (_≡_ {A = Kind})
_≟-Kind_ strong        strong        = yes P.refl
_≟-Kind_ strong        (other k)     = no λ()
_≟-Kind_ (other k)     strong        = no λ()
_≟-Kind_ (other geq)   (other geq)   = yes P.refl
_≟-Kind_ (other geq)   (other weak)  = no λ()
_≟-Kind_ (other weak)  (other geq)   = no λ()
_≟-Kind_ (other weak)  (other weak)  = yes P.refl
\end{code}
%</deckind>

%<*equality>
\begin{code}
Equality : Kind → Set
Equality k = False (k ≟-Kind other geq)
\end{code}
%</equality>


