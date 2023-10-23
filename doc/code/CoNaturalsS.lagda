\begin{code}
{-# OPTIONS --without-K --sized-types #-}

module CoNaturalsS where

open import Size
open import Data.Nat as Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Structures
open import Data.Empty
open import Function.Equivalence using (_⇔_)
open import Data.Sum
\end{code}

%<*conat>
\begin{code} 
mutual

  data Conat (i : Size) : Set where
    zero : Conat i
    suc  : Conat′ i → Conat i

  record Conat′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Conat j

open Conat′ public
\end{code} 
%</conat>

%<*pred>
\begin{code} 
pred : ∀ {i} {j : Size< i} → Conat i → Conat j
pred zero    = zero
pred (suc n) = force n
\end{code} 
%</pred>

%<*natconat>
\begin{code} 
mutual

  ⌜_⌝ : ∀ {i} → ℕ → Conat i
  ⌜ zero  ⌝ = zero
  ⌜ suc n ⌝ = suc ⌜ n ⌝′

  ⌜_⌝′ : ∀ {i} → ℕ → Conat′ i
  force ⌜ n ⌝′ = ⌜ n ⌝
\end{code} 
%</natconat>

%<*igualdad>
\begin{code} 
mutual

  infix 4 [_]_∼_ [_]_∼′_

  data [_]_∼_ (i : Size) : Conat ∞ → Conat ∞ → Set where
    zero : [ i ] zero ∼ zero
    suc  : ∀ {m n} → [ i ] force m ∼′ force n → [ i ] suc m ∼ suc n

  record [_]_∼′_ (i : Size) (m n : Conat ∞) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] m ∼ n

open [_]_∼′_ public
\end{code} 
%</igualdad> 

%<*propseq>
\begin{code} 
reflexive-∼ : ∀ {i} n → [ i ] n ∼ n
reflexive-∼ zero    = zero
reflexive-∼ (suc n) = suc λ { .force → reflexive-∼ (force n) }

symmetric-∼ : ∀ {i m n} → [ i ] m ∼ n → [ i ] n ∼ m
symmetric-∼ zero    = zero
symmetric-∼ (suc p) = suc λ { .force → symmetric-∼ (force p) }

transitive-∼ : ∀ {i m n o} → [ i ] m ∼ n → [ i ] n ∼ o → [ i ] m ∼ o
transitive-∼ zero    zero    = zero
transitive-∼ (suc p) (suc q) =
  suc λ { .force → transitive-∼ (force p) (force q) }
\end{code} 
%</propseq>

%<*orden>
\begin{code} 
mutual 
  
  infix 4 [_]_≤_ [_]_≤′_

  data [_]_≤_ (i : Size) : Conat ∞ → Conat ∞ → Set where
    zero : ∀ {n} → [ i ] zero ≤ n
    suc  : ∀ {m n} → [ i ] force m ≤′ force n → [ i ] suc m ≤ suc n

  record [_]_≤′_ (i : Size) (m n : Conat ∞) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] m ≤ n

open [_]_≤′_ public
\end{code} 
%</orden>

%<*propsorden>
\begin{code} 
reflexive-≤ : ∀ {i} n → [ i ] n ≤ n
reflexive-≤ zero    = zero
reflexive-≤ (suc n) = suc λ { .force → reflexive-≤ (force n) }

transitive-≤ : ∀ {i m n o} → [ i ] m ≤ n → [ i ] n ≤ o → [ i ] m ≤ o
transitive-≤ zero    _       = zero
transitive-≤ (suc p) (suc q) =
  suc λ { .force → transitive-≤ (force p) (force q) }

antisymmetric-≤ : ∀ {i m n} → [ i ] m ≤ n → [ i ] n ≤ m → [ i ] m ∼ n
antisymmetric-≤ zero    zero    = zero
antisymmetric-≤ (suc p) (suc q) =
  suc λ { .force → antisymmetric-≤ (force p) (force q) }
\end{code} 
%</propsorden>

%<*reflorden>
\begin{code} 
∼→≤ : ∀ {i m n} → [ i ] m ∼ n → [ i ] m ≤ n
∼→≤ zero    = zero
∼→≤ (suc p) = suc λ { .force → ∼→≤ (force p) }
\end{code} 
%</reflorden>

%<*menorsuc>
\begin{code}
≤suc : ∀ {i n} → [ i ] force n ≤ suc n
≤suc = helper _ refl
  where
  helper : ∀ {i} m {n} → m ≡ force n → [ i ] m ≤ suc n
  helper zero    _    = zero
  helper (suc m) 1+m≡ = suc λ { .force {j = j} →
                          subst ([ j ] _ ≤_) 1+m≡ ≤suc }
\end{code} 
%</menorsuc>

%<*pasosuc>
\begin{code} 
≤-step : ∀ {m n i} → [ i ] m ≤′ force n → [ i ] m ≤ suc n
≤-step {zero}      _ = zero
≤-step {suc m} {n} p = suc λ { .force → transitive-≤ ≤suc (force p) }
\end{code}
%</pasosuc>

%<*predmenor>
\begin{code}
pred≤ : ∀ {i m} → [ i ] pred m ≤ m
pred≤ {i} {zero} = zero
pred≤ {i} {suc m} = ≤suc
\end{code} 
%</predmenor>

%<*ordenalt>
\begin{code} 
mutual

  infix 4 [_]_⊑_ [_]_⊑′_

  data [_]_⊑_ (i : Size) : Conat ∞ → Conat ∞ → Set where
    zero : [ i ] zero ⊑ zero
    sucr : ∀ {m n} → [ i ] m ⊑′ force n → [ i ] m ⊑ suc n
    suc  : ∀ {m n} → [ i ] force m ⊑′ force n → [ i ] suc m ⊑ suc n

  record [_]_⊑′_ (i : Size) (m n : Conat ∞) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] m ⊑ n

open [_]_⊑′_ public
\end{code} 
%</ordenalt>

%<*zeromenor>
\begin{code} 
zero⊑ : ∀ {i} n → [ i ] zero ⊑ n
zero⊑ zero = zero
zero⊑ (suc H) = sucr λ { .force → zero⊑ (H .force) }
\end{code} 
%</zeromenor> 

%<*ordeneseq>
\begin{code}
⊑⇒≤ : ∀ {i} {n m} → [ i ] n ⊑ m → [ i ] n ≤ m
⊑⇒≤ zero = zero
⊑⇒≤ {n = zero} {m = suc m} (sucr H) = zero
⊑⇒≤ {n = suc n} {m = suc m} (sucr H) = suc λ { .force → transitive-≤ ≤suc (⊑⇒≤ (H .force)) }
⊑⇒≤ (suc H) = suc λ { .force {j} → ⊑⇒≤ (force H) }

≤⇒⊑ : ∀ {i} {n m} → [ i ] n ≤ m → [ i ] n ⊑ m
≤⇒⊑ {n} {.zero} zero = zero⊑ _
≤⇒⊑ {n} {.(suc _)} (suc H) = suc λ { .force → ≤⇒⊑ (H .force) }
\end{code} 
%</ordeneseq>