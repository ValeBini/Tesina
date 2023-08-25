\begin{code}
{-# OPTIONS --guardedness #-}

module Coind where

open import Size hiding (∞)
\end{code}

%<*delayforce>
\AgdaHide{
\begin{code}
module Defs where
    infix 1000 ♯_

    postulate
        ∞  : ∀ {a} (A : Set a) → Set a
\end{code}
}
\begin{code}
        ♯_ : ∀ {a} {A : Set a} → A → ∞ A 
        ♭  : ∀ {a} {A : Set a} → ∞ A → A  
\end{code}
%</delayforce>

\begin{code}
open import Codata.Musical.Notation
\end{code}

%<*musconat>
\begin{code}
data Coℕ : Set where
    zero : Coℕ
    suc  : ∞ Coℕ → Coℕ
\end{code}
%</musconat>

%<*inf>
\begin{code}
inf : Coℕ
inf = suc (♯ inf)
\end{code}
%</inf>

%<*sizedconat>
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
%</sizedconat>

%<*sizedinf>
\begin{code}
infty : ∀ {i} → Conat′ i 
force (infty {i}) {j} = suc (infty {j})
\end{code}
%</sizedinf>