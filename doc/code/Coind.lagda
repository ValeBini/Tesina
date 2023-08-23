\begin{code}
{-# OPTIONS --guardedness #-}

module Coind where
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