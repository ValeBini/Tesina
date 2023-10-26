\begin{code} 
module Instances.AltConcurrentMonad where

open import Instances.ConcurrentMonoid 
open import ConcMonoid-ConcMonad 
open import Structures.ConcurrentMonad
open import CoNaturalsS
open import Size
\end{code} 

%<*altconcurrent>
\begin{code}
altDelayConcurrent : ConcurrentMonad (F (Conat ∞)) 
altDelayConcurrent = cmonoid⇒cmonad conatConcurrent
\end{code}
%</altconcurrent>