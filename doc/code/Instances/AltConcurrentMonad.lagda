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
writerConatConcurrent : ConcurrentMonad (F (Conat ∞)) 
writerConatConcurrent = cmonoid⇒cmonad conatConcurrent
\end{code}
%</altconcurrent>