module Instances.AltConcurrentMonad where

open import Instances.ConcurrentMonoid 
open import Proofs.ConcMonoid->ConcMonad 
open import Structures.ConcurrentMonad
open import CoNaturalsS
open import Size

writerConatConcurrent : ConcurrentMonad (F (Conat ∞)) 
writerConatConcurrent = cmonoid⇒cmonad conatConcurrent
