\begin{code}
{-# OPTIONS --without-K --sized-types #-} 

module Instances.ConcurrentMonoid where

open import Size
open import Data.Nat as Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Structures
open import Data.Empty
open import Function.Equivalence using (_⇔_)
open import Data.Sum
open import CoNaturalsS 
\end{code}

%<*suma>
\begin{code} 
infixl 6 _+_

_+_ : ∀ {i} → Conat i → Conat i → Conat i
zero  + n = n
suc m + n = suc λ { .force → force m + n }
\end{code}
%</suma> 

%<*propsuma>
\begin{code} 
+-left-identity : ∀ {i} n → [ i ] zero + n ∼ n
+-left-identity = reflexive-∼

+-right-identity : ∀ {i} n → [ i ] n + zero ∼ n
+-right-identity zero    = zero
+-right-identity (suc n) = suc λ { .force → +-right-identity (force n) }

+-assoc : ∀ m {n o i} → [ i ] m + (n + o) ∼ (m + n) + o
+-assoc zero    = reflexive-∼ _
+-assoc (suc m) = suc λ { .force → +-assoc (force m) }
\end{code} 
%</propsuma>

%<*commsuma>
\begin{code}
mutual

  suc+∼+suc : ∀ {m n i} → [ i ] suc m + force n ∼ force m + suc n
  suc+∼+suc {m} {n} = transitive-∼ (suc λ { .force → reflexive-∼ _ }) (1++∼+suc _)

  1++∼+suc : ∀ m {n i} → [ i ] ⌜ 1 ⌝ + m + force n ∼ m + suc n
  1++∼+suc zero    = suc λ { .force → reflexive-∼ _ }
  1++∼+suc (suc _) = suc λ { .force → suc+∼+suc }

+-comm : ∀ m {n i} → [ i ] m + n ∼ n + m
+-comm zero {n} = symmetric-∼ (+-right-identity _)
+-comm (suc m) {n} = transitive-∼ (suc λ { .force → +-comm (force m) }) (1++∼+suc _)
\end{code} 
%</commsuma>

%<*congsuma>
\begin{code} 
infixl 6 _+-cong_

_+-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] m₁ + n₁ ∼ m₂ + n₂
zero  +-cong q = q
suc p +-cong q = suc λ { .force → force p +-cong q }
\end{code} 
%</congsuma>

%<*monosuma>
\begin{code} 
infixl 6 _+-mono_

m≤m+n : ∀ {m n i} → [ i ] m ≤ m + n
m≤m+n {zero}  {n} = zero
m≤m+n {suc m} {n} = suc (λ { .force → m≤m+n })

m≤n+m : ∀ {i m n} → [ i ] m ≤ n + m
m≤n+m {n = zero}  = reflexive-≤ _
m≤n+m {n = suc n} = ≤-step λ { .force → m≤n+m }

_+-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] m₁ + n₁ ≤ m₂ + n₂
_+-mono_ {m₁ = m₁} {m₂} {n₁} {n₂} zero q = transitive-≤ q m≤n+m
suc p +-mono q = suc λ { .force → force p +-mono q }
\end{code} 
%</monosuma>

%<*max>
\begin{code}
max : ∀ {i} → Conat i → Conat i → Conat i
max zero    n = n
max (suc m) n = suc λ { .force → max (force m) (pred n) }
\end{code} 
%</max>

%<*idsmax>
\begin{code} 
max-left-identity : ∀ {i} n → [ i ] max zero n ∼ n
max-left-identity = reflexive-∼

max-right-identity : ∀ {i} n → [ i ] max n zero ∼ n
max-right-identity zero    = zero
max-right-identity (suc n) = suc λ { .force → max-right-identity (force n) }
\end{code} 
%</idsmax>

%<*congmax>
\begin{code} 
infixl 6 _max-cong_

_max-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] max m₁ n₁ ∼ max m₂ n₂
zero  max-cong q = q
_max-cong_ {i} {.suc m} {.suc n} {zero} {zero}  (suc p) zero = 
                        suc λ { .force → transitive-∼ (max-right-identity (force m)) 
                                        (transitive-∼ (force p) 
                                        (symmetric-∼ (max-right-identity (force n)))) }
suc p max-cong suc q = suc λ { .force → (force p) max-cong (force q) }
\end{code} 
%</congmax>

%<*monomax>
\begin{code} 
ˡ≤max : ∀ {i} m n → [ i ] m ≤ max m n
ˡ≤max zero    _ = zero
ˡ≤max (suc m) n = suc λ { .force → ˡ≤max (force m) (pred n) }

ʳ≤max : ∀ {i} m n → [ i ] n ≤ max m n
ʳ≤max zero    _       = reflexive-≤ _
ʳ≤max (suc _) zero    = zero
ʳ≤max (suc m) (suc n) = suc λ { .force → ʳ≤max (force m) (force n) }

infixl 6 _max-mono_

_max-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] max m₁ n₁ ≤ max m₂ n₂
_max-mono_ {m₁ = m₁} {m₂} {n₁} {n₂} zero q = transitive-≤ q (ʳ≤max m₂ n₂)
suc p max-mono zero = suc λ { .force → (force p) max-mono zero }
suc p max-mono suc q = suc λ { .force → (force p) max-mono (force q) }
\end{code} 
%</monomax>

%<*assocmax>
\begin{code} 
pred-max : ∀ {i} m n → [ i ] max (pred m) (pred n) ∼ pred (max m n)
pred-max zero n = reflexive-∼ (pred n)
pred-max (suc m) n = reflexive-∼ (max (force m) (pred n))

max-assoc : ∀ {i} n m o → [ i ] max (max n m) o ∼ max n (max m o)
max-assoc zero m o = reflexive-∼ (max m o)
max-assoc (suc n) m o = suc λ { .force → transitive-∼ (max-assoc (force n) (pred m) (pred o)) 
                                        (reflexive-∼ (force n) max-cong pred-max m o) }
\end{code} 
%</assocmax>

%<*commmax>
\begin{code}
max-comm : ∀ {i} n m → [ i ] max n m ∼ max m n
max-comm zero zero = zero
max-comm zero (suc m) = suc λ { .force → symmetric-∼ (max-right-identity (force m)) }
max-comm (suc n) zero = suc λ { .force → max-right-identity (force n) }
max-comm (suc n) (suc m) = suc λ { .force → max-comm (force n) (force m) }
\end{code} 
%</commmax>

%<*interchange>
\begin{code} 
max≤+ : ∀ {i m n} → [ i ] max m n ≤ m + n
max≤+ {i} {zero} {n} = reflexive-≤ (max zero n)
max≤+ {i} {suc x} {n} = suc λ { .force → transitive-≤ (max≤+ {m = force x} {n = pred n}) 
                                        (reflexive-≤ (force x) +-mono pred≤) }

interchange : ∀ {i} a b c d → [ i ] max (a + b) (c + d) ≤ (max a c) + (max b d)
interchange {i} zero b zero d = reflexive-≤ (max (zero + b) (zero + d))
interchange {i} zero zero (suc c) d = reflexive-≤ (max (zero + zero) (suc c + d))
interchange {i} zero (suc b) (suc c) zero = 
            suc λ { .force → (transitive-≤ (∼→≤ (reflexive-∼ (force b) 
                                                max-cong +-right-identity (force c))) 
                             (transitive-≤ (max≤+ {_} {force b} {force c}) 
                             (transitive-≤ (∼→≤ (+-comm (force b))) 
                             ((reflexive-≤ (force c)) +-mono transitive-≤ (≤suc {_} {b}) 
                             (suc λ { .force → ∼→≤ (symmetric-∼ (max-right-identity (force b))) 
                                                                                      })) ))) }
interchange {i} zero (suc b) (suc c) (suc d) = 
            suc λ { .force → transitive-≤ (interchange zero (force b) (force c) (suc d)) 
                             ((reflexive-≤ (force c)) +-mono transitive-≤ 
                             (∼→≤ (max-comm (force b) (suc d))) 
                             (suc λ { .force → transitive-≤ (∼→≤ (max-comm (force d) 
                                                                  (pred (force b)))) 
                             (pred≤ max-mono reflexive-≤ (force d)) })) }
interchange {i} (suc x) b zero zero = 
            suc λ { .force → ∼→≤ (transitive-∼ (max-right-identity (force x + b)) 
                                 ((symmetric-∼ (max-right-identity (force x))) +-cong 
                                  (symmetric-∼ (max-right-identity b)))) }
interchange {i} (suc a) zero zero (suc d) = 
            suc λ { .force →  transitive-≤ (∼→≤ ((+-right-identity (force a)) max-cong 
                                                             (reflexive-∼ (force d)))) 
                              (transitive-≤ (max≤+ {_} {force a}) 
                              (ˡ≤max (force a) zero +-mono ≤suc)) }
interchange {i} (suc a) (suc b) zero (suc d) = 
            suc λ { .force → transitive-≤ (interchange (force a) (suc b) zero (force d)) 
                             ((reflexive-≤ (max (force a) zero)) +-mono 
                             suc λ { .force → (reflexive-≤ (force b)) max-mono pred≤  }) }
interchange {i} (suc a) b (suc c) d = suc λ { .force → interchange (force a) b (force c) d }
\end{code} 
%</interchange>

%<*eqpartial>
\begin{code} 
eq-∼ : IsEquivalence ([ ∞ ]_∼_)
eq-∼ = record { refl = reflexive-∼ _
             ; sym = symmetric-∼
             ; trans = transitive-∼ }

partial-≤ : IsPartialOrder ([ ∞ ]_∼_) ([ ∞ ]_≤_)
partial-≤ = record { isPreorder = 
                   record { isEquivalence = eq-∼ 
                           ; reflexive = ∼→≤
                           ; trans = transitive-≤ } 
                   ; antisym = antisymmetric-≤ }
\end{code} 
%</eqpartial>

%<*instance>
\begin{code} 
open import Structures.ConcurrentMonoid

conatConcurrent : ConcurrentMonoid (Conat ∞)
conatConcurrent = makeConcurrentMonoid
                    ([ ∞ ]_∼_)
                    eq-∼
                    ([ ∞ ]_≤_)
                    partial-≤
                    zero
                    _+_
                    (λ x y z w → _+-mono_ {∞} {x} {z} {y} {w})
                    +-left-identity
                    +-right-identity
                    (λ x y z → +-assoc x {y} {z} {∞})
                    max
                    (λ x y z w → _max-mono_ {∞} {x} {z} {y} {w})
                    max-left-identity
                    max-right-identity
                    max-assoc
                    max-comm
                    interchange
\end{code}  
%</instance>