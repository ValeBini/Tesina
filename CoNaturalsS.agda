------------------------------------------------------------------------
-- Conatural numbers, taken mostly from Danielsson, updating it to
-- use the stdlib, and implement interchange and auxiliary lemmata:
-- https://www.cse.chalmers.se/~nad/publications/danielsson-definitional-interpreters-complexity/Conat.html
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module CoNaturalsS where

open import Size
open import Data.Nat as Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Function.Equivalence using (_⇔_)
open import Data.Sum

------------------------------------------------------------------------
-- The type

-- Conats.

mutual

  data Conat (i : Size) : Set where
    zero : Conat i
    suc  : Conat′ i → Conat i

  record Conat′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Conat j

open Conat′ public

------------------------------------------------------------------------
-- Some operations

-- The largest conatural number.

infinity : ∀ {i} → Conat i
infinity = suc λ { .force → infinity }

mutual

  -- Turns natural numbers into conatural numbers.

  ⌜_⌝ : ∀ {i} → ℕ → Conat i
  ⌜ zero  ⌝ = zero
  ⌜ suc n ⌝ = suc ⌜ n ⌝′

  ⌜_⌝′ : ∀ {i} → ℕ → Conat′ i
  force ⌜ n ⌝′ = ⌜ n ⌝

-- Truncated predecessor.

pred : ∀ {i} {j : Size< i} → Conat i → Conat j
pred zero    = zero
pred (suc n) = force n


------------------------------------------------------------------------
-- Bisimilarity

-- Bisimilarity is only defined for fully defined conatural numbers
-- (of size ∞).

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

-- Bisimilarity is an equivalence relation.

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


------------------------------------------------------------------------
-- Ordering

-- [ ∞ ] m ≤ n means that m is less than or equal to n.

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

-- Every conatural number is less than or equal to infinity.

infix 4 _≤infinity

_≤infinity : ∀ {i} n → [ i ] n ≤ infinity
zero  ≤infinity = zero
suc n ≤infinity = suc λ { .force → force n ≤infinity }

-- No natural number is greater than or equal to infinity.

¬_ : Set → Set
¬ X = X → ⊥

infinity≰⌜⌝ : ∀ n → ¬ ([ ∞ ] infinity ≤ ⌜ n ⌝)
infinity≰⌜⌝ zero    ()
infinity≰⌜⌝ (suc n) (suc p) = infinity≰⌜⌝ n (force p)

-- The ordering relation is a partial order (with respect to
-- bisimilarity).

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

-- Bisimilarity is contained in the ordering relation.

∼→≤ : ∀ {i m n} → [ i ] m ∼ n → [ i ] m ≤ n
∼→≤ zero    = zero
∼→≤ (suc p) = suc λ { .force → ∼→≤ (force p) }


-- The successor of a number is greater than or equal to the number.

≤suc : ∀ {i n} → [ i ] force n ≤ suc n
≤suc = helper _ refl
  where
  helper : ∀ {i} m {n} → m ≡ force n → [ i ] m ≤ suc n
  helper zero    _    = zero
  helper (suc m) 1+m≡ = suc λ { .force {j = j} →
                          subst ([ j ] _ ≤_) 1+m≡ ≤suc }

-- If a number is less than or equal to another, then it is also less
-- than or equal to the other's successor.

≤-step : ∀ {m n i} → [ i ] m ≤′ force n → [ i ] m ≤ suc n
≤-step {zero}      _ = zero
≤-step {suc m} {n} p = suc λ { .force → transitive-≤ ≤suc (force p) }


-- Addition.

infixl 6 _+_

_+_ : ∀ {i} → Conat i → Conat i → Conat i
zero  + n = n
suc m + n = suc λ { .force → force m + n }

-- Zero is a left and right identity of addition (up to bisimilarity).

+-left-identity : ∀ {i} n → [ i ] zero + n ∼ n
+-left-identity = reflexive-∼

+-right-identity : ∀ {i} n → [ i ] n + zero ∼ n
+-right-identity zero    = zero
+-right-identity (suc n) = suc λ { .force → +-right-identity (force n) }

-- Infinity is a left and right zero of addition (up to bisimilarity).

+-left-zero : ∀ {i n} → [ i ] infinity + n ∼ infinity
+-left-zero = suc λ { .force → +-left-zero }

+-right-zero : ∀ {i} n → [ i ] n + infinity ∼ infinity
+-right-zero zero    = reflexive-∼ _
+-right-zero (suc n) = suc λ { .force → +-right-zero (force n) }

-- Addition is associative.

+-assoc : ∀ m {n o i} → [ i ] m + (n + o) ∼ (m + n) + o
+-assoc zero    = reflexive-∼ _
+-assoc (suc m) = suc λ { .force → +-assoc (force m) }

mutual

  -- The successor constructor can be moved from one side of _+_ to the
  -- other.

  suc+∼+suc : ∀ {m n i} → [ i ] suc m + force n ∼ force m + suc n
  suc+∼+suc {m} {n} = transitive-∼ (suc λ { .force → reflexive-∼ _ }) (1++∼+suc _)

  1++∼+suc : ∀ m {n i} → [ i ] ⌜ 1 ⌝ + m + force n ∼ m + suc n
  1++∼+suc zero    = suc λ { .force → reflexive-∼ _ }
  1++∼+suc (suc _) = suc λ { .force → suc+∼+suc }

-- Addition is commutative.

+-comm : ∀ m {n i} → [ i ] m + n ∼ n + m
+-comm zero {n} = symmetric-∼ (+-right-identity _)
+-comm (suc m) {n} = transitive-∼ (suc λ { .force → +-comm (force m) }) (1++∼+suc _)

-- Addition preserves bisimilarity.

infixl 6 _+-cong_

_+-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] m₁ + n₁ ∼ m₂ + n₂
zero  +-cong q = q
suc p +-cong q = suc λ { .force → force p +-cong q }

-- If you add something to a number, then you get something that is
-- greater than or equal to what you started with.

m≤m+n : ∀ {m n i} → [ i ] m ≤ m + n
m≤m+n {zero}  {n} = zero
m≤m+n {suc m} {n} = suc (λ { .force → m≤m+n })

m≤n+m : ∀ {i m n} → [ i ] m ≤ n + m
m≤n+m {n = zero}  = reflexive-≤ _
m≤n+m {n = suc n} = ≤-step λ { .force → m≤n+m }

-- Addition is monotone.

infixl 6 _+-mono_

_+-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] m₁ + n₁ ≤ m₂ + n₂
_+-mono_ {m₁ = m₁} {m₂} {n₁} {n₂} zero q = transitive-≤ q m≤n+m
suc p +-mono q = suc λ { .force → force p +-mono q }


------------------------------------------------------------------------
-- Maximum

-- The largest number.

max : ∀ {i} → Conat i → Conat i → Conat i
max zero    n = n
max (suc m) n = suc λ { .force → max (force m) (pred n) }

-- The maximum of two numbers is greater than or equal to both of
-- them.

ˡ≤max : ∀ {i} m n → [ i ] m ≤ max m n
ˡ≤max zero    _ = zero
ˡ≤max (suc m) n = suc λ { .force → ˡ≤max (force m) (pred n) }

ʳ≤max : ∀ {i} m n → [ i ] n ≤ max m n
ʳ≤max zero    _       = reflexive-≤ _
ʳ≤max (suc _) zero    = zero
ʳ≤max (suc m) (suc n) = suc λ { .force → ʳ≤max (force m) (force n) }

-- Maximum is monotone.

_max-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] max m₁ n₁ ≤ max m₂ n₂
_max-mono_ {m₁ = m₁} {m₂} {n₁} {n₂} zero q = transitive-≤ q (ʳ≤max m₂ n₂)
suc p max-mono zero = suc λ { .force → (force p) max-mono zero }
suc p max-mono suc q = suc λ { .force → (force p) max-mono (force q) }

-- Zero is a left and right identity of max (up to bisimilarity).

max-left-identity : ∀ {i} n → [ i ] max zero n ∼ n
max-left-identity = reflexive-∼

max-right-identity : ∀ {i} n → [ i ] max n zero ∼ n
max-right-identity zero    = zero
max-right-identity (suc n) = suc λ { .force → max-right-identity (force n) }

-- Maximum preserves bisimilarity

infixl 6 _max-cong_

_max-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] max m₁ n₁ ∼ max m₂ n₂
zero  max-cong q = q
_max-cong_ {i} {.suc m} {.suc n} {zero} {zero}  (suc p) zero = suc λ { .force → transitive-∼ (max-right-identity (force m)) (transitive-∼ (force p) (symmetric-∼ (max-right-identity (force n)))) }
suc p max-cong suc q = suc λ { .force → (force p) max-cong (force q) }

-- The predecessor of a number is less than or equal to the number

pred≤ : ∀ {i m} → [ i ] pred m ≤ m
pred≤ {i} {zero} = zero
pred≤ {i} {suc m} = ≤suc

-- The maximum is less than or equal to the addition

max≤+ : ∀ {i m n} → [ i ] max m n ≤ m + n
max≤+ {i} {zero} {n} = reflexive-≤ (max zero n)
max≤+ {i} {suc x} {n} = suc λ { .force → transitive-≤ (max≤+ {m = force x} {n = pred n}) (reflexive-≤ (force x) +-mono pred≤) }

-- The maximum of the predecessors is equal to the predecessor of the maximum 

pred-max : ∀ {i} m n → [ i ] max (pred m) (pred n) ∼ pred (max m n)
pred-max zero n = reflexive-∼ (pred n)
pred-max (suc m) n = reflexive-∼ (max (force m) (pred n))

-- Max is associative

max-assoc : ∀ {i} n m o → [ i ] max (max n m) o ∼ max n (max m o)
max-assoc zero m o = reflexive-∼ (max m o)
max-assoc (suc n) m o = suc λ { .force → transitive-∼ (max-assoc (force n) (pred m) (pred o)) (reflexive-∼ (force n) max-cong pred-max m o) }

-- Max is commutative

max-comm : ∀ {i} n m → [ i ] max n m ∼ max m n
max-comm zero zero = zero
max-comm zero (suc m) = suc λ { .force → symmetric-∼ (max-right-identity (force m)) }
max-comm (suc n) zero = suc λ { .force → max-right-identity (force n) }
max-comm (suc n) (suc m) = suc λ { .force → max-comm (force n) (force m) }

-- Interchange law

interchange : ∀ {i} a b c d → [ i ] max (a + b) (c + d) ≤ (max a c) + (max b d)
interchange {i} zero b zero d = reflexive-≤ (max b d)
interchange {i} zero zero (suc c) d = reflexive-≤ (suc c + d)
interchange {i} zero (suc b) (suc c) zero =
            suc λ { .force → (transitive-≤ (∼→≤ (reflexive-∼ (force b) 
                                                max-cong +-right-identity (force c))) 
                             (transitive-≤ (max≤+ {_} {force b} {force c}) 
                             (transitive-≤ (∼→≤ (+-comm (force b))) 
                                           ((reflexive-≤ (force c)) +-mono 
                                           transitive-≤ (≤suc {_} {b}) 
                                            (suc λ { .force → ∼→≤ (symmetric-∼ 
                                                      (max-right-identity (force b))) 
                                                                            })) ))) }
interchange {i} zero (suc b) (suc c) (suc d) = 
            suc λ { .force → transitive-≤ (interchange zero (force b) (force c) (suc d)) 
                             ((reflexive-≤ (force c)) +-mono 
                             transitive-≤ (∼→≤ (max-comm (force b) (suc d))) 
                                 (suc λ { .force → transitive-≤ 
                                            (∼→≤ (max-comm (force d) (pred (force b)))) 
                                            (pred≤ max-mono reflexive-≤ (force d)) })) }
interchange {i} (suc a) b zero zero = 
            suc λ { .force → ∼→≤ (transitive-∼ (max-right-identity (force a + b)) 
                                               ((symmetric-∼ (max-right-identity (force a))) 
                                               +-cong 
                                               (symmetric-∼ (max-right-identity b)))) }
interchange {i} (suc a) zero zero (suc d) = 
            suc λ { .force →  transitive-≤ (∼→≤ ((+-right-identity (force a)) 
                                                 max-cong 
                                                 (reflexive-∼ (force d)))) 
                             (transitive-≤ (max≤+ {_} {force a}) 
                                           (ˡ≤max (force a) zero +-mono ≤suc)) }
interchange {i} (suc a) (suc b) zero (suc d) = 
            suc λ { .force → transitive-≤ (interchange (force a) (suc b) zero (force d)) 
                                          ((reflexive-≤ (max (force a) zero)) 
                                          +-mono 
                                          suc λ { .force → (reflexive-≤ (force b)) 
                                                           max-mono pred≤  }) }
interchange {i} (suc a) b (suc c) d = suc λ { .force → interchange (force a) b (force c) d }


-- We can give an alternative definition in which the zero is only for zero

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

zero⊑ : ∀ {i} n → [ i ] zero ⊑ n
zero⊑ zero = zero
zero⊑ (suc H) = sucr λ { .force → zero⊑ (H .force) }

-- But this is "equivalent"

⊑⇒≤ : ∀ {i} {n m} → [ i ] n ⊑ m → [ i ] n ≤ m
⊑⇒≤ zero = zero
⊑⇒≤ {n = zero} {m = suc m} (sucr H) = zero
⊑⇒≤ {n = suc n} {m = suc m} (sucr H) = suc λ { .force → transitive-≤ ≤suc (⊑⇒≤ (H .force)) }
⊑⇒≤ (suc H) = suc λ { .force {j} → ⊑⇒≤ (force H) }

≤⇒⊑ : ∀ {i} {n m} → [ i ] n ≤ m → [ i ] n ⊑ m
≤⇒⊑ {n} {.zero} zero = zero⊑ _
≤⇒⊑ {n} {.(suc _)} (suc H) = suc λ { .force → ≤⇒⊑ (H .force) }
 