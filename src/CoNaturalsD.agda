------------------------------------------------------------------------
-- Conatural numbers, taken mostly from Danielsson, updating it to
-- use the stdlib, and implement interchange and auxiliary lemmata:
-- https://www.cse.chalmers.se/~nad/publications/danielsson-definitional-interpreters-complexity/Conat.html
-- Then, we can construct a concurrent monad by product
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module CoNaturalsD where

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

-- Equational reasoning combinators.

infix  -1 finally-∼ _∎∼
infixr -2 step-∼ _≡⟨⟩∼_

_∎∼ : ∀ {i} n → [ i ] n ∼ n
_∎∼ = reflexive-∼

-- For an explanation of why step-∼ is defined in this way, see
-- Equality.step-≡.

step-∼ : ∀ {i} m {n o} → [ i ] n ∼ o → [ i ] m ∼ n → [ i ] m ∼ o
step-∼ _ n∼o m∼n = transitive-∼ m∼n n∼o

syntax step-∼ m n∼o m∼n = m ∼⟨ m∼n ⟩ n∼o

_≡⟨⟩∼_ : ∀ {i} m {n} → [ i ] m ∼ n → [ i ] m ∼ n
_ ≡⟨⟩∼ m∼n = m∼n

finally-∼ : ∀ {i} m n → [ i ] m ∼ n → [ i ] m ∼ n
finally-∼ _ _ m∼n = m∼n

syntax finally-∼ m n m∼n = m ∼⟨ m∼n ⟩∎ n ∎∼

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

-- ⌜_⌝ maps equal numbers to bisimilar numbers.

⌜⌝-cong : ∀ {i m n} → m ≡ n → [ i ] ⌜ m ⌝ ∼ ⌜ n ⌝
⌜⌝-cong refl = reflexive-∼ _

-- Truncated predecessor.

pred : ∀ {i} {j : Size< i} → Conat i → Conat j
pred zero    = zero
pred (suc n) = force n

-- ⌜_⌝ is homomorphic with respect to pred.

⌜⌝-pred : ∀ n {i} → [ i ] ⌜ Nat.pred n ⌝ ∼ pred ⌜ n ⌝
⌜⌝-pred zero    = zero   ∎∼
⌜⌝-pred (suc n) = ⌜ n ⌝  ∎∼

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
  suc+∼+suc {m} {n} =
    suc m + force n            ∼⟨ (suc λ { .force → reflexive-∼ _ }) ⟩
    ⌜ 1 ⌝ + force m + force n  ∼⟨ 1++∼+suc _ ⟩∎
    force m + suc n            ∎∼

  1++∼+suc : ∀ m {n i} → [ i ] ⌜ 1 ⌝ + m + force n ∼ m + suc n
  1++∼+suc zero    = suc λ { .force → reflexive-∼ _ }
  1++∼+suc (suc _) = suc λ { .force → suc+∼+suc }

-- Addition is commutative.

+-comm : ∀ m {n i} → [ i ] m + n ∼ n + m
+-comm zero {n} =
  zero + n  ∼⟨ symmetric-∼ (+-right-identity _) ⟩∎
  n + zero  ∎∼
+-comm (suc m) {n} =
  suc m + n            ∼⟨ (suc λ { .force → +-comm (force m) }) ⟩
  ⌜ 1 ⌝ + n + force m  ∼⟨ 1++∼+suc _ ⟩∎
  n + suc m            ∎∼

-- Addition preserves bisimilarity.

infixl 6 _+-cong_

_+-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] m₁ + n₁ ∼ m₂ + n₂
zero  +-cong q = q
suc p +-cong q = suc λ { .force → force p +-cong q }

-- ⌜_⌝ is homomorphic with respect to addition.

⌜⌝-+ : ∀ m {n i} → [ i ] ⌜ m Nat.+ n ⌝ ∼ ⌜ m ⌝ + ⌜ n ⌝
⌜⌝-+ zero    = reflexive-∼ _
⌜⌝-+ (suc m) = suc λ { .force → ⌜⌝-+ m }

-- Truncated subtraction of a natural number.

infixl 6 _∸_

_∸_ : Conat ∞ → ℕ → Conat ∞
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = force m ∸ n

-- Infinity is a left zero of _∸_ (up to bisimilarity).

∸-left-zero-infinity : ∀ {i} n → [ i ] infinity ∸ n ∼ infinity
∸-left-zero-infinity zero    = reflexive-∼ _
∸-left-zero-infinity (suc n) = ∸-left-zero-infinity n

-- Zero is a left zero of _∸_ (up to bisimilarity).

∸-left-zero-zero : ∀ {i} n → [ i ] zero ∸ n ∼ zero
∸-left-zero-zero zero    = reflexive-∼ _
∸-left-zero-zero (suc n) = reflexive-∼ _

-- Zero is a right identity of subtraction (up to bisimilarity).

∸-right-identity : ∀ {i} n → [ i ] n ∸ zero ∼ n
∸-right-identity = reflexive-∼

-- Subtraction preserves bisimilarity and equality.

infixl 6 _∸-cong_

_∸-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ ∞ ] m₁ ∼ m₂ → n₁ ≡ n₂ → [ i ] m₁ ∸ n₁ ∼ m₂ ∸ n₂
_∸-cong_ {n₁ = zero}  p       refl = p
_∸-cong_ {n₁ = suc _} zero    refl = reflexive-∼ _
_∸-cong_ {n₁ = suc n} (suc p) refl = force p ∸-cong (refl {x = n})

-- ⌜_⌝ is homomorphic with respect to subtraction.

⌜⌝-∸ : ∀ m n {i} → [ i ] ⌜ m Nat.∸ n ⌝ ∼ ⌜ m ⌝ ∸ n
⌜⌝-∸ m       zero    = reflexive-∼ _
⌜⌝-∸ zero    (suc n) = reflexive-∼ _
⌜⌝-∸ (suc m) (suc n) = ⌜⌝-∸ m n

-- Multiplication.

infixl 7 _*_

_*_ : ∀ {i} → Conat i → Conat i → Conat i
zero  * n     = zero
m     * zero  = zero
suc m * suc n = suc λ { .force → n .force + m .force * suc n }

-- One is a left and right identity of multiplication (up to
-- bisimilarity).

*-left-identity : ∀ {i} n → [ i ] ⌜ 1 ⌝ * n ∼ n
*-left-identity zero    = reflexive-∼ _
*-left-identity (suc n) = suc λ { .force →
  n .force + zero  ∼⟨ +-right-identity _ ⟩
  n .force         ∎∼ }

*-right-identity : ∀ {i} n → [ i ] n * ⌜ 1 ⌝ ∼ n
*-right-identity zero    = reflexive-∼ _
*-right-identity (suc n) = suc λ { .force → *-right-identity _ }

-- Zero is a left and right zero of multiplication (up to
-- bisimilarity).

*-left-zero : ∀ {i n} → [ i ] zero * n ∼ zero
*-left-zero = reflexive-∼ _

*-right-zero : ∀ {i n} → [ i ] n * zero ∼ zero
*-right-zero {n = zero}  = reflexive-∼ _
*-right-zero {n = suc n} = reflexive-∼ _

-- An unfolding lemma for multiplication.

suc*∼+* : ∀ {m n i} → [ i ] suc m * n ∼ n + m .force * n
suc*∼+* {m} {zero}  =
  zero             ∼⟨ symmetric-∼ *-right-zero ⟩
  m .force * zero  ∎∼
suc*∼+* {m} {suc n} = suc λ { .force → reflexive-∼ _ }

-- Multiplication distributes over addition.

*-+-distribˡ : ∀ m {n o i} → [ i ] m * (n + o) ∼ m * n + m * o
*-+-distribˡ zero                = reflexive-∼ _
*-+-distribˡ (suc m) {zero}  {o} = reflexive-∼ _
*-+-distribˡ (suc m) {suc n} {o} = suc λ { .force →
  n .force + o + m .force * (suc n + o)               ∼⟨ (_ ∎∼) +-cong *-+-distribˡ (m .force) ⟩
  n .force + o + (m .force * suc n + m .force * o)    ∼⟨ symmetric-∼ (+-assoc (n .force)) ⟩
  n .force + (o + (m .force * suc n + m .force * o))  ∼⟨ (n .force ∎∼) +-cong +-assoc o ⟩
  n .force + ((o + m .force * suc n) + m .force * o)  ∼⟨ (n .force ∎∼) +-cong (+-comm o +-cong (_ ∎∼)) ⟩
  n .force + ((m .force * suc n + o) + m .force * o)  ∼⟨ (n .force ∎∼) +-cong symmetric-∼ (+-assoc (m .force * _)) ⟩
  n .force + (m .force * suc n + (o + m .force * o))  ∼⟨ +-assoc (n .force) ⟩
  n .force + m .force * suc n + (o + m .force * o)    ∼⟨ (n .force + _ ∎∼) +-cong symmetric-∼ suc*∼+* ⟩
  n .force + m .force * suc n + suc m * o             ∎∼ }

*-+-distribʳ : ∀ m {n o i} → [ i ] (m + n) * o ∼ m * o + n * o
*-+-distribʳ zero               = reflexive-∼ _
*-+-distribʳ (suc m) {n} {zero} =
  zero      ∼⟨ symmetric-∼ *-right-zero ⟩
  n * zero  ∎∼
*-+-distribʳ (suc m) {n} {suc o} = suc λ { .force →
  o .force + (m .force + n) * suc o          ∼⟨ (_ ∎∼) +-cong *-+-distribʳ (m .force) ⟩
  o .force + (m .force * suc o + n * suc o)  ∼⟨ +-assoc (o .force) ⟩
  o .force + m .force * suc o + n * suc o    ∎∼ }

-- Multiplication is associative.

*-assoc : ∀ m {n o i} → [ i ] m * (n * o) ∼ (m * n) * o
*-assoc zero                    = reflexive-∼ _
*-assoc (suc m) {zero}          = reflexive-∼ _
*-assoc (suc m) {suc n} {zero}  = reflexive-∼ _
*-assoc (suc m) {suc n} {suc o} = suc λ { .force →
  o .force + n .force * suc o + m .force * (suc n * suc o)    ∼⟨ symmetric-∼ (+-assoc (o .force)) ⟩
  o .force + (n .force * suc o + m .force * (suc n * suc o))  ∼⟨ (o .force ∎∼) +-cong ((_ ∎∼) +-cong *-assoc (m .force)) ⟩
  o .force + (n .force * suc o + (m .force * suc n) * suc o)  ∼⟨ (o .force ∎∼) +-cong symmetric-∼ (*-+-distribʳ (n .force)) ⟩
  o .force + (n .force + m .force * suc n) * suc o            ∎∼ }

-- Multiplication is commutative.

*-comm : ∀ m {n i} → [ i ] m * n ∼ n * m
*-comm zero {n} =
  zero      ∼⟨ symmetric-∼ *-right-zero ⟩
  n * zero  ∎∼
*-comm (suc m) {zero}  = reflexive-∼ _
*-comm (suc m) {suc n} = suc λ { .force →
  n .force + m .force * suc n                  ∼⟨ (_ ∎∼) +-cong *-comm (m .force) ⟩
  n .force + suc n * m .force                  ∼⟨ (n .force ∎∼) +-cong suc*∼+* ⟩
  n .force + (m .force + n .force * m .force)  ∼⟨ +-assoc (n .force) ⟩
  (n .force + m .force) + n .force * m .force  ∼⟨ +-comm (n .force) +-cong *-comm _ ⟩
  (m .force + n .force) + m .force * n .force  ∼⟨ symmetric-∼ (+-assoc (m .force)) ⟩
  m .force + (n .force + m .force * n .force)  ∼⟨ (m .force ∎∼) +-cong symmetric-∼ suc*∼+* ⟩
  m .force + suc m * n .force                  ∼⟨ (m .force ∎∼) +-cong *-comm (suc m) ⟩
  m .force + n .force * suc m                  ∎∼ }

-- An unfolding lemma for multiplication.

*suc∼+* : ∀ {m n i} → [ i ] m * suc n ∼ m + m * n .force
*suc∼+* {m} {n} =
  m * suc n         ∼⟨ *-comm _ ⟩
  suc n * m         ∼⟨ suc*∼+* ⟩
  m + n .force * m  ∼⟨ (_ ∎∼) +-cong *-comm (n .force) ⟩
  m + m * n .force  ∎∼

-- Multiplication preserves bisimilarity.

infixl 7 _*-cong_

_*-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] m₁ * n₁ ∼ m₂ * n₂
zero  *-cong _     = zero
suc p *-cong zero  = zero
suc p *-cong suc q = suc λ { .force →
  q .force +-cong p .force *-cong suc q }

-- ⌜_⌝ is homomorphic with respect to multiplication.

⌜⌝-* : ∀ m {n i} → [ i ] ⌜ m Nat.* n ⌝ ∼ ⌜ m ⌝ * ⌜ n ⌝
⌜⌝-* zero        = reflexive-∼ _
⌜⌝-* (suc m) {n} =
  ⌜ n Nat.+ m Nat.* n ⌝  ∼⟨ ⌜⌝-+ n ⟩
  ⌜ n ⌝ + ⌜ m Nat.* n ⌝      ∼⟨ reflexive-∼ _ +-cong ⌜⌝-* m ⟩
  ⌜ n ⌝ + ⌜ m ⌝ * ⌜ n ⌝          ∼⟨ symmetric-∼ suc*∼+* ⟩
  ⌜ suc m ⌝ * ⌜ n ⌝              ∎∼

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

-- [ ∞ ] m < n means that m is less than n (if n is finite).

infix 4 [_]_<_

[_]_<_ : Size → Conat′ ∞ → Conat ∞ → Set
[ i ] m < n = [ i ] suc m ≤ n

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

-- No number is less than zero.

≮0 : ∀ {n i} → ¬ ([ i ] n < zero)
≮0 ()

-- If a number is not bounded from above by any natural number, then
-- it is bisimilar to infinity.

¬≤⌜⌝→∼∞ : ∀ {i} m → (∀ n → ¬ ([ ∞ ] m ≤ ⌜ n ⌝)) → [ i ] m ∼ infinity
¬≤⌜⌝→∼∞ zero    zero≰ = ⊥-elim (zero≰ 0 zero)
¬≤⌜⌝→∼∞ (suc m) hyp   =
  suc λ { .force →
    ¬≤⌜⌝→∼∞ (force m) λ n → λ p → hyp (suc n) (suc λ { .force → p }) }

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

-- "Equational" reasoning combinators.

infix  -1 finally-≤ _∎≤
infixr -2 step-≤ step-∼≤ _≡⟨⟩≤_

_∎≤ : ∀ {i} n → [ i ] n ≤ n
_∎≤ = reflexive-≤

step-≤ : ∀ {i} m {n o} → [ i ] n ≤ o → [ i ] m ≤ n → [ i ] m ≤ o
step-≤ _ n≤o m≤n = transitive-≤ m≤n n≤o

syntax step-≤ m n≤o m≤n = m ≤⟨ m≤n ⟩ n≤o

step-∼≤ : ∀ {i} m {n o} → [ i ] n ≤ o → [ i ] m ∼ n → [ i ] m ≤ o
step-∼≤ _ n≤o m∼n = step-≤ _ n≤o (∼→≤ m∼n)

syntax step-∼≤ m n≤o m∼n = m ∼⟨ m∼n ⟩≤ n≤o

_≡⟨⟩≤_ : ∀ {i} m {n} → [ i ] m ≤ n → [ i ] m ≤ n
_ ≡⟨⟩≤ m≤n = m≤n

finally-≤ : ∀ {i} m n → [ i ] m ≤ n → [ i ] m ≤ n
finally-≤ _ _ m≤n = m≤n

syntax finally-≤ m n m≤n = m ≤⟨ m≤n ⟩∎ n ∎≤

-- The ordering relation respects the ordering relation
-- (contravariantly in the first argument).

infix 4 _≤-cong-≤_

_≤-cong-≤_ :
  ∀ {m m′ n n′ i} →
  [ i ] m′ ≤ m → [ i ] n ≤ n′ → [ i ] m ≤ n → [ i ] m′ ≤ n′
_≤-cong-≤_ {m} {m′} {n} {n′} m≥m′ n≤n′ m≤n =
  m′  ≤⟨ m≥m′ ⟩
  m   ≤⟨ m≤n ⟩
  n   ≤⟨ n≤n′ ⟩
  n′  ∎≤

-- A kind of preservation result for bisimilarity, ordering and
-- logical equivalence.

infix 4 _≤-cong-∼_

_≤-cong-∼_ :
  ∀ {m m′ n n′ i} →
  [ i ] m ∼ m′ → [ i ] n ∼ n′ → ([ i ] m ≤ n) ⇔ ([ i ] m′ ≤ n′)
m∼m′ ≤-cong-∼ n∼n′ = record
  { to   = record { _⟨$⟩_ = ∼→≤ (symmetric-∼ m∼m′) ≤-cong-≤ ∼→≤ n∼n′ ; cong = λ { refl → refl } }
  ; from = record { _⟨$⟩_ = ∼→≤ m∼m′ ≤-cong-≤ ∼→≤ (symmetric-∼ n∼n′) ; cong = λ { refl → refl } }
  }

-- Some inversion lemmas.

cancel-suc-≤ :
  ∀ {i m n} → [ i ] suc m ≤ suc n → [ i ] force m ≤′ force n
cancel-suc-≤ (suc p) = p

cancel-pred-≤ :
  ∀ {m n i} →
  [ i ] ⌜ 1 ⌝ ≤ n →
  [ i ] pred m ≤′ pred n →
  [ i ] m ≤ n
cancel-pred-≤ {zero}  (suc _) = λ _ → zero
cancel-pred-≤ {suc _} (suc _) = suc

cancel-∸-suc-≤ :
  ∀ {m n o i} →
  [ ∞ ] ⌜ o ⌝′ < n →
  [ i ] m ∸ suc o ≤′ n ∸ suc o →
  [ i ] m ∸ o ≤ n ∸ o
cancel-∸-suc-≤ {zero} {n} {o} _ _ =
  zero ∸ o  ∼⟨ ∸-left-zero-zero o ⟩≤
  zero      ≤⟨ zero ⟩∎
  n ∸ o     ∎≤
cancel-∸-suc-≤ {suc _} {_}     {zero}  (suc _)   = suc
cancel-∸-suc-≤ {suc m} {suc n} {suc o} (suc o<n) =
  cancel-∸-suc-≤ (force o<n)

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
≤-step {suc m} {n} p = suc λ { .force →
  force m  ≤⟨ ≤suc ⟩
  suc m    ≤⟨ force p ⟩∎
  force n  ∎≤ }

-- If m is less than n, then m is less than or equal to n.

<→≤ : ∀ {i m n} → [ i ] m < n → [ i ] force m ≤ n
<→≤ (suc p) = ≤-step p

-- If you add something to a number, then you get something that is
-- greater than or equal to what you started with.

m≤n+m : ∀ {i m n} → [ i ] m ≤ n + m
m≤n+m {n = zero}  = reflexive-≤ _
m≤n+m {n = suc n} = ≤-step λ { .force → m≤n+m }

m≤m+n : ∀ {m n i} → [ i ] m ≤ m + n
m≤m+n {m} {n} =
  m      ≤⟨ m≤n+m ⟩
  n + m  ≤⟨ ∼→≤ (+-comm n) ⟩∎
  m + n  ∎≤

-- A form of associativity for _∸_.

∸-∸-assoc : ∀ {m} n {k i} → [ i ] (m ∸ n) ∸ k ∼ m ∸ (n Nat.+ k)
∸-∸-assoc         zero            = _ ∎∼
∸-∸-assoc {zero}  (suc _) {zero}  = _ ∎∼
∸-∸-assoc {zero}  (suc _) {suc _} = _ ∎∼
∸-∸-assoc {suc _} (suc n)         = ∸-∸-assoc n

-- A limited form of associativity for _+_ and _∸_.

+-∸-assoc : ∀ {m n k i} →
            [ ∞ ] ⌜ k ⌝ ≤ n → [ i ] (m + n) ∸ k ∼ m + (n ∸ k)
+-∸-assoc {m} {n} {zero} zero =
  m + n ∸ 0    ≡⟨⟩∼
  m + n        ≡⟨⟩∼
  m + (n ∸ 0)  ∎∼
+-∸-assoc {m} {suc n} {suc k} (suc k≤n) =
  m + suc n ∸ suc k            ∼⟨ symmetric-∼ (1++∼+suc m) ∸-cong refl {x = suc k} ⟩
  ⌜ 1 ⌝ + m + force n ∸ suc k  ≡⟨⟩∼
  m + force n ∸ k              ∼⟨ +-∸-assoc (force k≤n) ⟩
  m + (force n ∸ k)            ≡⟨⟩∼
  m + (suc n ∸ suc k)          ∎∼

-- If you subtract a number and then add it again, then you get back
-- what you started with if the number is less than or equal to the
-- number that you started with.

∸+≡ : ∀ {m n i} → [ i ] ⌜ n ⌝ ≤ m → [ i ] (m ∸ n) + ⌜ n ⌝ ∼ m
∸+≡ {m} {zero} zero =
  m + zero  ∼⟨ +-right-identity _ ⟩∎
  m         ∎∼
∸+≡ {.suc m} {suc n} (suc p) =
  force m ∸ n + ⌜ suc n ⌝        ∼⟨ symmetric-∼ (1++∼+suc _) ⟩
  ⌜ 1 ⌝ + (force m ∸ n) + ⌜ n ⌝  ∼⟨ symmetric-∼ (+-assoc ⌜ 1 ⌝) ⟩
  ⌜ 1 ⌝ + (force m ∸ n + ⌜ n ⌝)  ∼⟨ (suc λ { .force → ∸+≡ (force p) }) ⟩
  ⌜ 1 ⌝ + force m                ∼⟨ (suc λ { .force → _ ∎∼ }) ⟩∎
  suc m                          ∎∼

-- If you subtract a natural number and then add it again, then you
-- get something that is greater than or equal to what you started
-- with.

≤∸+ : ∀ m n {i} → [ i ] m ≤ (m ∸ n) + ⌜ n ⌝
≤∸+ m zero =
  m          ∼⟨ symmetric-∼ (+-right-identity _) ⟩≤
  m + ⌜ 0 ⌝  ∎≤
≤∸+ zero    (suc n) = zero
≤∸+ (suc m) (suc n) =
  suc m                          ≤⟨ (suc λ { .force → ≤∸+ (force m) n }) ⟩
  ⌜ 1 ⌝ + (force m ∸ n + ⌜ n ⌝)  ∼⟨ +-assoc ⌜ 1 ⌝ ⟩≤
  ⌜ 1 ⌝ + (force m ∸ n) + ⌜ n ⌝  ∼⟨ 1++∼+suc _ ⟩≤
  force m ∸ n + ⌜ suc n ⌝        ≡⟨⟩≤
  suc m ∸ suc n + ⌜ suc n ⌝      ∎≤

-- If you subtract something from a number you get a number that is
-- less than or equal to the one you started with.

∸≤ : ∀ {m} n {i} → [ i ] m ∸ n ≤ m
∸≤         zero    = _ ∎≤
∸≤ {zero}  (suc _) = _ ∎≤
∸≤ {suc m} (suc n) = ≤-step λ { .force → ∸≤ n }

-- Lemmas relating the ordering relation, subtraction and the
-- successor function.

∸suc≤→∸≤suc :
  ∀ {i} m n {o} →
  [ i ] m ∸ suc n ≤ force o → [ i ] m ∸ n ≤ suc o
∸suc≤→∸≤suc zero    zero    p = zero
∸suc≤→∸≤suc zero    (suc n) p = zero
∸suc≤→∸≤suc (suc m) zero    p = suc λ { .force → p }
∸suc≤→∸≤suc (suc m) (suc n) p = ∸suc≤→∸≤suc (force m) n p

∸≤suc→∸suc≤ :
  ∀ {i} {j : Size< i} m n {o} →
  [ i ] m ∸ n ≤ suc o → [ j ] m ∸ suc n ≤ force o
∸≤suc→∸suc≤ zero    zero    p       = zero
∸≤suc→∸suc≤ zero    (suc n) p       = zero
∸≤suc→∸suc≤ (suc m) zero    (suc p) = force p
∸≤suc→∸suc≤ (suc m) (suc n) p       = ∸≤suc→∸suc≤ (force m) n p

-- One can decide whether a natural number is greater than or equal
-- to, or less than, any number.

≤⌜⌝⊎>⌜⌝ : ∀ {i} m n → ([ i ] m ≤ ⌜ n ⌝) ⊎ ([ i ] ⌜ n ⌝′ < m)
≤⌜⌝⊎>⌜⌝ zero    _       = inj₁ zero
≤⌜⌝⊎>⌜⌝ (suc m) zero    = inj₂ (suc λ { .force → zero })
≤⌜⌝⊎>⌜⌝ (suc m) (suc n) =
    map (λ (p : [ _ ] _ ≤ _) → suc λ { .force → p })
        (λ (p : [ _ ] _ < _) → suc λ { .force → p })
        (≤⌜⌝⊎>⌜⌝ (force m) n)

-- One can decide whether a natural number is less than or equal to,
-- or greater than, any number.

⌜⌝≤⊎⌜⌝> : ∀ {i} m n → [ i ] ⌜ m ⌝ ≤ n ⊎ [ i ] ⌜ 1 ⌝ + n ≤ ⌜ m ⌝
⌜⌝≤⊎⌜⌝> zero    _       = inj₁ zero
⌜⌝≤⊎⌜⌝> (suc m) zero    = inj₂ (suc λ { .force → zero })
⌜⌝≤⊎⌜⌝> (suc m) (suc n) =
    map (λ (p : [ _ ] _ ≤ _) → suc λ { .force → p })
        (λ p                 → suc λ { .force → suc n            ≤⟨ (suc λ { .force → _ ∎≤ }) ⟩
                                                ⌜ 1 ⌝ + force n  ≤⟨ p ⟩∎
                                                ⌜ m ⌝            ∎≤ })
        (⌜⌝≤⊎⌜⌝> m (force n))

-- ⌜_⌝ is monotone.
nat≮0 : ∀ n → ¬ (Nat._<_ n zero)
nat≮0 n = λ { () }

⌜⌝-mono : ∀ {m n i} → m ≤ n → [ i ] ⌜ m ⌝ ≤ ⌜ n ⌝
⌜⌝-mono {zero}          m≤n = zero
⌜⌝-mono {suc _} {zero}  m≤n = ⊥-elim (nat≮0 _ m≤n)
⌜⌝-mono {suc _} {suc _} (Nat.s≤s m≤n) =
  suc λ { .force → ⌜⌝-mono (m≤n) } --

-- If two natural numbers are related by [ ∞ ]_≤_, then they are also
-- related by _≤_.

⌜⌝-mono⁻¹ : ∀ {m n} → [ ∞ ] ⌜ m ⌝ ≤ ⌜ n ⌝ → m ≤ n
⌜⌝-mono⁻¹ {zero}          zero      = Nat.z≤n
⌜⌝-mono⁻¹ {suc _} {zero}  ()
⌜⌝-mono⁻¹ {suc _} {suc _} (suc m≤n) =
  Nat.s≤s (⌜⌝-mono⁻¹ (force m≤n))

-- The pred function is monotone.

pred-mono : ∀ {m n} → [ ∞ ] m ≤ n → [ ∞ ] pred m ≤ pred n
pred-mono zero    = zero
pred-mono (suc p) = force p

-- Addition is monotone.

infixl 6 _+-mono_

_+-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] m₁ + n₁ ≤ m₂ + n₂
_+-mono_ {m₁ = m₁} {m₂} {n₁} {n₂} zero q =
  zero + n₁  ≡⟨⟩≤
  n₁         ≤⟨ q ⟩
  n₂         ≤⟨ m≤n+m ⟩∎
  m₂ + n₂    ∎≤
suc p +-mono q = suc λ { .force → force p +-mono q }

-- Subtraction is monotone in its first argument and antitone in its
-- second argument.

infixl 6 _∸-mono_

_∸-mono_ : ∀ {m₁ m₂ n₁ n₂ i} →
           [ ∞ ] m₁ ≤ m₂ → n₂ ≤ n₁ → [ i ] m₁ ∸ n₁ ≤ m₂ ∸ n₂
_∸-mono_              {n₁ = zero}   {zero}  p  _ = p
_∸-mono_              {n₁ = zero}   {suc _} _  q = ⊥-elim (nat≮0 _ q)
_∸-mono_ {zero}       {n₁ = suc n₁}         _  _ = zero
_∸-mono_ {suc _}  {zero}   {suc _}          () _
_∸-mono_ {suc m₁} {suc m₂} {suc n₁} {zero}  p  _ = force m₁ ∸ n₁  ≤⟨ ∸≤ n₁ ⟩
                                                   force m₁       ≤⟨ ≤suc ⟩
                                                   suc m₁         ≤⟨ p ⟩∎
                                                   suc m₂         ∎≤
_∸-mono_ {suc _}  {suc _}  {suc _}  {suc _} p  (Nat.s≤s q) =
  force (cancel-suc-≤ p) ∸-mono q

-- Multiplication is monotone.

infixl 7 _*-mono_

_*-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] m₁ * n₁ ≤ m₂ * n₂
zero  *-mono _     = zero
suc _ *-mono zero  = zero
suc p *-mono suc q = suc λ { .force →
  q .force +-mono p .force *-mono suc q  }

------------------------------------------------------------------------
-- Minimum and maximum

-- The smallest number.

min : ∀ {i} → Conat i → Conat i → Conat i
min zero    n       = zero
min m       zero    = zero
min (suc m) (suc n) = suc λ { .force → min (force m) (force n) }

-- The largest number.

max : ∀ {i} → Conat i → Conat i → Conat i
max zero    n = n
max (suc m) n = suc λ { .force → max (force m) (pred n) }

-- The minimum of two numbers is less than or equal to both of them.

min≤ˡ : ∀ {i} m n → [ i ] min m n ≤ m
min≤ˡ zero    _       = zero
min≤ˡ (suc _) zero    = zero
min≤ˡ (suc m) (suc n) = suc λ { .force → min≤ˡ (force m) (force n) }

min≤ʳ : ∀ {i} m n → [ i ] min m n ≤ n
min≤ʳ zero    _       = zero
min≤ʳ (suc _) zero    = zero
min≤ʳ (suc m) (suc n) = suc λ { .force → min≤ʳ (force m) (force n) }

-- The maximum of two numbers is greater than or equal to both of
-- them.

ˡ≤max : ∀ {i} m n → [ i ] m ≤ max m n
ˡ≤max zero    _ = zero
ˡ≤max (suc m) n = suc λ { .force → ˡ≤max (force m) (pred n) }

ʳ≤max : ∀ {i} m n → [ i ] n ≤ max m n
ʳ≤max zero    _       = reflexive-≤ _
ʳ≤max (suc _) zero    = zero
ʳ≤max (suc m) (suc n) = suc λ { .force → ʳ≤max (force m) (force n) }

_max-mono_ : ∀ {i m₁ m₂ n₁ n₂} →
           [ i ] m₁ ≤ m₂ → [ i ] n₁ ≤ n₂ → [ i ] max m₁ n₁ ≤ max m₂ n₂
_max-mono_ {m₁ = m₁} {m₂} {n₁} {n₂} zero q =
  max zero n₁  ≡⟨⟩≤
  n₁         ≤⟨ q ⟩
  n₂         ≤⟨ ʳ≤max m₂ n₂ ⟩∎
  max m₂ n₂    ∎≤
suc p max-mono zero = suc λ { .force → (force p) max-mono zero }
suc p max-mono suc q = suc λ { .force → (force p) max-mono (force q) }


-- Zero is a left and right identity of max (up to bisimilarity).

max-left-identity : ∀ {i} n → [ i ] max zero n ∼ n
max-left-identity = reflexive-∼

max-right-identity : ∀ {i} n → [ i ] max n zero ∼ n
max-right-identity zero    = zero
max-right-identity (suc n) = suc λ { .force → max-right-identity (force n) }


infixl 6 _max-cong_

_max-cong_ :
  ∀ {i m₁ m₂ n₁ n₂} →
  [ i ] m₁ ∼ m₂ → [ i ] n₁ ∼ n₂ → [ i ] max m₁ n₁ ∼ max m₂ n₂
zero  max-cong q = q
_max-cong_ {i} {.suc m} {.suc n} {zero} {zero}  (suc p) zero = suc λ { .force → transitive-∼ (max-right-identity (force m)) (transitive-∼ (force p) (symmetric-∼ (max-right-identity (force n)))) }
suc p max-cong suc q = suc λ { .force → (force p) max-cong (force q) }

pred≤ : ∀ {i m} → [ i ] pred m ≤ m
pred≤ {i} {zero} = zero
pred≤ {i} {suc m} = ≤suc

max≤+ : ∀ {i m n} → [ i ] max m n ≤ m + n
max≤+ {i} {zero} {n} = reflexive-≤ (max zero n)
max≤+ {i} {suc x} {n} = suc λ { .force → transitive-≤ (max≤+ {m = force x} {n = pred n}) (reflexive-≤ (force x) +-mono pred≤) }

pred-max : ∀ {i} m n → [ i ] max (pred m) (pred n) ∼ pred (max m n)
pred-max zero n = reflexive-∼ (pred n)
pred-max (suc m) n = reflexive-∼ (max (force m) (pred n))

max-assoc : ∀ {i} n m o → [ i ] max (max n m) o ∼ max n (max m o)
max-assoc zero m o = reflexive-∼ (max m o)
max-assoc (suc n) m o = suc λ { .force → transitive-∼ (max-assoc (force n) (pred m) (pred o)) (reflexive-∼ (force n) max-cong pred-max m o) }

-- Max is commutative

max-comm : ∀ {i} n m → [ i ] max n m ∼ max m n
max-comm zero zero = zero
max-comm zero (suc m) = suc λ { .force → symmetric-∼ (max-right-identity (force m)) }
max-comm (suc n) zero = suc λ { .force → max-right-identity (force n) }
max-comm (suc n) (suc m) = suc λ { .force → max-comm (force n) (force m) }

interchange : ∀ {i} a b c d → [ i ] max (a + b) (c + d) ≤ (max a c) + (max b d)
interchange {i} zero b zero d = reflexive-≤ (max (zero + b) (zero + d))
interchange {i} zero zero (suc c) d = reflexive-≤ (max (zero + zero) (suc c + d))
interchange {i} zero (suc b) (suc c) zero = suc λ { .force → (transitive-≤ (∼→≤ (reflexive-∼ (force b) max-cong +-right-identity (force c))) (transitive-≤ (max≤+ {_} {force b} {force c}) (transitive-≤ (∼→≤ (+-comm (force b))) ((reflexive-≤ (force c)) +-mono transitive-≤ (≤suc {_} {b}) (suc λ { .force → ∼→≤ (symmetric-∼ (max-right-identity (force b))) })) ))) }
interchange {i} zero (suc b) (suc c) (suc d) = suc λ { .force → transitive-≤ (interchange zero (force b) (force c) (suc d)) ((reflexive-≤ (force c)) +-mono transitive-≤ (∼→≤ (max-comm (force b) (suc d))) (suc λ { .force → transitive-≤ (∼→≤ (max-comm (force d) (pred (force b)))) (pred≤ max-mono reflexive-≤ (force d)) })) }
interchange {i} (suc x) b zero zero = suc λ { .force → ∼→≤ (transitive-∼ (max-right-identity (force x + b)) ((symmetric-∼ (max-right-identity (force x))) +-cong (symmetric-∼ (max-right-identity b)))) }
interchange {i} (suc a) zero zero (suc d) = suc λ { .force →  transitive-≤ (∼→≤ ((+-right-identity (force a)) max-cong (reflexive-∼ (force d)))) (transitive-≤ (max≤+ {_} {force a}) (ˡ≤max (force a) zero +-mono ≤suc)) }
interchange {i} (suc a) (suc b) zero (suc d) = suc λ { .force → transitive-≤ (interchange (force a) (suc b) zero (force d)) ((reflexive-≤ (max (force a) zero)) +-mono suc λ { .force → (reflexive-≤ (force b)) max-mono pred≤  }) }
interchange {i} (suc a) b (suc c) d = suc λ { .force → interchange (force a) b (force c) d }

open import Structures.Concurrent hiding (unit; merge)
open import Data.Product

F : Set → Set
F X = Conat ∞ × X

_F≈_ : {A : Set} → F A → F A → Set
(n , a) F≈ (m , a') = ([ ∞ ] n ∼ m) × a ≡ a'

_F≤_ : {A : Set} → F A → F A → Set
(n , a) F≤ (m , a') = ([ ∞ ] n ≤ m) × a ≡ a'

η : {A : Set} → A → F A
η {A} x = (zero , x)

ext : {A B : Set} → F B → (B → F A) → F A
ext {A} {B} (n , b) f with f b
... | m , a = n + m , a

ext-left : {A B : Set} (x : B) (f : B → F A) → ext (η x) f F≈ f x
ext-left x f = (reflexive-∼ (proj₁ (ext (η x) f))) , refl

ext-right : {A : Set} (t : F A) → ext t η F≈ t
ext-right (n , a) = +-right-identity n , refl

ext-assoc : {A B C : Set} (t : F C) (f : C → F B) (g : B → F A) →
            ext (ext t f) g F≈ ext t (λ x → ext (f x) g)
ext-assoc (n , c) f g with f c
... | (m , b) with g b
... | (o , a) = symmetric-∼ (+-assoc n {m} {o}) , refl

open import Data.Unit

mult : {A B : Set} → F A → F B → F (A × B)
mult (n , a) (m , b) = max n m , a , b

mult-left : {A : Set} (a : F A) →
            mult a (zero , tt) F≈ ext a (λ a₁ → η (a₁ , tt))
mult-left a = transitive-∼ (max-right-identity _) (symmetric-∼ (+-right-identity _)) , refl

mult-right : {B : Set} (b : F B) →
             mult (zero , tt) b F≈ ext b (λ b₁ → η (tt , b₁))
mult-right b = symmetric-∼ (+-right-identity _) , refl

mult-assoc : {A B C : Set} (a : F A) (b : F B) (c : F C) →
             ext (mult (mult a b) c) (λ { ((a , b) , c) → η (a , b , c) }) F≈
             mult a (mult b c)
mult-assoc (n , a) (m , b) (o , c) = transitive-∼ (+-right-identity _) (max-assoc n m o) , refl

ichg : {A B C D : Set} (a : F A) (b : F B) (f : A → F C)
       (g : B → F D) →
       mult (ext a f) (ext b g) F≤
       ext (mult a b) (λ { (a , b) → mult (f a) (g b) })
ichg {A} {B} {C} {D} (n , a) (m , b) f g with f a | g b
... | (o , c) | (p , d) = (interchange n o m p) , refl

conc : Concurrent F
conc = makeConcurrent
         _F≈_ _F≤_ η ext ext-left ext-right ext-assoc (zero , tt) mult mult-left mult-right mult-assoc ichg

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
 