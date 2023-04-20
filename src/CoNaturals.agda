{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Relation.Binary.PropositionalEquality

data Coℕ : Set where
   zero : Coℕ
   suc  : ∞ Coℕ → Coℕ

inf : Coℕ
inf = suc (♯ inf)

data _≈_ : Coℕ → Coℕ → Set where
  zero : zero ≈ zero
  suc  : ∀ {m n} → ∞ (♭ m ≈ ♭ n) → suc m ≈ suc n

data _≳_ : Coℕ → Coℕ → Set where
  zero  : zero ≳ zero
  suc   : ∀ {m n} → ∞ (♭ m ≳ ♭ n) → suc m ≳ suc n
  sucˡ  : ∀ {m n} → (♭ m) ≳ n → suc m ≳ n

refl≳ : {n : Coℕ} → n ≳ n
refl≳ {zero}  = zero
refl≳ {suc n} = suc (♯ (refl≳))

succ : Coℕ → Coℕ
succ n = suc (♯ n)

sucʳ⁻¹ : ∀ {m} {n : ∞ Coℕ} → m ≳ suc n → m ≳ ♭ n
sucʳ⁻¹ {.(suc _)} {n} (suc p)  = sucˡ (♭ p)
sucʳ⁻¹ {.(suc _)} {n} (sucˡ H) = sucˡ (sucʳ⁻¹ H)

suc⁻¹ : ∀ {m} {n : ∞ Coℕ} → suc m ≳ suc n → ♭ m ≳ ♭ n
suc⁻¹ {m} {n} (suc x)  = ♭ x
suc⁻¹ {m} {n} (sucˡ H) = sucʳ⁻¹ H

trans≳zero : {m n : Coℕ} → m ≳ n → n ≳ zero → m ≳ zero
trans≳zero zero     zero     = zero
trans≳zero (suc p)  (sucˡ q) = sucˡ (trans≳zero (♭ p) q)
trans≳zero (sucˡ p) q        = sucˡ (trans≳zero p q)

mutual
  trans≳suc : ∀ {m n : Coℕ} {o} → m ≳ n → n ≳ suc o → m ≳ suc o
  trans≳suc {.(suc _)} {.(suc _)} {o} (suc p)  q = suc (♯ trans≳ (♭ p) (suc⁻¹ q))
  trans≳suc {.(suc _)} {n}        {o} (sucˡ p) q = suc (♯ (trans≳ p (sucʳ⁻¹ q)))
  
  trans≳ : {m n p : Coℕ} → m ≳ n → n ≳ p → m ≳ p
  trans≳ {p = zero}  p q = trans≳zero p q
  trans≳ {p = suc x} p q = trans≳suc p q

{-}
{-# NON_TERMINATING #-}
≳zero : (n : Coℕ) → n ≳ zero
≳zero zero = zero
≳zero (suc n) = sucˡ (≳zero (♭ n))
-} 

≡⇒≳ : {n₁ n₂ : Coℕ} → n₁ ≡ n₂ → n₁ ≳ n₂
≡⇒≳ {zero}   {zero}    n≡   = zero
≡⇒≳ {suc n₁} {suc .n₁} refl = refl≳

≳suc : {n : ∞ Coℕ} → suc n ≳ ♭ n
≳suc {n} = sucʳ⁻¹ (refl≳ {suc n})

max : Coℕ → Coℕ → Coℕ
max zero n          = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (♯ (max (♭ m) (♭ n)))

sum : Coℕ → Coℕ → Coℕ
sum zero n          = n
sum (suc m) zero    = suc m
sum (suc m) (suc n) = suc (♯ (suc (♯ (sum (♭ m) (♭ n)))))

maxzero₁ : {n : Coℕ} → n ≳ max n zero
maxzero₁ {zero}  = zero
maxzero₁ {suc n} = refl≳

maxzero₂ : {n : Coℕ} → max n zero ≳ n 
maxzero₂ {zero}  = zero
maxzero₂ {suc n} = refl≳

sumzero₁ : {m : Coℕ} → m ≳ sum m zero
sumzero₁ {zero}  = zero
sumzero₁ {suc m} = refl≳

sumzero₂ : {m : Coℕ} → sum m zero ≳ m 
sumzero₂ {zero}  = zero
sumzero₂ {suc x} = refl≳

sum≳max : {m n : Coℕ} → sum m n ≳ max m n
sum≳max {zero}  {zero}  = zero
sum≳max {zero}  {suc n} = refl≳
sum≳max {suc m} {zero}  = refl≳
sum≳max {suc m} {suc n} = suc (♯ (sucˡ (sum≳max {♭ m} {♭ n})))

sym-sum : {m n : Coℕ} → sum m n ≳ sum n m
sym-sum {zero}  {zero}  = zero
sym-sum {zero}  {suc n} = refl≳
sym-sum {suc m} {zero}  = refl≳
sym-sum {suc m} {suc n} = suc (♯ suc (♯ (sym-sum {♭ m} {♭ n})))

sym-max : {m n : Coℕ} → max m n ≳ max n m 
sym-max {zero}  {zero}  = zero
sym-max {zero}  {suc n} = refl≳
sym-max {suc m} {zero}  = refl≳
sym-max {suc m} {suc n} = suc (♯ sym-max {♭ m} {♭ n}) 

max-ext : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≡ m₂ → n₁ ≡ n₂ → max m₁ n₁ ≳ max m₂ n₂
max-ext {zero}   {zero}    {n₁}     {n₂}      m≡   n≡   = ≡⇒≳ n≡
max-ext {suc m₁} {suc .m₁} {zero}   {zero}    refl n≡   = refl≳
max-ext {suc m₁} {suc .m₁} {suc n₁} {suc .n₁} refl refl = suc (♯ refl≳)

sum-ext : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≡ m₂ → n₁ ≡ n₂ → sum m₁ n₁ ≳ sum m₂ n₂
sum-ext {zero}   {zero}    {n₁}     {n₂}      m≡   n≡   = ≡⇒≳ n≡
sum-ext {suc m₁} {suc .m₁} {zero}   {zero}    refl n≡   = refl≳
sum-ext {suc m₁} {suc .m₁} {suc n₁} {suc .n₁} refl refl = suc (♯ (suc (♯ refl≳)))

{-}
≳max₂ : {m n : Coℕ} → max m n ≳ n
≳max₂ {zero}  {zero}  = zero
≳max₂ {zero}  {suc n} = refl≳
≳max₂ {suc m} {zero}  = {!   !} -- ≳zero (suc m)
≳max₂ {suc m} {suc n} = suc (♯ ≳max₂)
-}
{-}
≳sum₁ : {m n : Coℕ} → sum m n ≳ m
≳sum₁ {zero}  {zero}  = zero
≳sum₁ {zero}  {suc n} = {!   !} -- ≳zero (suc n)
≳sum₁ {suc m} {zero}  = refl≳
≳sum₁ {suc m} {suc n} = suc (♯ (sucˡ ≳sum₁))
-}
{-}
≳sum₂ : {m n : Coℕ} → sum m n ≳ n
≳sum₂ {zero}  {n} = refl≳
≳sum₂ {suc m} {zero}  = {!   !} -- ≳zero (suc m)
≳sum₂ {suc m} {suc n} = suc (♯ (sucˡ ≳sum₂))
-} 

-- {-# NON_TERMINATING #-}
≳sumzero : {m₁ m₂ n : Coℕ} → m₁ ≳ m₂ → n ≳ zero → sum m₁ n ≳ sum m₂ zero 
≳sumzero {.zero}    {.zero}    {.zero}    zero     zero     = zero
≳sumzero {.zero}    {.zero}    {.(suc _)} zero     (sucˡ q) = sucˡ q
≳sumzero {.(suc _)} {.(suc _)} {.zero}    (suc x)  zero     = suc (♯ (♭ x))
≳sumzero {.(suc _)} {.(suc _)} {.(suc _)} (suc x)  (sucˡ q) = suc (♯ (sucˡ (trans≳ (≳sumzero (♭ x) q) sumzero₂)))
≳sumzero {.(suc _)} {m₂}       {.zero}    (sucˡ p) zero     = sucˡ (trans≳ p sumzero₁)
≳sumzero {.(suc _)} {m₂}       {.(suc _)} (sucˡ p) (sucˡ q) = sucˡ (sucˡ (≳sumzero p q))

≳sum : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≳ m₂ → n₁ ≳ n₂ → sum m₁ n₁ ≳ sum m₂ n₂
≳sum {.zero}    {.zero}    {n₁}       {n₂}       zero      ≳n        = ≳n
≳sum {.(suc _)} {.(suc _)} {.zero}    {.zero}    (suc x)   zero      = suc x
≳sum {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (suc x)   (suc x₁)  = suc (♯ (suc (♯ (≳sum (♭ x) (♭ x₁)))))
≳sum {.(suc _)} {.(suc _)} {.(suc _)} {zero}     (suc x)   (sucˡ ≳n) = suc (♯ (sucˡ (trans≳ (≳sumzero (♭ x) ≳n) sumzero₂))) -- suc (♯ (sucˡ (trans≳ (≳sum (♭ x) ≳n) ≳sum₁)))
≳sum {.(suc _)} {.(suc _)} {.(suc _)} {suc x₁}   (suc x)   (sucˡ ≳n) = suc (♯ suc (♯ ≳sum (♭ x) (trans≳ ≳n ≳suc)))
≳sum {.(suc _)} {m₂}       {.zero}    {.zero}    (sucˡ ≳m) zero      = trans≳ (trans≳ ≳suc ≳m) sumzero₁
≳sum {suc m}    {zero}     {suc n}    {.(suc _)} (sucˡ ≳m) (suc x)   = suc (♯ (sucˡ (trans≳ (trans≳ (sym-sum {♭ m} {♭ n}) (≳sumzero (♭ x) ≳m)) sumzero₂))) -- suc (♯ (sucˡ (trans≳ (≳sum refl≳ (♭ x)) ≳sum₂)))
≳sum {.(suc _)} {suc x₁}   {.(suc _)} {.(suc _)} (sucˡ ≳m) (suc x)   = suc (♯ (suc (♯ (≳sum (trans≳ ≳m ≳suc) (♭ x)))))
≳sum {.(suc _)} {m₂}       {.(suc _)} {n₂}       (sucˡ ≳m) (sucˡ ≳n) = sucˡ (sucˡ (≳sum ≳m ≳n))

≳maxzero : {m₁ m₂ n : Coℕ} → m₁ ≳ m₂ → n ≳ zero → max m₁ n ≳ max m₂ zero 
≳maxzero {.zero}    {.zero}    {.zero}    zero     zero     = zero
≳maxzero {.zero}    {.zero}    {.(suc _)} zero     (sucˡ q) = sucˡ q
≳maxzero {.(suc _)} {.(suc _)} {.zero}    (suc x)  zero     = suc x
≳maxzero {.(suc _)} {.(suc _)} {.(suc _)} (suc x)  (sucˡ q) = suc (♯ trans≳ (≳maxzero (♭ x) q) maxzero₂)
≳maxzero {.(suc _)} {m₂}       {.zero}    (sucˡ p) zero     = sucˡ (trans≳ p maxzero₁)
≳maxzero {.(suc _)} {m₂}       {.(suc _)} (sucˡ p) (sucˡ q) = sucˡ (≳maxzero p q)

≳max : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≳ m₂ → n₁ ≳ n₂ → max m₁ n₁ ≳ max m₂ n₂ 
≳max {.zero}    {.zero}    {.zero}    {.zero}    zero     zero     = zero
≳max {.zero}    {.zero}    {.(suc _)} {.(suc _)} zero     (suc x)  = suc x
≳max {.zero}    {.zero}    {.(suc _)} {n₂}       zero     (sucˡ q) = sucˡ q
≳max {.(suc _)} {.(suc _)} {.zero}    {.zero}    (suc x)  zero     = suc x
≳max {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (suc x)  (suc x₁) = suc (♯ (≳max (♭ x) (♭ x₁)))
≳max {.(suc _)} {.(suc _)} {.(suc _)} {zero}     (suc x)  (sucˡ q) = suc (♯ (trans≳ (≳maxzero (♭ x) q) maxzero₂))
≳max {.(suc _)} {.(suc _)} {.(suc _)} {suc x₁}   (suc x)  (sucˡ q) = suc (♯ (≳max (♭ x) (sucʳ⁻¹ q)))
≳max {.(suc _)} {m₂}       {.zero}    {.zero}    (sucˡ p) zero     = sucˡ (trans≳ p maxzero₁)
≳max {suc m}    {zero}     {suc n}    {.(suc _)} (sucˡ p) (suc x)  = suc (♯ trans≳ (trans≳ (sym-max {♭ m} {♭ n}) (≳maxzero (♭ x) p)) maxzero₂)
≳max {.(suc _)} {suc x₁}   {.(suc _)} {.(suc _)} (sucˡ p) (suc x)  = suc (♯ (≳max (sucʳ⁻¹ p) (♭ x)))
≳max {.(suc _)} {m₂}       {.(suc _)} {n₂}       (sucˡ p) (sucˡ q) = sucˡ (≳max p q) 

{-}
{-# NON_TERMINATING #-}
max-suc : {m : ∞ Coℕ} {n : Coℕ} → max (suc m) n ≳ max (♭ m) n
max-suc {m} {zero}  = trans≳ (sucˡ refl≳) max-zero
max-suc {m} {suc n} with ♭ m    | inspect ♭ m
...                    | zero   | x      = suc (♯ ≳max₂)
...                    | suc m₁ | [ eq ] = suc (♯ (trans≳ (max-ext eq refl) (max-suc {m₁} {♭ n})))
-}


suc-max : {m : Coℕ} {n : ∞ Coℕ} → suc (♯ (max m (♭ n))) ≳ max m (suc n)
suc-max {zero}  {n} = suc (♯ refl≳)
suc-max {suc m} {n} = suc (♯ (≳max ≳suc (refl≳ {♭ n})))

lema₁ : {b c d : Coℕ} → suc (♯ (sum b (max c d))) ≳ max c (suc (♯ (sum b d)))
lema₁ {zero}  {zero}  {zero}  = suc (♯ zero)
lema₁ {zero}  {zero}  {suc d} = suc (♯ refl≳)
lema₁ {zero}  {suc c} {zero}  = suc (♯ trans≳ (sucˡ refl≳) maxzero₁)
lema₁ {zero}  {suc c} {suc d} with ♭ c    | inspect ♭ c 
...                              | zero   | [ eq ] = suc (♯ (trans≳ (suc (♯ (≳max (≡⇒≳ eq) (refl≳ {♭ d})))) (trans≳ (trans≳ maxzero₁ (sym-max {suc d} {zero})) (≳max (≡⇒≳ (sym eq)) (refl≳ {suc d})))))
...                              | suc c₁ | [ eq ] = suc (♯ (trans≳ (suc (♯ (≳max (trans≳ (≡⇒≳ eq) ≳suc) refl≳))) (≳max (≡⇒≳ (sym eq)) (refl≳ {suc d}))))
lema₁ {suc b} {zero}  {zero}  = suc (♯ refl≳)
lema₁ {suc b} {zero}  {suc d} = suc (♯ (suc (♯ (suc (♯ refl≳)))))
lema₁ {suc b} {suc c} {zero}  with ♭ c    | inspect ♭ c
...                              | zero   | [ eq ] = suc (♯ (trans≳ (suc (♯ (sucˡ (trans≳ (≳sum (refl≳ {♭ b}) (≡⇒≳ eq)) sumzero₂)))) (≳max (≡⇒≳ (sym eq)) (refl≳ {suc b})))) 
...                              | suc c₁ | [ eq ] = suc (♯ (trans≳ (suc (♯ (sucˡ (trans≳ (sym-sum {♭ b} {♭ c}) (trans≳ (≳sum (trans≳ (≡⇒≳ eq) ≳suc) refl≳) (sum≳max {♭ c₁} {♭ b})))))) ((≳max (≡⇒≳ (sym eq)) (refl≳ {suc b}))))) 
lema₁ {suc b} {suc c} {suc d} with ♭ c    | inspect ♭ c 
...                              | zero   | [ eq ] = suc (♯ (trans≳ (suc (♯ (suc (♯ (≳sum (refl≳ {♭ b}) (trans≳ (≳max (≡⇒≳ eq) (refl≳ {♭ d})) refl≳)))))) (≳max (≡⇒≳ (sym eq)) refl≳)))
...                              | suc c₁ | [ eq ] = suc (♯ (trans≳ (suc (♯ {! lema₁ {?} {?} {?}  !})) (≳max (≡⇒≳ (sym eq)) refl≳)))

interchange : (a b c d : Coℕ) → (sum (max a b) (max c d)) ≳ (max (sum a c) (sum b d))
interchange zero    zero    zero    zero    = zero
interchange zero    zero    zero    (suc d) = refl≳
interchange zero    zero    (suc c) zero    = refl≳
interchange zero    zero    (suc c) (suc d) = suc (♯ refl≳)
interchange zero    (suc b) zero    zero    = suc (♯ refl≳)
interchange zero    (suc b) zero    (suc d) = suc (♯ (suc (♯ refl≳)))
interchange zero    (suc b) (suc c) zero    = suc (♯ sucˡ (trans≳ (sym-sum {♭ b} {♭ c}) (sum≳max {♭ c} {♭ b})))
interchange zero    (suc b) (suc c) (suc d) = suc (♯ {!  lema₁ {♭ b} {♭ c} {♭ d} !})
interchange (suc a) zero    zero    zero    = refl≳
interchange (suc a) zero    zero    (suc d) = suc (♯ (sucˡ (sum≳max {♭ a} {♭ d})))
interchange (suc a) zero    (suc c) zero    = suc (♯ (suc (♯ refl≳)))
interchange (suc a) zero    (suc c) (suc d) = suc (♯ {!   !})
interchange (suc a) (suc b) zero    zero    = suc (♯ refl≳)
interchange (suc a) (suc b) zero    (suc d) = suc (♯ {!   !})
interchange (suc a) (suc b) (suc c) zero    = suc (♯ {!   !})
interchange (suc a) (suc b) (suc c) (suc d) = suc (♯ (suc (♯ (interchange (♭ a) (♭ b) (♭ c) (♭ d)))))
