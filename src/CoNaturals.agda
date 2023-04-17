
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

sucʳ⁻¹ : ∀ {m : Coℕ} {n} → m ≳ (suc n) → m ≳ (♭ n)
sucʳ⁻¹ (suc m≳n)     = sucˡ (♭ m≳n)
sucʳ⁻¹ (sucˡ m≳sucn) = sucˡ (sucʳ⁻¹ m≳sucn)

refl≳ : {n : Coℕ} → n ≳ n 
refl≳ {zero}  = zero
refl≳ {suc n} = suc (♯ (refl≳))

{-# NON_TERMINATING #-}
≳zero : (n : Coℕ) → n ≳ zero 
≳zero zero    = zero
≳zero (suc n) = sucˡ (≳zero (♭ n))

trans≳ : {m n p : Coℕ} → m ≳ n → n ≳ p → m ≳ p 
trans≳ {zero}  {zero}  {zero}  m≳n           n≳p           = zero
trans≳ {suc m} {zero}  {zero}  m≳n           n≳p           = ≳zero (suc m)
trans≳ {suc m} {suc n} {zero}  m≳n           n≳p           = ≳zero (suc m)
trans≳ {suc m} {suc n} {suc p} (suc m≳n)     (suc n≳p)     = suc (♯ (trans≳ (♭ m≳n) (♭ n≳p)))
trans≳ {suc m} {suc n} {suc p} (suc m≳n)     (sucˡ n≳sucp) = suc (♯ (trans≳ (♭ m≳n) (sucʳ⁻¹ n≳sucp)))
trans≳ {suc m} {suc n} {suc p} (sucˡ m≳sucn) (suc n≳p)     = suc (♯ trans≳ (sucʳ⁻¹ m≳sucn) (♭ n≳p))
trans≳ {suc m} {suc n} {suc p} (sucˡ m≳sucn) (sucˡ n≳sucp) = suc (♯ (trans≳ (sucʳ⁻¹ m≳sucn) (sucʳ⁻¹ n≳sucp)))

≡⇒≳ : {n₁ n₂ : Coℕ} → n₁ ≡ n₂ → n₁ ≳ n₂ 
≡⇒≳ {zero}   {zero}    n≡ = zero
≡⇒≳ {suc n₁} {suc .n₁} refl = refl≳

{-# NON_TERMINATING #-}
≳suc : {n : ∞ Coℕ} → suc n ≳ ♭ n 
≳suc {n} with ♭ n   | inspect ♭ n
...         | zero  | eq     = ≳zero (suc n)
...         | suc m | [ eq ] = suc (♯ trans≳ (≡⇒≳ eq) ≳suc)

max : Coℕ → Coℕ → Coℕ 
max zero n          = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (♯ (max (♭ m) (♭ n)))

max-zero : {n : Coℕ} → n ≳ max n zero 
max-zero {zero}  = zero
max-zero {suc n} = refl≳

sum : Coℕ → Coℕ → Coℕ
sum zero n          = n
sum (suc m) zero    = suc m
sum (suc m) (suc n) = suc (♯ (suc (♯ (sum (♭ m) (♭ n)))))

sumzero : {m : Coℕ} → m ≳ sum m zero 
sumzero {zero}  = zero
sumzero {suc m} = refl≳

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

≳max₂ : {m n : Coℕ} → max m n ≳ n 
≳max₂ {zero}  {zero}  = zero
≳max₂ {zero}  {suc n} = refl≳
≳max₂ {suc m} {zero}  = ≳zero (suc m)
≳max₂ {suc m} {suc n} = suc (♯ ≳max₂)

≳sum₁ : {m n : Coℕ} → sum m n ≳ m 
≳sum₁ {zero}  {zero}  = zero
≳sum₁ {zero}  {suc n} = ≳zero (suc n)
≳sum₁ {suc m} {zero}  = refl≳
≳sum₁ {suc m} {suc n} = suc (♯ (sucˡ ≳sum₁))

≳sum₂ : {m n : Coℕ} → sum m n ≳ n 
≳sum₂ {zero}  {n} = refl≳
≳sum₂ {suc m} {zero}  = ≳zero (suc m)
≳sum₂ {suc m} {suc n} = suc (♯ (sucˡ ≳sum₂))

{-# NON_TERMINATING #-}
≳sum : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≳ m₂ → n₁ ≳ n₂ → sum m₁ n₁ ≳ sum m₂ n₂ 
≳sum {.zero}    {.zero}    {n₁}       {n₂}       zero      ≳n        = ≳n
≳sum {.(suc _)} {.(suc _)} {.zero}    {.zero}    (suc x)   zero      = suc x
≳sum {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (suc x)   (suc x₁)  = suc (♯ (suc (♯ (≳sum (♭ x) (♭ x₁)))))
≳sum {.(suc _)} {.(suc _)} {.(suc _)} {zero}     (suc x)   (sucˡ ≳n) = suc (♯ (sucˡ (trans≳ (≳sum (♭ x) ≳n) ≳sum₁)))
≳sum {.(suc _)} {.(suc _)} {.(suc _)} {suc x₁}   (suc x)   (sucˡ ≳n) = suc (♯ suc (♯ ≳sum (♭ x) (trans≳ ≳n ≳suc)))
≳sum {.(suc _)} {m₂}       {.zero}    {.zero}    (sucˡ ≳m) zero      = trans≳ (trans≳ ≳suc ≳m) sumzero
≳sum {.(suc _)} {zero}     {.(suc _)} {.(suc _)} (sucˡ ≳m) (suc x)   = suc (♯ (sucˡ (trans≳ (≳sum refl≳ (♭ x)) ≳sum₂)))
≳sum {.(suc _)} {suc x₁}   {.(suc _)} {.(suc _)} (sucˡ ≳m) (suc x)   = suc (♯ (suc (♯ (≳sum (trans≳ ≳m ≳suc) (♭ x)))))
≳sum {.(suc _)} {m₂}       {.(suc _)} {n₂}       (sucˡ ≳m) (sucˡ ≳n) = sucˡ (sucˡ (≳sum ≳m ≳n))

max-ext : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≡ m₂ → n₁ ≡ n₂ → max m₁ n₁ ≳ max m₂ n₂
max-ext {zero}   {zero}    {n₁}     {n₂}      m≡   n≡   = ≡⇒≳ n≡
max-ext {suc m₁} {suc .m₁} {zero}   {zero}    refl n≡   = refl≳
max-ext {suc m₁} {suc .m₁} {suc n₁} {suc .n₁} refl refl = suc (♯ refl≳)

sum-ext : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≡ m₂ → n₁ ≡ n₂ → sum m₁ n₁ ≳ sum m₂ n₂ 
sum-ext {zero}   {zero}    {n₁}     {n₂}      m≡   n≡   = ≡⇒≳ n≡
sum-ext {suc m₁} {suc .m₁} {zero}   {zero}    refl n≡   = refl≳
sum-ext {suc m₁} {suc .m₁} {suc n₁} {suc .n₁} refl refl = suc (♯ (suc (♯ refl≳)))

{-# NON_TERMINATING #-}
max-suc : {m : ∞ Coℕ} {n : Coℕ} → max (suc m) n ≳ max (♭ m) n 
max-suc {m} {zero}  = trans≳ (sucˡ refl≳) max-zero
max-suc {m} {suc n} with ♭ m    | inspect ♭ m 
...                    | zero   | x      = suc (♯ ≳max₂)
...                    | suc m₁ | [ eq ] = suc (♯ (trans≳ (max-ext eq refl) (max-suc {m₁} {♭ n})))

suc-max : {m : Coℕ} {n : ∞ Coℕ} → suc (♯ (max m (♭ n))) ≳ max m (suc n) 
suc-max {zero}  {n} = suc (♯ refl≳)
suc-max {suc m} {n} = suc (♯ max-suc {m} {♭ n})

-- {-# NON_TERMINATING #-}
lema₁ : {b c d : Coℕ} → suc (♯ (sum b (max c d))) ≳ max c (suc (♯ (sum b d)))
lema₁ {zero}  {zero}  {zero}  = suc (♯ zero)
lema₁ {zero}  {zero}  {suc d} = suc (♯ refl≳)
lema₁ {zero}  {suc c} {zero}  = suc (♯ trans≳ (sucˡ refl≳) max-zero)
lema₁ {zero}  {suc c} {suc d} with ♭ c    | inspect ♭ c 
...                              | zero   | [ eq ] = suc (♯ (trans≳ (suc (♯ ≳max₂)) (max-ext (sym eq) refl)))
...                              | suc c₁ | [ eq ] = suc (♯ (trans≳ (suc (♯ (trans≳ (max-ext eq refl) (max-suc {c₁} {♭ d})))) (max-ext (sym eq) refl)))
lema₁ {suc b} {zero}  {zero}  = suc (♯ refl≳)
lema₁ {suc b} {zero}  {suc d} = suc (♯ (suc (♯ (suc (♯ refl≳)))))
lema₁ {suc b} {suc c} {zero}  with ♭ c    | inspect ♭ c 
...                              | zero   | [ eq ] = suc (♯ trans≳ (suc (♯ (sucˡ ≳sum₁))) (max-ext (sym eq) refl))
...                              | suc c₁ | [ eq ] = suc (♯ (sucˡ (trans≳ (suc (♯ (trans≳ (sym-sum {♭ b} {♭ c}) (trans≳ (sum≳max {♭ c} {♭ b}) (trans≳ (max-ext eq refl) (max-suc {c₁} {♭ b})))))) (max-ext (sym eq) refl))))
lema₁ {suc b} {suc c} {suc d} = suc (♯ {! (lema₁ {♭ b} {♭ c} {♭ d})  !})

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