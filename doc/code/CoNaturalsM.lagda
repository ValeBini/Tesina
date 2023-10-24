\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

module CoNaturalsM where

open import Codata.Musical.Notation
open import Relation.Binary.PropositionalEquality 
open import Relation.Binary.Structures
\end{code}

%<*def>
\begin{code} 
data Coℕ : Set where
   zero : Coℕ
   suc  : ∞ Coℕ → Coℕ
\end{code}
%</def>

%<*rels>
\begin{code} 
data _≈_ : Coℕ → Coℕ → Set where
  zero : zero ≈ zero
  suc  : ∀ {m n} → ∞ (♭ m ≈ ♭ n) → suc m ≈ suc n

data _≳_ : Coℕ → Coℕ → Set where
  zero  : zero ≳ zero
  suc   : ∀ {m n} → ∞ (♭ m ≳ ♭ n) → suc m ≳ suc n
  sucˡ  : ∀ {m n} → (♭ m) ≳ n → suc m ≳ n
\end{code}
%</rels>

%<*equiv>
\begin{code} 
refl≈ : {n : Coℕ} → n ≈ n 
refl≈ {zero}   = zero
refl≈ {suc x}  = suc (♯ refl≈)

sym≈ : {m n : Coℕ} → m ≈ n → n ≈ m 
sym≈ zero     = zero
sym≈ (suc p)  = suc (♯ (sym≈ (♭ p)))

trans≈ : {m n o : Coℕ} → m ≈ n → n ≈ o → m ≈ o 
trans≈ zero     zero     = zero
trans≈ (suc p)  (suc q)  = suc (♯ (trans≈ (♭ p) (♭ q)))

eq≈ : IsEquivalence _≈_ 
eq≈ = record { refl = refl≈ 
             ; sym = sym≈ 
             ; trans = trans≈ }
\end{code}
%</equiv>

%<*partial>
\begin{code} 
refl≳ : {n m : Coℕ} → n ≈ m → n ≳ m
refl≳ zero       = zero
refl≳ (suc m≈n)  = suc (♯ (refl≳ (♭ m≈n)))

sucʳ⁻¹ : ∀ {m} {n : ∞ Coℕ} → m ≳ suc n → m ≳ ♭ n
sucʳ⁻¹ (suc p)   = sucˡ (♭ p)
sucʳ⁻¹ (sucˡ H)  = sucˡ (sucʳ⁻¹ H)

suc⁻¹ : ∀ {m} {n : ∞ Coℕ} → suc m ≳ suc n → ♭ m ≳ ♭ n
suc⁻¹ (suc x)   = ♭ x
suc⁻¹ (sucˡ H)  = sucʳ⁻¹ H

≳suc : {n : ∞ Coℕ} → suc n ≳ ♭ n
≳suc = sucˡ (refl≳ refl≈)

trans≳zero : {m n : Coℕ} → m ≳ n → n ≳ zero → m ≳ zero
trans≳zero zero      zero      = zero
trans≳zero (suc p)   (sucˡ q)  = sucˡ (trans≳zero (♭ p) q)
trans≳zero (sucˡ p)  q         = sucˡ (trans≳zero p q)

mutual
  trans≳suc : ∀ {m n : Coℕ} {o} → m ≳ n → n ≳ suc o → m ≳ suc o
  trans≳suc (suc p)   q = suc (♯ trans≳ (♭ p) (suc⁻¹ q))
  trans≳suc (sucˡ p)  q = suc (♯ (trans≳ p (sucʳ⁻¹ q)))
  
  trans≳ : {m n p : Coℕ} → m ≳ n → n ≳ p → m ≳ p
  trans≳ {p = zero}   p q = trans≳zero p q
  trans≳ {p = suc x}  p q = trans≳suc p q

antisym≳ : ∀ {m n : Coℕ} → m ≳ n → n ≳ m → m ≈ n 
antisym≳ zero           zero           = zero
antisym≳ (suc m≳n)      (suc n≳m)      = suc (♯ (antisym≳ (♭ m≳n) (♭ n≳m)))
antisym≳ (suc m≳n)      (sucˡ n≳sucm)  = suc (♯ antisym≳ (♭ m≳n) (trans≳ n≳sucm ≳suc))
antisym≳ (sucˡ m≳sucn)  (suc n≳m)      = suc (♯ (antisym≳ (trans≳ m≳sucn ≳suc) (♭ n≳m)))
antisym≳ (sucˡ m≳sucn)  (sucˡ n≳sucm)  = suc (♯ (antisym≳ (trans≳ m≳sucn ≳suc) 
                                                          (trans≳ n≳sucm ≳suc))) 

partial≳ : IsPartialOrder _≈_ _≳_ 
partial≳ = record { isPreorder = record { isEquivalence = eq≈ 
                                        ; reflexive = refl≳ 
                                        ; trans = trans≳ } 
                  ; antisym = antisym≳ }
\end{code}
%</partial> 

%<*zero>
\begin{code}
≳zero : (n : Coℕ) → n ≳ zero
≳zero zero     = zero
≳zero (suc n)  = sucˡ (≳zero (♭ n))
\end{code}
%</zero>

%<*propmayor>
\begin{code}
≡⇒≳ : {n₁ n₂ : Coℕ} → n₁ ≡ n₂ → n₁ ≳ n₂
≡⇒≳ {zero}    {zero}     n≡    = zero
≡⇒≳ {suc n₁}  {suc .n₁}  refl  = refl≳ refl≈
\end{code}
%</propmayor>

%<*ops>
\begin{code}
max : Coℕ → Coℕ → Coℕ
max zero     n        = n
max (suc m)  zero     = suc m
max (suc m)  (suc n)  = suc (♯ (max (♭ m) (♭ n)))

sum : Coℕ → Coℕ → Coℕ
sum zero     n        = n
sum (suc m)  zero     = suc m
sum (suc m)  (suc n)  = suc (♯ (suc (♯ (sum (♭ m) (♭ n)))))
\end{code}
%</ops>

%<*zerolemas>
\begin{code}
maxzero₁ : {n : Coℕ} → n ≳ max n zero
maxzero₁ {zero}   = zero
maxzero₁ {suc n}  = refl≳ refl≈

maxzero₂ : {n : Coℕ} → max n zero ≳ n 
maxzero₂ {zero}   = zero
maxzero₂ {suc n}  = refl≳ refl≈

sumzero₁ : {m : Coℕ} → m ≳ sum m zero
sumzero₁ {zero}   = zero
sumzero₁ {suc m}  = refl≳ refl≈

sumzero₂ : {m : Coℕ} → sum m zero ≳ m 
sumzero₂ {zero}   = zero
sumzero₂ {suc x}  = refl≳ refl≈
\end{code}
%</zerolemas>

%<*syms>
\begin{code}
sym-sum : {m n : Coℕ} → sum m n ≳ sum n m
sym-sum {zero}   {zero}   = zero
sym-sum {zero}   {suc n}  = refl≳ refl≈
sym-sum {suc m}  {zero}   = refl≳ refl≈
sym-sum {suc m}  {suc n}  = suc (♯ suc (♯ (sym-sum {♭ m} {♭ n})))

sym-max : {m n : Coℕ} → max m n ≳ max n m 
sym-max {zero}   {zero}   = zero
sym-max {zero}   {suc n}  = refl≳ refl≈
sym-max {suc m}  {zero}   = refl≳ refl≈
sym-max {suc m}  {suc n}  = suc (♯ sym-max {♭ m} {♭ n}) 
\end{code}
%</syms>

%<*sumcong>
\begin{code}
≳sumzero : {m₁ m₂ n : Coℕ} → m₁ ≳ m₂ → n ≳ zero → sum m₁ n ≳ sum m₂ zero 
≳sumzero zero      zero      = zero
≳sumzero zero      (sucˡ q)  = sucˡ q
≳sumzero (suc x)   zero      = suc (♯ (♭ x))
≳sumzero (suc x)   (sucˡ q)  = suc (♯ (sucˡ (trans≳ (≳sumzero (♭ x) q) sumzero₂)))
≳sumzero (sucˡ p)  zero      = sucˡ (trans≳ p sumzero₁)
≳sumzero (sucˡ p)  (sucˡ q)  = sucˡ (sucˡ (≳sumzero p q))

≳sum : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≳ m₂ → n₁ ≳ n₂ → sum m₁ n₁ ≳ sum m₂ n₂
≳sum zero       ≳n         = ≳n
≳sum (suc x)    zero       = suc x
≳sum (suc x)    (suc x₁)   = suc (♯ (suc (♯ (≳sum (♭ x) (♭ x₁)))))
≳sum (sucˡ ≳m)  (sucˡ ≳n)  = sucˡ (sucˡ (≳sum ≳m ≳n))
≳sum (sucˡ ≳m)  zero       = trans≳ (trans≳ ≳suc ≳m) sumzero₁
≳sum {n₂ = zero}   (suc x) (sucˡ ≳n) = suc (♯ (sucˡ (trans≳ (≳sumzero (♭ x) ≳n) sumzero₂))) 
≳sum {n₂ = suc n}  (suc x) (sucˡ ≳n) = suc (♯ suc (♯ ≳sum (♭ x) (trans≳ ≳n ≳suc)))
≳sum {suc m} {zero} {suc n} (sucˡ ≳m) (suc x) = suc (♯ (sucˡ (trans≳ (trans≳ (sym-sum {♭ m} {♭ n}) 
                                                (≳sumzero (♭ x) ≳m)) sumzero₂))) 
≳sum {m₂ = suc m} (sucˡ ≳m) (suc x) = suc (♯ (suc (♯ (≳sum (trans≳ ≳m ≳suc) (♭ x)))))
\end{code}
%</sumcong>

%<*maxcong>
\begin{code}
≳maxzero : {m₁ m₂ n : Coℕ} → m₁ ≳ m₂ → n ≳ zero → max m₁ n ≳ max m₂ zero 
≳maxzero zero      zero      = zero
≳maxzero zero      (sucˡ q)  = sucˡ q
≳maxzero (suc x)   zero      = suc x
≳maxzero (suc x)   (sucˡ q)  = suc (♯ trans≳ (≳maxzero (♭ x) q) maxzero₂)
≳maxzero (sucˡ p)  zero      = sucˡ (trans≳ p maxzero₁)
≳maxzero (sucˡ p)  (sucˡ q)  = sucˡ (≳maxzero p q)

≳max : {m₁ m₂ n₁ n₂ : Coℕ} → m₁ ≳ m₂ → n₁ ≳ n₂ → max m₁ n₁ ≳ max m₂ n₂ 
≳max zero      zero      = zero
≳max zero      (suc x)   = suc x
≳max zero      (sucˡ q)  = sucˡ q
≳max (suc x)   zero      = suc x
≳max (suc x)   (suc x₁)  = suc (♯ (≳max (♭ x) (♭ x₁)))
≳max (sucˡ p)  zero      = sucˡ (trans≳ p maxzero₁)
≳max (sucˡ p)  (sucˡ q)  = sucˡ (≳max p q) 
≳max {n₂ = zero}   (suc x) (sucˡ q) = suc (♯ (trans≳ (≳maxzero (♭ x) q) maxzero₂))
≳max {n₂ = suc n}  (suc x) (sucˡ q) = suc (♯ (≳max (♭ x) (sucʳ⁻¹ q)))
≳max {suc m} {zero} {suc n} (sucˡ p) (suc x)  = suc (♯ trans≳ (trans≳ (sym-max {♭ m} {♭ n}) 
                                                (≳maxzero (♭ x) p)) maxzero₂)
≳max {m₂ = suc m} (sucˡ p) (suc x)  = suc (♯ (≳max (sucʳ⁻¹ p) (♭ x)))
\end{code}
%</maxcong>

%<*interchange>
\begin{code}
interchange : (a b c d : Coℕ) → (sum (max a b) (max c d)) ≳ (max (sum a c) (sum b d))
interchange zero     zero     zero     zero     = zero
interchange zero     zero     zero     (suc d)  = refl≳ refl≈
interchange zero     zero     (suc c)  zero     = refl≳ refl≈
interchange zero     zero     (suc c)  (suc d)  = suc (♯ refl≳ refl≈)
interchange zero     (suc b)  zero     zero     = suc (♯ refl≳ refl≈)
interchange zero     (suc b)  zero     (suc d)  = suc (♯ (suc (♯ refl≳ refl≈)))
interchange zero     (suc b)  (suc c)  zero     = {!   !} 
interchange zero     (suc b)  (suc c)  (suc d)  = {!   !}
interchange (suc a)  zero     zero     zero     = refl≳ refl≈
interchange (suc a)  zero     zero     (suc d)  = {!   !} 
interchange (suc a)  zero     (suc c)  zero     = suc (♯ (suc (♯ refl≳ refl≈))) 
interchange (suc a)  zero     (suc c)  (suc d)  = suc (♯ {!   !})
interchange (suc a)  (suc b)  zero     zero     = suc (♯ refl≳ refl≈) 
interchange (suc a)  (suc b)  (suc c)  zero     = {!   !}
interchange (suc a)  (suc b)  zero     (suc d) with ♭ a    | inspect ♭ a
...         | zero    | [ eq ] = suc (♯ trans≳ (suc (♯ (trans≳ (≳sum (≳max (≡⇒≳ eq) (refl≳ refl≈)) 
                                (refl≳ refl≈)) (refl≳ refl≈)))) (≳max (≡⇒≳ (sym eq)) (refl≳ refl≈)))
...         | suc a₁  | [ eq ] = suc (♯ (trans≳ (suc (♯ (trans≳ (≳sum (≳max (≡⇒≳ eq) (refl≳ refl≈)) 
                                (refl≳ refl≈)) (trans≳ ((≳sum {max (suc a₁) (♭ b)} {max (♭ a₁) (♭ b)} 
                                (≳max {suc a₁} {♭ a₁} (≳suc) (refl≳ refl≈)) (refl≳ refl≈))) 
                                (trans≳ (interchange (♭ a₁) (♭ b) zero (♭ d)) (≳max {(sum (♭ a₁) zero)} 
                                {(♭ a₁)} sumzero₂ (refl≳ refl≈))))))) (≳max (≡⇒≳ (sym eq)) (refl≳ refl≈))))
interchange (suc a) (suc b) (suc c) (suc d)  = suc (♯ (suc (♯ (interchange (♭ a) (♭ b) (♭ c) (♭ d)))))  
\end{code}
%</interchange>