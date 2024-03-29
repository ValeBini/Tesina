%<*module>
\begin{code}
module Agda where
\end{code}
%</module>

%<*booleans>
\begin{code}
data Bool : Set where
    true  : Bool
    false : Bool
\end{code}
%</booleans>

%<*not>
\begin{code}
not : Bool → Bool 
not true  = false 
not false = true 
\end{code}
%</not>

%<*naturals>
\begin{code}
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ 
\end{code}
%</naturals>

%<*add>
\begin{code}
_+_ : ℕ → ℕ → ℕ 
zero + m = m 
(suc n) + m = suc (n + m) 
\end{code}
%</add>

%<*precedence>
\begin{code}
infixl 2 _*_
infixl 1 _+_

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + n * m
\end{code}
%</precedence>

%<*lists>
\begin{code}
infixr 1 _∷_

data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A
\end{code}
%</lists>

%<*square>
\begin{code}
data Square : ℕ → Set where
  sq : (m : ℕ) → Square (m * m)
\end{code}
%</square>

%<*root> 
\begin{code}
root : (n : ℕ) → Square n → ℕ
root .(m * m) (sq m) = m
\end{code}
%</root>

%<*even>
\begin{code}
data Even : ℕ → Set where
  even-zero  : Even zero
  even-plus2 : {n : ℕ} → Even n → Even (suc (suc n))
\end{code}
%</even>

%<*half>
\begin{code}
half : (n : ℕ) → Even n → ℕ
half zero even-zero = zero
half (suc zero) ()
half (suc (suc n)) (even-plus2 e) = suc (half n e)
\end{code}
%</half>

%<*less>
\begin{code}
_<_ : ℕ → ℕ → Bool
_<_ zero    _       = true
_<_ (suc _) zero    = false
_<_ (suc x) (suc y) = x < y
\end{code}
%</less>

%<*min>
\begin{code}
min : ℕ → ℕ → ℕ 
min x y with x < y 
min x y           | true = x 
min x y           | false = y
\end{code}
%</min>

%<*min2>
\begin{code}
min₂  : ℕ → ℕ → ℕ 
min₂  x y with x < y 
...               | true = x 
...               | false = y
\end{code}
%</min2>

%<*id>
\begin{code}
identity : (A : Set) → A → A 
identity A x = x 

zero' : ℕ 
zero' = identity ℕ zero 
\end{code}
%</id>

%<*apply>
\begin{code}
apply : (A : Set) (B : A → Set) → ((x : A) → B x) → (a : A) → B a 
apply A B f a = f a
\end{code}
%</apply>

%<*sigmadata>
\begin{code}
infixr 4 _,_

data Σ′ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ′ A B
\end{code}
%</sigmadata>

%<*id2>
\begin{code}
id : {A : Set} → A → A 
id x = x 

true' : Bool 
true' = id true 
\end{code}
%</id2>

%<*one'>
\begin{code}
one' : ℕ 
one' = identity _ (suc zero) 
\end{code}
%</one'>

%<*vec>
\begin{code}
data Vec (A : Set) : ℕ → Set where 
    []  : Vec A zero 
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
%</vec>

%<*head>
\begin{code}
head : {A : Set} {n : ℕ} → Vec A (suc n) → A 
head (x ∷ xs) = x
\end{code}
%</head>

%<*filtervec>
\begin{code}
filterVec : {A : Set} {n : ℕ} → (A → Bool) → Vec A n → Σ′ ℕ (Vec A)
filterVec _ [] = zero , []
filterVec f (x ∷ xs) with filterVec f xs | f x
... | length , filtered | true = (suc length) , (x ∷ filtered) 
... | length , filtered | false = length , filtered
\end{code}
%</filtervec>

%<*moduleNumbers>
\begin{code}
module Numbers where
    data Nat : Set where
        zero : Nat 
        suc : Nat → Nat

    suc₂ : Nat → Nat 
    suc₂ n = suc (suc n)
\end{code}
%</moduleNumbers>

%<*one>
\begin{code}
one : Numbers.Nat 
one = Numbers.suc Numbers.zero
\end{code}
%</one>

%<*two>
\begin{code}
two : Numbers.Nat 
two = let open Numbers in suc one
\end{code}
%</two>

%<*two2>
\begin{code}
open Numbers 
two₂  : Nat
two₂  = suc one
\end{code}
%</two2>

%<*hidingrenaming>
\begin{code}
open Numbers hiding (suc₂) 
             renaming (Nat to natural; zero to z0; suc to successor)
\end{code}
%</hidingrenaming>

\begin{code}
-- open import Data.Bool hiding (_<_)
-- open import Data.List
\end{code}

%<*sort>
\begin{code}
module Sort (A : Set)(_<_ : A → A → Bool) where
    insert : A → List A → List A
    insert y [] = y ∷ []
    insert y (x ∷ xs) with x < y
    ...                  | true  = x ∷ insert y xs
    ...                  | false = y ∷ x ∷ xs

    sort : List A → List A
    sort []           = []
    sort (x ∷ xs) = insert x (sort xs)
\end{code}
%</sort>

%<*sort1>
\begin{code}
sort₁ : (A : Set) (_<_ : A → A → Bool) → List A → List A
sort₁  = Sort.sort
\end{code}
%</sort1>

\begin{code}
-- open import Data.Nat hiding (_<_)
\end{code}

%<*sortnat>
\begin{code}
module SortNat = Sort ℕ _<_
\end{code}
%</sortnat>

%<*sort2>
\begin{code}
sort₂  : List ℕ → List ℕ
sort₂  = SortNat.sort
\end{code}
%</sort2>

%<*opensortnat>
\begin{code}
open Sort ℕ _<_ renaming (insert to insertNat; sort to sortNat)
\end{code}
%</opensortnat>

%<*point>
\begin{code}
record Point : Set where
    field x : ℕ 
          y : ℕ
\end{code}
%</point>

%<*mkpoint>
\begin{code}
mkPoint : ℕ → ℕ → Point 
mkPoint a b = record{ x = a; y = b }
\end{code}
%</mkpoint>

%<*point2>
\begin{code}
record Point' : Set where
    constructor _,_
    field x : ℕ 
          y : ℕ

mkPoint' : ℕ → ℕ → Point' 
mkPoint' a b = a , b
\end{code}
%</point2>

%<*modpoint>
\begin{code}
module Pοint (p : Point) where
    x : ℕ 
    y : ℕ 
\end{code}
%</modpoint>

\begin{code}
    x = Point.x p
    y = Point.y p
\end{code}

%<*get>
\begin{code}
getX : Point → ℕ 
getX = Point.x 

getY : Point → ℕ 
getY p = let open Point p in y
\end{code}
%</get>

%<*monad>
\begin{code}
record Monad (M : Set → Set) : Set₁ where 
    constructor makeMonad
    field 
      return : {A : Set} → A → M A 
      _>>=_ : {A B : Set} → M A → (A → M B) → M B 

    mapM : {A B : Set} → (A → M B) → List A → M (List B) 
    mapM f [] = return [] 
    mapM f (x ∷ xs) = f x       >>= \y → 
                      mapM f xs >>= \ys → 
                      return (y ∷ ys)

mapM' : {M : Set → Set} → Monad M 
      → {A B : Set} → (A → M B) → List A → M (List B) 
mapM' {M} Mon f xs = Monad.mapM {M} Mon f xs
\end{code}
%</monad>

%<*sigmarecord>
\begin{code}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public
\end{code}
%</sigmarecord>

\begin{code}
open import Function.Equality
\end{code}

%<*ind-rec>
\begin{code}
mutual
    data U : Set where
        sig : (A : U) → (El A → U) → U 
        pi  : (A : U) → (El A → U) → U 

    El : U → Set
    El (sig A B) = Σ (El A) (λ a → El (B a)) 
    El (pi A B) = (a : (El A)) → (El (B a))   
\end{code}
%</ind-rec>

%<*mutual>
\begin{code}
mutual 
    even : ℕ → Bool 
    even zero = true 
    even (suc n) = odd n 

    odd : ℕ → Bool 
    odd zero = false
    odd (suc n) = even n
\end{code}
%</mutual>