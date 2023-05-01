module Proofs.ConcMonoid->ConcMonad where 

open import Structures.ConcurrentMonoid
open import Structures.Concurrent 

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Product

F : Set → Set → Set
F S X = S × X

-- paso como argumento solo lo que se necesita o la instancia completa de concurrent monoid de S?

_F≈_ : {S A : Set} {cmonoid : ConcurrentMonoid S} → F S A → F S A → Set
_F≈_ {S} {A} {makeConcurrentMonoid 
              _≅ₘ_ _≲ₘ_ zeroₘ _+ₘ_ sidl sidr sassoc maxₘ midl midr massoc ichange} 
                     (n , a) (m , a') = (n ≅ₘ m) × a ≡ a' 

_F≤_ : {S A : Set} {_≲ₛ_ : S → S → Set} → F S A → F S A → Set
_F≤_ {S} {A} {_≲ₛ_} (n , a) (m , a') = n ≲ₛ m × a ≡ a'

η : {S A : Set} {z : S} → A → F S A
η {S} {A} {z} x = (z , x)

ext : {S A B : Set} {sum : S → S → S} → F S B → (B → F S A) → F S A
ext {S} {A} {B} {sum} (n , b) f with f b
...                                | m , a = (sum n m) , a

-- necesito reflexividad de la relacion en S
{-}
ext-left : {S A B : Set} {_≈ₛ_ : S → S → Set} {reflₛ : Reflexive _≈ₛ_} → (x : B) (f : B → F S A) → ext (η x) f F≈ f x
ext-left {S} {A} {B} {_≈ₛ_} {reflₛ} x f = (reflₛ (proj₁ (ext (η x) f))) , refl

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
-}


cmonoid⇒cmonad : {S : Set} → ConcurrentMonoid S → Concurrent (F S)
cmonoid⇒cmonad {S}
       cmonoid@(makeConcurrentMonoid _≅ₘ_ _≲ₘ_ zeroₘ _+ₘ_ sidl sidr sassoc maxₘ midl midr massoc ichange) 
              = makeConcurrent 
                    (λ {A} →  _F≈_ {S} {A} {cmonoid}) 
                    (λ {A} → _F≤_ {S} {A} {_≲ₘ_}) 
                    (λ {A} → η {S} {A} {zeroₘ}) 
                    (λ {A B} → ext {S} {A} {B} {_+ₘ_}) 
                    {!   !} 
                    {!   !} 
                    {!   !} 
                    {!   !} 
                    {!   !} 
                    {!   !} 
                    {!   !} 
                    {!   !} 
                    {!   !}