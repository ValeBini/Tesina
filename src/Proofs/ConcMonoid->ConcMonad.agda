module Proofs.ConcMonoid->ConcMonad where 

open import Structures.ConcurrentMonoid
open import Structures.Concurrent hiding (unit)

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Product

F : Set → Set → Set
F S X = S × X

-- paso como argumento solo lo que se necesita o la instancia completa de concurrent monoid de S?
module _ {S : Set} {cmonoid : ConcurrentMonoid S} where 

       open ConcurrentMonoid {S} cmonoid renaming (_≅ₘ_ to _≅_   ; _≲ₘ_ to _≲_ ; 
                                                   zeroₘ to zero ; _+ₘ_ to _+_ ; 
                                                   eqₘ to eq     ; sidl to +idl ; 
                                                   sidr to +idr  ; sassoc to +assoc ;
                                                   maxₘ to max   ; porderₘ to porder ;
                                                   midr to maxidr; midl to maxidl ;
                                                   massoc to maxassoc ;
                                                   ichange to interchange) 
       open IsEquivalence eq renaming (refl to reflₛ ; trans to transₛ ; sym to symₛ)
       open IsPreorder porder renaming (refl to preflₛ ; trans to ptransₛ)

       _F≈_ : ∀ {A : Set} → F S A → F S A → Set
       _F≈_ (n , a) (m , a') = (n ≅ m) × a ≡ a'

       _F≤_ : ∀ {A : Set} → F S A → F S A → Set
       _F≤_ (n , a) (m , a') = n ≲ m × a ≡ a'

       η : ∀ {A : Set} → A → F S A
       η x = (zero , x)

       ext : ∀ {A B : Set} → F S B → (B → F S A) → F S A
       ext (n , b) f with f b
       ...              | m , a = (n + m) , a

       ext-left : ∀ {A B : Set} → (x : B) (f : B → F S A) → ext (η x) f F≈ f x
       ext-left x f with f x 
       ...             | m , a = +idl m , refl

       ext-right : ∀ {A : Set} → (t : F S A) → ext t η F≈ t
       ext-right (n , a) = +idr n , refl

       ext-assoc : ∀ {A B C : Set} (t : F S C) (f : C → F S B) (g : B → F S A) →
              ext (ext t f) g F≈ ext t (λ x → ext (f x) g)
       ext-assoc (n , c) f g with f c
       ...                      | (m , b) with g b
       ...                                   | (o , a) = symₛ (+assoc n m o) , refl

       open import Data.Unit 

       unit : F S ⊤ 
       unit = zero , tt

       mult : {A B : Set} → F S A → F S B → F S (A × B)
       mult (n , a) (m , b) = max n m , a , b

       mult-left : {A : Set} (a : F S A) →
              mult a unit F≈ ext a (λ a₁ → η (a₁ , tt))
       mult-left a = transₛ (maxidr _) (symₛ (+idr _)) , refl

       mult-right : {B : Set} (b : F S B) →
              mult unit b F≈ ext b (λ b₁ → η (tt , b₁))
       mult-right (n , a) = transₛ (maxidl n) (symₛ (+idr n)) , refl  

       mult-assoc : {A B C : Set} (a : F S A) (b : F S B) (c : F S C) →
              ext (mult (mult a b) c) (λ { ((a , b) , c) → η (a , b , c) }) F≈ mult a (mult b c)
       mult-assoc (n , a) (m , b) (o , c) = transₛ (+idr (max (max n m) o)) (maxassoc n m o) , refl

       ichg : {A B C D : Set} (a : F S A) (b : F S B) (f : A → F S C) (g : B → F S D) →
              mult (ext a f) (ext b g) F≤ ext (mult a b) (λ { (a , b) → mult (f a) (g b) })
       ichg (n , a) (m , b) f g with f a     | g b
       ...                         | (o , c) | (p , d) = (interchange n o m p) , refl



cmonoid⇒cmonad : {S : Set} → ConcurrentMonoid S → Concurrent (F S)
cmonoid⇒cmonad {S} cmonoid
              = makeConcurrent 
                    (_F≈_       {S} {cmonoid})
                    (_F≤_       {S} {cmonoid})
                    (η          {S} {cmonoid})
                    (ext        {S} {cmonoid})
                    (ext-left   {S} {cmonoid}) 
                    (ext-right  {S} {cmonoid}) 
                    (ext-assoc  {S} {cmonoid}) 
                    (unit       {S} {cmonoid}) 
                    (mult       {S} {cmonoid}) 
                    (mult-left  {S} {cmonoid}) 
                    (mult-right {S} {cmonoid}) 
                    (mult-assoc {S} {cmonoid}) 
                    (ichg       {S} {cmonoid})