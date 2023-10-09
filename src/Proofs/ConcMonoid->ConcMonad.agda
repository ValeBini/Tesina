module Proofs.ConcMonoid->ConcMonad where 

open import Structures.ConcurrentMonoid
open import Structures.ConcurrentMonad hiding (unit)

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Product

F : Set → Set → Set
F S X = S × X

-- paso como argumento solo lo que se necesita o la instancia completa de concurrent monoid de S?
module _ {S : Set} {cmonoid : ConcurrentMonoid S} where 

       open ConcurrentMonoid {S} cmonoid renaming (_≅ₘ_ to _≅_        ; _≲ₘ_ to _≲_ ; 
                                                   zeroₘ to zero      ; _+ₘ_ to _+_ ; 
                                                   eqₘ to eq          ; sidl to +idl ; 
                                                   sidr to +idr       ; sassoc to +assoc ;
                                                   maxₘ to max        ; porderₘ to porder ;
                                                   midr to maxidr     ; midl to maxidl ;
                                                   scomp≲ₘ to scomp≲  ; mcomp≲ₘ to mcomp≲ ;
                                                   mcomm to maxcomm   ;
                                                   massoc to maxassoc ; ichange to interchange) 
       open IsEquivalence eq renaming (refl to reflₛ ; trans to transₛ ; sym to symₛ)
       open IsPartialOrder porder renaming (isPreorder to preorderₛ ; antisym to antisymₛ 
                                          ; refl to preflₛ ; trans to ptransₛ)

       _F≈_ : ∀ {A : Set} → F S A → F S A → Set
       _F≈_ (n , a) (m , a') = (n ≅ m) × a ≡ a'

       eqF≈ : ∀ {A} → IsEquivalence (_F≈_ {A})
       eqF≈ = record { refl = reflₛ , refl ; 
                       sym = λ {(n≅m , a≡b) → (symₛ n≅m) , sym a≡b} ; 
                       trans = λ {(n≅m , a≡b) (m≅o , b≡c) → transₛ n≅m m≅o , trans a≡b b≡c}
              }       
              
       _F≤_ : ∀ {A : Set} → F S A → F S A → Set
       _F≤_ (n , a) (m , a') = n ≲ m × a ≡ a'

       porderF≤ : ∀ {A} → IsPartialOrder (_F≈_ {A}) (_F≤_ {A})
       porderF≤ = record 
                  { isPreorder = 
                     record { isEquivalence = eqF≈ 
                            ; reflexive = λ {(n≤m , a≡b) → IsPreorder.reflexive preorderₛ n≤m , a≡b} 
                            ; trans = λ {(n≤m , a≡b) (m≤o , b≡c) → (IsPreorder.trans preorderₛ n≤m m≤o) , trans a≡b b≡c} } 
                  ; antisym = λ {(n≤m , a≡b) (m≤n , b≡a) → antisymₛ n≤m m≤n , a≡b} 
                  }

       η : ∀ {A : Set} → A → F S A
       η x = (zero , x)

       ext : ∀ {A B : Set} → F S B → (B → F S A) → F S A
       ext (n , b) f with f b
       ...              | m , a = (n + m) , a

       ext-comp : ∀ {A B : Set} → (a₁ a₂ : F S A) (f₁ f₂ : A → F S B) → 
                     a₁ F≤ a₂ → (∀ (a : A) → f₁ a F≤ f₂ a) → ext a₁ f₁ F≤ ext a₂ f₂ 
       ext-comp (fa₁ , sa₁) (fa₂ , .sa₁) f₁ f₂ (fst≤ , refl) f≤ = 
              scomp≲ fa₁ (proj₁ (f₁ sa₁)) fa₂ (proj₁ (f₂ sa₁)) fst≤ (proj₁ (f≤ sa₁)) , proj₂ (f≤ sa₁) 

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

       mult-comp : ∀ {A B : Set} → (a₁ a₂ : F S A) (b₁ b₂ : F S B) → 
                     a₁ F≤ a₂ → b₁ F≤ b₂ → mult a₁ b₁ F≤ mult a₂ b₂ 
       mult-comp (fa₁ , sa₁) (fa₂ , .sa₁) (fb₁ , sb₁) (fb₂ , .sb₁) (fa≤ , refl) (fb≤ , refl) 
                     = (mcomp≲ fa₁ fb₁ fa₂ fb₂ fa≤ fb≤) , refl

       mult-left : {A : Set} (a : F S A) →
              mult a unit F≈ ext a (λ a₁ → η (a₁ , tt))
       mult-left a = transₛ (maxidr _) (symₛ (+idr _)) , refl

       mult-right : {B : Set} (b : F S B) →
              mult unit b F≈ ext b (λ b₁ → η (tt , b₁))
       mult-right (n , a) = transₛ (maxidl n) (symₛ (+idr n)) , refl  

       mult-assoc : {A B C : Set} (a : F S A) (b : F S B) (c : F S C) →
              ext (mult (mult a b) c) (λ { ((a , b) , c) → η (a , b , c) }) F≈ mult a (mult b c)
       mult-assoc (n , a) (m , b) (o , c) = transₛ (+idr (max (max n m) o)) (maxassoc n m o) , refl

       mult-comm : {A B : Set} → (a : F S A) → (b : F S B) 
                     → mult a b F≈ ext (mult b a) (λ { (a , b) → zeroₘ cmonoid , b , a})
       mult-comm (n , a) (m , b) = transₛ (maxcomm n m) (symₛ (+idr (max m n))) , refl

       ichg : {A B C D : Set} (a : F S A) (b : F S B) (f : A → F S C) (g : B → F S D) →
              mult (ext a f) (ext b g) F≤ ext (mult a b) (λ { (a , b) → mult (f a) (g b) })
       ichg (n , a) (m , b) f g with f a     | g b
       ...                         | (o , c) | (p , d) = (interchange n o m p) , refl



cmonoid⇒cmonad : {S : Set} → ConcurrentMonoid S → ConcurrentMonad (F S)
cmonoid⇒cmonad {S} cmonoid
              = makeConcurrentMonad
                    (_F≈_       {S} {cmonoid})
                    (eqF≈       {S} {cmonoid})
                    (_F≤_       {S} {cmonoid})
                    (porderF≤   {S} {cmonoid})
                    (η          {S} {cmonoid})
                    (ext        {S} {cmonoid})
                    (ext-comp   {S} {cmonoid})
                    (ext-left   {S} {cmonoid}) 
                    (ext-right  {S} {cmonoid}) 
                    (ext-assoc  {S} {cmonoid}) 
                    (unit       {S} {cmonoid}) 
                    (mult       {S} {cmonoid}) 
                    (mult-comp  {S} {cmonoid})
                    (mult-left  {S} {cmonoid}) 
                    (mult-right {S} {cmonoid}) 
                    (mult-assoc {S} {cmonoid}) 
                    (mult-comm  {S} {cmonoid})       
                    (ichg       {S} {cmonoid})