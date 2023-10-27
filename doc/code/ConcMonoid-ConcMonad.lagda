\begin{code} 

module ConcMonoid-ConcMonad where 

open import Structures.ConcurrentMonoid
open import Structures.ConcurrentMonad using (ConcurrentMonad ; makeConcurrentMonad)

open import Relation.Binary.PropositionalEquality renaming (refl to prefl ; sym to psym ; trans to ptrans)
open import Relation.Binary
open import Data.Product
open import Data.Unit 
\end{code}

%<*funtor>
\begin{code}
F : Set → Set → Set
F S X = S × X
\end{code}
%</funtor>

%<*module>
\begin{code}
module _ {S : Set} {cmonoid : ConcurrentMonoid S} where 

  open ConcurrentMonoid {S} cmonoid 
    renaming (_≅ₘ_ to _≅_ ; _≲ₘ_ to _≲_ ; zeroₘ to zero ; _+ₘ_ to _+_)       
    renaming (eqₘ to eq ; sidl to +idl ; sidr to +idr ; sassoc to +assoc)
    renaming (maxₘ to max ; porderₘ to porder ; midr to maxidr ; midl to maxidl)     
    renaming (scomp≲ₘ to scomp≲ ; mcomp≲ₘ to mcomp≲ ; mcomm to maxcomm)
    renaming (massoc to maxassoc ; ichange to interchange) 

  open IsEquivalence eq renaming (refl to reflₛ ; trans to transₛ ; sym to symₛ)
  
  open IsPartialOrder porder renaming (isPreorder to preorderₛ ; antisym to antisymₛ)
  
  open IsPreorder preorderₛ renaming (reflexive to ≤reflₛ ; trans to ≤transₛ) 
\end{code}
%</module> 

%<*eq>
\begin{code}
  _F≈_ : ∀ {A : Set} → F S A → F S A → Set
  _F≈_ (n , a) (m , a') = (n ≅ m) × a ≡ a'

  eqF≈ : ∀ {A} → IsEquivalence (_F≈_ {A})
  eqF≈ = record { refl = reflₛ , prefl ; 
                  sym = λ {(n≅m , a≡b) → (symₛ n≅m) , psym a≡b} ; 
                  trans = λ {(n≅m , a≡b) (m≅o , b≡c) 
                             → transₛ n≅m m≅o , ptrans a≡b b≡c}
         }       
\end{code}
%</eq>

%<*orden>
\begin{code}
  _F≤_ : ∀ {A : Set} → F S A → F S A → Set
  _F≤_ (n , a) (m , a') = n ≲ m × a ≡ a'
  
  porderF≤ : ∀ {A} → IsPartialOrder (_F≈_ {A}) (_F≤_ {A})
  porderF≤ = record 
             { isPreorder = 
               record { isEquivalence = eqF≈ 
                      ; reflexive = λ {(n≤m , a≡b) → ≤reflₛ n≤m , a≡b} 
                      ; trans = λ {(n≤m , a≡b) (m≤o , b≡c) 
                                      → (≤transₛ n≤m m≤o) , ptrans a≡b b≡c} } 
             ; antisym = λ {(n≤m , a≡b) (m≤n , b≡a) → antisymₛ n≤m m≤n , a≡b} 
             }
\end{code}
%</orden>

%<*monad>
\begin{code}
  return : ∀ {A : Set} → A → F S A
  return x = (zero , x)

  bind : ∀ {A B : Set} → F S A → (A → F S B) → F S B
  bind (n , a) f with f a
  ...             | m , b = (n + m) , b
\end{code}
%</monad>

%<*bindcomp>
\begin{code}
  bind-comp : ∀ {A B : Set} → (x₁ x₂ : F S A) (f₁ f₂ : A → F S B) → 
              x₁ F≤ x₂ → (∀ (a : A) → f₁ a F≤ f₂ a) → bind x₁ f₁ F≤ bind x₂ f₂ 
  bind-comp (n₁ , a₁) (n₂ , .a₁) f₁ f₂ (fst≤ , prefl) f≤ = 
         scomp≲ n₁ (proj₁ (f₁ a₁)) n₂ (proj₁ (f₂ a₁)) fst≤ (proj₁ (f≤ a₁)) , proj₂ (f≤ a₁) 
\end{code}
%</bindcomp>

%<*monadprops>
\begin{code}
  bind-left : ∀ {A B : Set} → (x : B) (f : B → F S A) → bind (return x) f F≈ f x
  bind-left x f with f x 
  ...             | m , a = +idl m , prefl

  bind-right : ∀ {A : Set} → (t : F S A) → bind t return F≈ t
  bind-right (n , a) = +idr n , prefl
  
  bind-assoc : ∀ {A B C : Set} (t : F S C) (f : C → F S B) (g : B → F S A) →
              bind (bind t f) g F≈ bind t (λ x → bind (f x) g)
  bind-assoc (n , c) f g  with f c
  ...                     | (m , b)  with g b
  ...                                | (o , a) = symₛ (+assoc n m o) , prefl
\end{code}
%</monadprops>

%<*monoidal>
\begin{code}
  unit : F S ⊤ 
  unit = return tt

  merge : {A B : Set} → F S A → F S B → F S (A × B)
  merge (n , a) (m , b) = max n m , a , b
\end{code}
%</monoidal>

%<*mergecomp>
\begin{code}
  merge-comp : ∀ {A B : Set} → (x₁ x₂ : F S A) (y₁ y₂ : F S B) → x₁ F≤ x₂ → y₁ F≤ y₂ 
              → merge x₁ y₁ F≤ merge x₂ y₂ 
  merge-comp (n₁ , a₁) (n₂ , .a₁) (m₁ , b₁) (m₂ , .b₁) (n≤ , prefl) (m≤ , prefl) 
              = (mcomp≲ n₁ m₁ n₂ m₂ n≤ m≤) , prefl
\end{code}
%</mergecomp>

%<*monoidalprops>
\begin{code}
  merge-left : {A : Set} (a : F S A) → merge a unit F≈ bind a (λ a₁ → return (a₁ , tt))
  merge-left a = transₛ (maxidr _) (symₛ (+idr _)) , prefl

  merge-right : {B : Set} (b : F S B) → merge unit b F≈ bind b (λ b₁ → return (tt , b₁))
  merge-right (n , a) = transₛ (maxidl n) (symₛ (+idr n)) , prefl  
  
  merge-assoc : {A B C : Set} (a : F S A) (b : F S B) (c : F S C) →
               bind (merge (merge a b) c) (λ { ((a , b) , c) → return (a , b , c) }) 
                                                              F≈ merge a (merge b c)
  merge-assoc (n , a) (m , b) (o , c) = 
             transₛ (+idr (max (max n m) o)) (maxassoc n m o) , prefl
\end{code}
%</monoidalprops>

%<*mergecomm>
\begin{code}
  merge-comm : {A B : Set} → (a : F S A) → (b : F S B) 
              → merge a b F≈ bind (merge b a) (λ { (a , b) → zeroₘ cmonoid , b , a})
  merge-comm (n , a) (m , b) = transₛ (maxcomm n m) (symₛ (+idr (max m n))) , prefl
\end{code}
%</mergecomm>

%<*ichange>
\begin{code}
  ichg : {A B C D : Set} (a : F S A) (b : F S B) (f : A → F S C) (g : B → F S D) →
      merge (bind a f) (bind b g) F≤ bind (merge a b) (λ { (a , b) → merge (f a) (g b) })
  ichg (n , a) (m , b) f g  with  f a      | g b
  ...                       |     (o , c)  | (p , d) = (interchange n o m p) , prefl
\end{code}
%</ichange>

%<*proof>
\begin{code}
cmonoid⇒cmonad : {S : Set} → ConcurrentMonoid S → ConcurrentMonad (F S)
cmonoid⇒cmonad {S} cmonoid
              = makeConcurrentMonad
                    (_F≈_         {S} {cmonoid})
                    (eqF≈         {S} {cmonoid})
                    (_F≤_         {S} {cmonoid})
                    (porderF≤     {S} {cmonoid})
                    (return       {S} {cmonoid})
                    (bind         {S} {cmonoid})
                    (bind-comp    {S} {cmonoid})
                    (bind-left    {S} {cmonoid}) 
                    (bind-right   {S} {cmonoid}) 
                    (bind-assoc   {S} {cmonoid}) 
                    (merge        {S} {cmonoid}) 
                    (merge-comp   {S} {cmonoid})
                    (merge-left   {S} {cmonoid}) 
                    (merge-right  {S} {cmonoid}) 
                    (merge-assoc  {S} {cmonoid}) 
                    (merge-comm   {S} {cmonoid})       
                    (ichg         {S} {cmonoid})
\end{code}
%</proof>