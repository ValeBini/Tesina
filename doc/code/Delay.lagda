\begin{code}
module Delay where 

open import Data.Bool.Base using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod hiding (map)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Binary as B hiding (Rel)
import Relation.Binary.Properties.Setoid as SetoidProperties
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Negation
open import Codata.Musical.Notation

private
  variable
    A B C : Set
\end{code}

%<*bottom>
\begin{code}
data _⊥ (A : Set) : Set where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥
\end{code}
%</bottom>

%<*never>
\begin{code}
never : A ⊥
never = later (♯ never)
\end{code}
%</never>

%<*kind>
\begin{code}
data OtherKind : Set where
  geq weak : OtherKind

data Kind : Set where
  strong : Kind
  other  : (k : OtherKind) → Kind
\end{code}
%</kind>

%<*deckind>
\begin{code}
infix 4 _≟-Kind_

_≟-Kind_ : Decidable (_≡_ {A = Kind})
_≟-Kind_ strong        strong        = yes P.refl
_≟-Kind_ strong        (other k)     = no λ()
_≟-Kind_ (other k)     strong        = no λ()
_≟-Kind_ (other geq)   (other geq)   = yes P.refl
_≟-Kind_ (other geq)   (other weak)  = no λ()
_≟-Kind_ (other weak)  (other geq)   = no λ()
_≟-Kind_ (other weak)  (other weak)  = yes P.refl
\end{code}
%</deckind>

%<*equality>
\begin{code}
Equality : Kind → Set
Equality k = False (k ≟-Kind other geq)
\end{code}
%</equality>

%<*modequality>
\begin{code}
module Equality {A : Set} -- The "return type".
                (_∼_ : A → A → Set) where

  -- The three relations.

  data Rel : Kind → A ⊥ → A ⊥ → Set where
    now     : ∀ {k x y}  (x∼y : x ∼ y)                     → Rel k (now x) (now y)
    later   : ∀ {k x y}  (x∼y : ∞ (Rel k (♭ x) (♭ y)))     → Rel k (later x) (later y)
    laterʳ  : ∀ {x y}    (x≈y : Rel (other weak) x (♭ y))  → Rel (other weak) x  (later y)
    laterˡ  : ∀ {k x y}  (x∼y : Rel (other k) (♭ x) y)     → Rel (other k) (later x) y

  infix 4 _≅_ _≳_ _≲_ _≈_

  _≅_ : A ⊥ → A ⊥ → Set _
  _≅_ = Rel strong

  _≳_ : A ⊥ → A ⊥ → Set _
  _≳_ = Rel (other geq)

  _≲_ : A ⊥ → A ⊥ → Set _
  _≲_ = flip _≳_

  _≈_ : A ⊥ → A ⊥ → Set _
  _≈_ = Rel (other weak)

  -- x ⇓ y means that x terminates with y.

  infix 4 _⇓[_]_ _⇓_

  _⇓[_]_ : A ⊥ → Kind → A → Set _
  x ⇓[ k ] y = Rel k x (now y)

  _⇓_ : A ⊥ → A → Set _
  x ⇓ y = x ⇓[ other weak ] y

  -- x ⇓ means that x terminates.

  infix 4 _⇓

  _⇓ : A ⊥ → Set _
  x ⇓ = ∃ λ v → x ⇓ v

  -- x ⇑ means that x does not terminate.

  infix 4 _⇑[_] _⇑

  _⇑[_] : A ⊥ → Kind → Set _
  x ⇑[ k ] = Rel k x never

  _⇑ : A ⊥ → Set _
  x ⇑ = x ⇑[ other weak ]
\end{code}
%</modequality>

%<*lemas>
\begin{code}
module _ {A : Set} {_∼_ : A → A → Set} where

  open Equality _∼_ using (Rel; _≅_; _≳_; _≲_; _≈_; _⇓[_]_; _⇑[_])
  open Equality.Rel

  -- All relations include strong equality.

  ≅⇒ : ∀ {k} {x y : A ⊥} → x ≅ y → Rel k x y
  ≅⇒ (now x∼y)    = now x∼y
  ≅⇒ (later x≅y)  = later (♯ ≅⇒ (♭ x≅y))

  -- The weak equality includes the ordering.

  ≳⇒ : ∀ {k} {x y : A ⊥} → x ≳ y → Rel (other k) x y
  ≳⇒ (now x∼y)     = now x∼y
  ≳⇒ (later  x≳y)  = later (♯ ≳⇒ (♭ x≳y))
  ≳⇒ (laterˡ x≳y)  = laterˡ  (≳⇒    x≳y )

  -- Weak equality includes the other relations.

  ⇒≈ : ∀ {k} {x y : A ⊥} → Rel k x y → x ≈ y
  ⇒≈ {strong}      = ≅⇒
  ⇒≈ {other geq}   = ≳⇒
  ⇒≈ {other weak}  = id

  -- The relations agree for non-terminating computations.

  never⇒never : ∀ {k₁ k₂} {x : A ⊥} →
                Rel k₁ x never → Rel k₂ x never
  never⇒never (later  x∼never)  = later (♯ never⇒never (♭ x∼never))
  never⇒never (laterʳ x≈never)  = never⇒never x≈never
  never⇒never (laterˡ x∼never)  = later (♯ never⇒never x∼never)

  -- The "other" relations agree when the right-hand side is a value.

  now⇒now : ∀ {k₁ k₂} {x} {y : A} →
            Rel (other k₁) x (now y) → Rel (other k₂) x (now y)
  now⇒now (now x∼y)       = now x∼y
  now⇒now (laterˡ x∼now)  = laterˡ (now⇒now x∼now)

------------------------------------------------------------------------
-- Later can be dropped

  laterʳ⁻¹ : ∀ {k} {x : A ⊥} {y} →
             Rel (other k) x (later y) → Rel (other k) x (♭ y)
  laterʳ⁻¹ (later  x∼y)   = laterˡ (♭ x∼y)
  laterʳ⁻¹ (laterʳ x≈y)   = x≈y
  laterʳ⁻¹ (laterˡ x∼ly)  = laterˡ (laterʳ⁻¹ x∼ly)

  laterˡ⁻¹ : ∀ {x} {y : A ⊥} → later x ≈ y → ♭ x ≈ y
  laterˡ⁻¹ (later  x≈y)   = laterʳ (♭ x≈y)
  laterˡ⁻¹ (laterʳ lx≈y)  = laterʳ (laterˡ⁻¹ lx≈y)
  laterˡ⁻¹ (laterˡ x≈y)   = x≈y

  later⁻¹ : ∀ {k} {x y : ∞ (A ⊥)} →
            Rel k (later x) (later y) → Rel k (♭ x) (♭ y)
  later⁻¹ (later  x∼y)   = ♭ x∼y
  later⁻¹ (laterʳ lx≈y)  = laterˡ⁻¹ lx≈y
  later⁻¹ (laterˡ x∼ly)  = laterʳ⁻¹ x∼ly

------------------------------------------------------------------------
-- The relations are equivalences or partial orders, given suitable
-- assumptions about the underlying relation

  module Equivalence where

    -- Reflexivity.

    refl : Reflexive _∼_ → ∀ {k} → Reflexive (Rel k)
    refl refl-∼ {x = now v}    = now refl-∼
    refl refl-∼ {x = later x}  = later (♯ refl refl-∼)

    -- Symmetry.

    sym : Symmetric _∼_ → ∀ {k} → Equality k → Symmetric (Rel k)
    sym sym-∼ eq (now x∼y)             = now (sym-∼ x∼y)
    sym sym-∼ eq (later          x∼y)  = later (♯ sym sym-∼ eq (♭ x∼y))
    sym sym-∼ eq (laterʳ         x≈y)  = laterˡ  (sym sym-∼ eq    x≈y )
    sym sym-∼ eq (laterˡ {weak}  x≈y)  = laterʳ  (sym sym-∼ eq    x≈y )

    -- Transitivity.

    private
     module Trans (trans-∼ : Transitive _∼_) where

      now-trans : ∀ {k x y} {v : A} →
                  Rel k x y → Rel k y (now v) → Rel k x (now v)
      now-trans (now x∼y)     (now y∼z)     = now (trans-∼ x∼y y∼z)
      now-trans (laterˡ x∼y)  y∼z           = laterˡ (now-trans x∼y y∼z)
      now-trans x∼ly          (laterˡ y∼z)  = now-trans (laterʳ⁻¹ x∼ly) y∼z

      mutual

        later-trans : ∀ {k} {x y : A ⊥} {z} →
                      Rel k x y → Rel k y (later z) → Rel k x (later z)
        later-trans (later x∼y)   ly∼lz         = later  (♯ trans (♭ x∼y) (later⁻¹  ly∼lz))
        later-trans (laterˡ x∼y)  y∼lz          = later  (♯ trans    x∼y  (laterʳ⁻¹  y∼lz))
        later-trans (laterʳ x≈y)  ly≈lz         = later-trans    x≈y  (laterˡ⁻¹ ly≈lz)
        later-trans x≈y           (laterʳ y≈z)  = laterʳ (  trans    x≈y             y≈z )

        trans : ∀ {k} {x y z : A ⊥} → Rel k x y → Rel k y z → Rel k x z
        trans {z = now v}    x∼y y∼v   = now-trans x∼y y∼v
        trans {z = later z}  x∼y y∼lz  = later-trans x∼y y∼lz

    open Trans public using (trans)

  -- All the relations are preorders.

  preorder : IsPreorder _≡_ _∼_ → Kind → Preorder _ _ _
  preorder pre k = record
    { Carrier    = A ⊥
    ; _≈_        = _≡_
    ; _∼_        = Rel k
    ; isPreorder = record
      { isEquivalence = P.isEquivalence
      ; reflexive     = refl′
      ; trans         = Equivalence.trans (IsPreorder.trans pre)
      }
    }
    where
    refl′ : ∀ {k} {x y : A ⊥} → x ≡ y → Rel k x y
    refl′ P.refl = Equivalence.refl (IsPreorder.refl pre)

  private
    preorder′ : IsEquivalence _∼_ → Kind → Preorder _ _ _
    preorder′ equiv =
      preorder (SetoidProperties.isPreorder (record { isEquivalence = equiv }))

  -- The two equalities are equivalence relations.

  setoid : IsEquivalence _∼_ →
           (k : Kind) {eq : Equality k} → Setoid _ _
  setoid equiv k {eq} = record
    { Carrier        = A ⊥
    ; _≈_            = Rel k
    ; isEquivalence  = record
      { refl   = Pre.refl
      ; sym    = Equivalence.sym (IsEquivalence.sym equiv) eq
      ; trans  = Pre.trans
      }
    } where module Pre = Preorder (preorder′ equiv k)

  -- The order is a partial order, with strong equality as the
  -- underlying equality.

  ≳-poset : IsEquivalence _∼_ → Poset _ _ _
  ≳-poset equiv = record
    { Carrier         = A ⊥
    ; _≈_             = _≅_
    ; _≤_             = _≳_
    ; isPartialOrder  = record
      { antisym     = antisym
      ; isPreorder  = record
        { isEquivalence  = S.isEquivalence
        ; reflexive      = ≅⇒
        ; trans          = Pre.trans
        }
      }
    }
    where
    module S   = Setoid (setoid equiv strong)
    module Pre = Preorder (preorder′ equiv (other geq))

    antisym : {x y : A ⊥} → x ≳ y → x ≲ y → x ≅ y
    antisym (now x∼y)      (now _)        = now x∼y
    antisym (later  x≳y)   (later x≲y)    = later (♯ antisym (♭ x≳y) (♭ x≲y))
    antisym (later  x≳y)   (laterˡ x≲ly)  = later (♯ antisym (♭ x≳y) (laterʳ⁻¹ x≲ly))
    antisym (laterˡ x≳ly)  (later x≲y)    = later (♯ antisym (laterʳ⁻¹ x≳ly) (♭ x≲y))
    antisym (laterˡ x≳ly)  (laterˡ x≲ly)  = later (♯ antisym (laterʳ⁻¹ x≳ly) (laterʳ⁻¹ x≲ly))
\end{code}
%</lemas>