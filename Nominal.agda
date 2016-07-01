
open import Relation.Binary using (Decidable ; Rel ; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to ≡[_])

module Nominal
  -- (Var : Set)
  -- (_≟ⱽ_ : Decidable (_≡_ {A = Var}))
  where

open import Level renaming (zero to lz ; suc to ls)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Data.Product using (Σ ; _,_ ; _×_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin) renaming (zero to fz ; suc to fs)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.List using (List ; [] ; _∷_)

Σ≡ : ∀ {a b} {A : Set a} {B : A → Set b}
   → {x y : A} → (p : x ≡ y)
   → {bx : B x} {by : B y} → subst B p bx ≡ by
   → (x , bx) ≡ (y , by)
Σ≡ refl refl = refl

proj₂-injective : ∀ {a b} {A : Set a} {B : A → Set b}
                → {x y : Σ A B} → (p : x ≡ y)
                → (q : proj₁ x ≡ proj₁ y)
                → subst B q (proj₂ x) ≡ proj₂ y
proj₂-injective refl refl = refl

infixr 6 _⊗_
data Sort : Set where
  𝕋    : Sort
  [𝔸]_ : Sort → Sort
  _⊗_  : Sort → Sort → Sort

[𝔸]-injective : ∀ {s₁ s₂}
              → [𝔸] s₁ ≡ [𝔸] s₂
              → s₁ ≡ s₂
[𝔸]-injective refl = refl

⊗-injective : ∀ {s₁ s₂ s₃ s₄}
            → s₁ ⊗ s₃ ≡ s₂ ⊗ s₄
            → s₁ ≡ s₂ × s₃ ≡ s₄
⊗-injective refl = refl , refl

_≟ˢ_ : Decidable (_≡_ {A = Sort})
𝕋 ≟ˢ 𝕋 = yes refl
𝕋 ≟ˢ ([𝔸] s₂) = no λ ()
𝕋 ≟ˢ (s₂ ⊗ s₃) = no λ ()
([𝔸] s₁) ≟ˢ ([𝔸] s₂) with s₁ ≟ˢ s₂
...| yes eq = yes (cong [𝔸]_ eq)
...| no neq = no (λ eq → neq ([𝔸]-injective eq))
([𝔸] s₁) ≟ˢ 𝕋 = no λ ()
([𝔸] s₁) ≟ˢ (s₂ ⊗ s₃) = no λ ()
(s₁ ⊗ s₂) ≟ˢ (s₃ ⊗ s₄) with s₁ ≟ˢ s₃ | s₂ ≟ˢ s₄
...| yes eq₁ | yes eq₂ = yes (cong₂ _⊗_ eq₁ eq₂)
...| _       | no neq₂ = no (λ eq → neq₂ (proj₂ (⊗-injective eq)))
...| no neq₁ | _       = no (λ eq → neq₁ (proj₁ (⊗-injective eq)))
(s₁ ⊗ s₂) ≟ˢ 𝕋 = no λ ()
(s₁ ⊗ s₂) ≟ˢ ([𝔸] s₃) = no λ ()

infix 4 _∈_
data _∈_ {a} {A : Set a} (x : A) : List A → Set where
  ₀   : ∀ {Γ}
      → x ∈ x ∷ Γ
  ₁₊_ : ∀ {y Γ}
      → x ∈ Γ
      → x ∈ y ∷ Γ

₁₊injective : ∀ {a} {A : Set a} {x y : A} {Γ : List A}
            → {p q : x ∈ Γ}
            → ₁₊_ {y = y} p ≡ ₁₊ q
            → p ≡ q
₁₊injective refl = refl

₁ : ∀ {a} {A : Set a} {x y : A} {Γ : List A}
  → x ∈ y ∷ x ∷ Γ
₁ = ₁₊ ₀ 

₂ : ∀ {a} {A : Set a} {x y z : A} {Γ : List A}
  → x ∈ z ∷ y ∷ x ∷ Γ
₂ = ₁₊ ₁₊ ₀ 

₃ : ∀ {a} {A : Set a} {x y z w : A} {Γ : List A}
  → x ∈ w ∷ z ∷ y ∷ x ∷ Γ
₃ = ₁₊ ₁₊ ₁₊ ₀ 

Cx : Set
Cx = List Sort

Var : Cx → Set
Var Γ = Σ[ s ∈ Sort ] s ∈ Γ

infix 4 _∈≟_
_∈≟_ : {s : Sort} {Γ : Cx}
     → Decidable (_≡_ {A = s ∈ Γ})
₀ ∈≟ ₀ = yes refl
₀ ∈≟ (₁₊ q) = no λ ()
(₁₊ p) ∈≟ ₀ = no λ ()
(₁₊ p) ∈≟ (₁₊ q) with p ∈≟ q
...| yes p≡q = yes (cong ₁₊_ p≡q)
...| no  p≢q = no λ prf → p≢q (₁₊injective prf)

infix 4 _≟ⱽ_
_≟ⱽ_ : ∀ {Γ} → Decidable (_≡_ {A = Var Γ})
(s₁ , p) ≟ⱽ (s₂ , q) with s₁ ≟ˢ s₂
...| no neq = no λ eq → neq (cong proj₁ eq)
...| yes eq with subst (λ s → s ∈ _) eq p ∈≟ q
...| yes eq' = yes (Σ≡ eq eq')
...| no neq' = no (λ eq' → neq' (proj₂-injective eq' eq))

varDecSetoid : (Γ : Cx) → DecSetoid lz lz
varDecSetoid Γ = record
  { Carrier = Var Γ
  ; _≈_ = _≡_
  ; isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_ = _≟ⱽ_
    }
  }

import Data.Substitution as Substitution
open module Subst (Γ : Cx) = Substitution (varDecSetoid Γ) public

Arity : Set
Arity = Sort × Sort

module Terms
  (Atom : Set)
  (_≟ᴬ_ : Decidable (_≡_ {A = Atom}))
  (Con   : Set)
  (_≟ᶜ_  : Decidable (_≡_ {A = Con}))
  (arityᶜ : Con → Arity)
  where
  open import Data.Permutation (PropEq.decSetoid _≟ᴬ_) as Perm public

  domᶜ : Con → Sort
  domᶜ f = proj₁ (arityᶜ f)

  codᶜ : Con → Sort
  codᶜ f = proj₂ (arityᶜ f)
  
  sortⱽ : ∀ {Γ} → Var Γ → Sort
  sortⱽ = proj₁

  infixr 5 _∷_
  infixr 5 _$_
  data Term (Γ : Cx) : Sort → Set where
    atom : (a : Atom)
         → Term Γ 𝕋
    _·_  : (π : Permutation)
         → (X : Var Γ)
         → Term Γ (sortⱽ X)
    [_]_ : ∀ {s}
         → (a : Atom)
         → (t : Term Γ s)
         → Term Γ ([𝔸] s)
    _∷_  : ∀ {s₁ s₂}
         → Term Γ s₁
         → Term Γ s₂
         → Term Γ (s₁ ⊗ s₂)
    _$_  : (f : Con)
         → Term Γ (domᶜ f)
         → Term Γ (codᶜ f)

  infixr 5 _∙_
  _∙_ : ∀ {Γ s} → Permutation → Term Γ s → Term Γ s
  π ∙ atom a = atom (permute π a)
  π ∙ (π₁ · X) = (π ∘ π₁) · X
  π ∙ ([ a ] t) = [ permute π a ] (π ∙ t)
  π ∙ (t ∷ u) = (π ∙ t) ∷ (π ∙ u)
  π ∙ (f $ t) = f $ (π ∙ t)

  Subst : Cx → Set 
  Subst Γ = Substitution Γ (λ X → Term Γ (sortⱽ X))

  substVar : ∀ {Γ} → Permutation → (X : Var Γ) → Subst Γ → Term Γ (sortⱽ X)
  substVar {Γ} π X σ with substitute Γ X σ
  ...| just (Y , X≡Y , val) = π ∙ subst (λ x → Term Γ (proj₁ x)) (sym X≡Y) val
  ...| nothing              = π · X

  infixl 6 _⟨_⟩
  _⟨_⟩ : ∀ {Γ s} → Term Γ s → Subst Γ → Term Γ s
  atom a ⟨ σ ⟩    = atom a
  (π · X) ⟨ σ ⟩   = substVar π X σ
  ([ a ] t) ⟨ σ ⟩ = [ a ] (t ⟨ σ ⟩)
  (t ∷ u) ⟨ σ ⟩   = (t ⟨ σ ⟩) ∷ (u ⟨ σ ⟩)
  (f $ t) ⟨ σ ⟩   = f $ (t ⟨ σ ⟩)

{-
  ∙∘ : ∀ {τ} π₁ π₂ (t : Term τ) → (π₁ ∘ π₂) ∙ t ≈ᵗ π₁ ∙ π₂ ∙ t
  ∙∘ π₁ π₂ (atom a)   = ≈atom (∘permute π₁ π₂ a)
  ∙∘ π₁ π₂ (π · X)    = {!!}
    where
    π∘ : (π₁ ∘ π₂) ∘ π ≡ π₁ ∘ π₂ ∘ π
    π∘ = ∘assoc π₁ π₂ π
  ∙∘ π₁ π₂ ([ a ] t)  = ≈[ ∘permute π₁ π₂ a ] ∙∘ π₁ π₂ t
  ∙∘ π₁ π₂ (f $ args) = {!!}

  permute-distrib-substitute : ∀ {τ} π σ (t : Term τ) → π ∙ t ⟨ σ ⟩ ≡ (π ∙ t) ⟨ σ ⟩
  permute-distrib-substitute π σ (atom a)   = ≡refl
  permute-distrib-substitute π σ (π' · X)   with substitute X σ
  ...| just (Y , X≈Y , val) = {!!}
  ...| nothing              = {!!}
  permute-distrib-substitute π σ ([ a ] t)  = {!!}
  permute-distrib-substitute π σ (f $ args) = {!!}
  -}
