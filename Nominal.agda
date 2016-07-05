
open import Relation.Binary using (Decidable ; REL ; Rel ; DecSetoid)
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
open import Data.List using (List ; [] ; _∷_ ; _++_) renaming ([_] to [_]ᴸ)

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

infix 4 _⊆_
_⊆_ : ∀ {a} {A : Set a} → Rel (List A) a
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

refl⊆ : ∀ {a} {A : Set a} {xs : List A}
      → xs ⊆ xs
refl⊆ i = i

trans⊆ : ∀ {a} {A : Set a} {xs ys zs : List A}
       → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
trans⊆ p q i = q (p i)

⊆++ₗ : ∀ {a} {A : Set a} {xs : List A} (ys : List A)
     → xs ⊆ xs ++ ys
⊆++ₗ ys ₀ = ₀
⊆++ₗ ys (₁₊ i) = ₁₊ (⊆++ₗ ys i)

⊆++ᵣ : ∀ {a} {A : Set a} (xs : List A) {ys : List A}
     → ys ⊆ xs ++ ys
⊆++ᵣ []       i = i
⊆++ᵣ (_ ∷ xs) i = ₁₊ (⊆++ᵣ xs i)

infix 4 _≈ᴸ_
_≈ᴸ_ : ∀ {a} {A : Set a} → Rel (List A) a
xs ≈ᴸ ys = xs ⊆ ys × ys ⊆ xs

Cxˢ : Set
Cxˢ = List Sort

Var : Cxˢ → Set
Var Γ = Σ[ s ∈ Sort ] s ∈ Γ

infix 4 _∈≟_
_∈≟_ : {s : Sort} {Γ : Cxˢ}
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

varDecSetoid : (Γ : Cxˢ) → DecSetoid lz lz
varDecSetoid Γ = record
  { Carrier = Var Γ
  ; _≈_ = _≡_
  ; isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_ = _≟ⱽ_
    }
  }

import Data.Substitution as Substitution
open module Subst (Γ : Cxˢ) = Substitution (varDecSetoid Γ) public

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
  open Perm.Properties public

  domᶜ : Con → Sort
  domᶜ f = proj₁ (arityᶜ f)

  codᶜ : Con → Sort
  codᶜ f = proj₂ (arityᶜ f)
  
  sortⱽ : ∀ {Γ} → Var Γ → Sort
  sortⱽ = proj₁

  infixr 5 _∷_
  infixr 5 _$_
  data Term (Γ : Cxˢ) : Sort → Set where
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
         → (t₁ : Term Γ s₁)
         → (t₂ : Term Γ s₂)
         → Term Γ (s₁ ⊗ s₂)
    _$_  : (f : Con)
         → (t : Term Γ (domᶜ f))
         → Term Γ (codᶜ f)

  infixr 5 _∙_
  _∙_ : ∀ {Γ s} → Permutation → Term Γ s → Term Γ s
  π ∙ atom a = atom (permute π a)
  π ∙ (π₁ · X) = (π ∘ π₁) · X
  π ∙ ([ a ] t) = [ permute π a ] (π ∙ t)
  π ∙ (t ∷ u) = (π ∙ t) ∷ (π ∙ u)
  π ∙ (f $ t) = f $ (π ∙ t)

  Subst : Cxˢ → Set 
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

  Cxᶠ : Cxˢ → Set
  Cxᶠ Γ = List (Atom × Var Γ)

  infix 4 _⊢_#_
  data _⊢_#_ {Γ : Cxˢ} (Δ : Cxᶠ Γ) (a : Atom) : ∀ {s} → Term Γ s → Set where
    #atom : ∀ {b}
          → (a≢b : a ≢ b)
          → Δ ⊢ a # atom b
    #var  : ∀ {π} {X : Var Γ}
          → (i : (permute (π ⁻¹) a , X) ∈ Δ)
          → Δ ⊢ a # π · X
    #abs≡ : ∀ {b s} {t : Term Γ s}
          → (a≡b : a ≡ b)
          → Δ ⊢ a # [ b ] t
    #abs≢ : ∀ {b s} {t : Term Γ s}
          → (a≢b : a ≢ b)
          → (a#t : Δ ⊢ a # t)
          → Δ ⊢ a # [ b ] t
    #∷    : ∀ {s₁ s₂} {Δ₁ Δ₂ : Cxᶠ Γ} {t₁ : Term Γ s₁} {t₂ : Term Γ s₂}
          → (δ₁ : Δ₁ ⊆ Δ)
          → (a#t₁ : Δ₁ ⊢ a # t₁)
          → (δ₂ : Δ₂ ⊆ Δ)
          → (a#t₂ : Δ₂ ⊢ a # t₂)
          → Δ ⊢ a # t₁ ∷ t₂
    #$    : ∀ {f} {t : Term Γ (domᶜ f)}
          → (a#t : Δ ⊢ a # t)
          → Δ ⊢ a # f $ t

  #weaken : ∀ {Γ s a} {Δ Δ' : Cxᶠ Γ} {t : Term Γ s}
          → Δ ⊆ Δ'
          → Δ ⊢ a # t
          → Δ' ⊢ a # t
  #weaken δ (#atom a≢b)          = #atom a≢b
  #weaken δ (#var i)             = #var (δ i)
  #weaken δ (#abs≡ a≡b)          = #abs≡ a≡b
  #weaken δ (#abs≢ a≢b a#t)      = #abs≢ a≢b (#weaken δ a#t)
  #weaken δ (#∷ δ₁ a#t₁ δ₂ a#t₂) = #∷ (trans⊆ δ₁ δ) a#t₁ (trans⊆ δ₂ δ) a#t₂
  #weaken δ (#$ a#t)             = #$ (#weaken δ a#t)

  infix 4 _#_
  _#_ : ∀ {Γ s} → REL Atom (Term Γ s) lz
  _#_ {Γ} a t = Σ[ Δ ∈ Cxᶠ Γ ] Δ ⊢ a # t

  infix 4 _#?_
  _#?_ : ∀ {Γ s} → Decidable (_#_ {Γ} {s})
  a #? atom b with a ≟ᴬ b
  ...| yes a≡b                           = no λ { (_ , #atom a≢b) → a≢b a≡b }
  ...| no  a≢b                           = yes ([] , #atom a≢b)
  a #? (π · X)                           = yes ([ permute (π ⁻¹) a , X ]ᴸ , #var ₀)
  a #? ([ b ] t) with a ≟ᴬ b
  ...| yes a≡b                           = yes ([] , #abs≡ a≡b)
  ...| no  a≢b with a #? t
  ...| yes (Δ , a#t)                     = yes (Δ , #abs≢ a≢b a#t)
  ...| no ¬a#t                           = no λ { (Δ , #abs≡ a≡b)   → a≢b a≡b
                                                ; (Δ , #abs≢ _ a#t) → ¬a#t (Δ , a#t)
                                                }
  a #? t₁ ∷ t₂ with a #? t₁ | a #? t₂
  ...| yes (Δ₁ , a#t₁) | yes (Δ₂ , a#t₂) = yes (Δ₁ ++ Δ₂ , #∷ (⊆++ₗ Δ₂) a#t₁ (⊆++ᵣ Δ₁) a#t₂)
  ...| _               | no ¬a#t₂        = no λ { (Δ , #∷ {Δ₂ = Δ₂} _ _    _ a#t₂) → ¬a#t₂ (Δ₂ , a#t₂) }
  ...| no ¬a#t₁        | _               = no λ { (Δ , #∷ {Δ₁ = Δ₁} _ a#t₁ _ _   ) → ¬a#t₁ (Δ₁ , a#t₁) }
  a #? f $ t with a #? t
  ...| yes (Δ , a#t)                     = yes (Δ , #$ a#t)
  ...| no ¬a#t                           = no λ { (Δ , #$ a#t) → ¬a#t (Δ , a#t) }

  -- Lemma 2.23 : freshness strengthening

  -- Lemma 2.24 : permutation respects freshness

  #permute : ∀ {Γ s a} {Δ : Cxᶠ Γ} {t : Term Γ s}
           → (π : Permutation)
           → Δ ⊢ a # t
           → Δ ⊢ permute π a # π ∙ t
  #permute π (#atom a≉b)          = #atom λ πa≈πb → a≉b (permute-injective π πa≈πb)
  #permute π (#abs≡ a≈b)          = #abs≡ (cong (permute π) a≈b)
  #permute π (#abs≢ a≉b a#t)      = #abs≢ (λ πa≈πb → a≉b (permute-injective π πa≈πb)) (#permute π a#t)
  #permute π (#∷ δ₁ a#t₁ δ₂ a#t₂) = #∷ δ₁ (#permute π a#t₁) δ₂ (#permute π a#t₂)
  #permute π (#$ a#t)             = #$ (#permute π a#t)
  #permute {a = a} {Δ} π (#var {π = π'} {X = X} i)     = #var
    ( subst (λ x → (x , proj₁ X , proj₂ X) ∈ Δ)
      ( trans
        (sym
          (trans (cong (λ π → permute π a)
            (trans (cong (λ π'' → π'' ∘ π) (∘⁻¹ π π'))
              (∘assoc (π' ⁻¹) (π ⁻¹) π)))
              (trans (∘permute (π' ⁻¹) ((π ⁻¹) ∘ π) a)
                (cong-permute (π' ⁻¹)
                  (permute⁻¹∘ π a)))))
        (∘permute ((π ∘ π') ⁻¹) π a)
      ) i
    )

  open PropEq.≡-Reasoning

  ∘∙ : ∀ {Γ s} π₁ π₂ (t : Term Γ s) → (π₁ ∘ π₂) ∙ t ≡ π₁ ∙ π₂ ∙ t
  ∘∙ π₁ π₂ (atom a)  = cong atom (∘permute π₁ π₂ a)
  ∘∙ π₁ π₂ (π · X)   = cong (λ π → π · X) (∘assoc π₁ π₂ π)
  ∘∙ π₁ π₂ ([ a ] t) = cong₂ [_]_ (∘permute π₁ π₂ a) (∘∙ π₁ π₂ t)
  ∘∙ π₁ π₂ (t₁ ∷ t₂) = cong₂ _∷_ (∘∙ π₁ π₂ t₁) (∘∙ π₁ π₂ t₂)
  ∘∙ π₁ π₂ (f $ t)   = cong (λ t → f $ t) (∘∙ π₁ π₂ t)

  ∙substVar : ∀ {Γ} π π' (X : Var Γ) (σ : Subst Γ) → π ∙ substVar π' X σ ≡ substVar (π ∘ π') X σ
  ∙substVar {Γ} π π' X σ with substitute Γ X σ
  ...| just (Y , X≡Y , val) = sym (∘∙ π π' _)
  ...| nothing              = refl

  ∙distrib⟨⟩ : ∀ {Γ s} π (σ : Subst Γ) (t : Term Γ s) → π ∙ t ⟨ σ ⟩ ≡ (π ∙ t) ⟨ σ ⟩
  ∙distrib⟨⟩ π σ (atom a)  = refl
  ∙distrib⟨⟩ π σ (π' · X)  = ∙substVar π π' X σ
  ∙distrib⟨⟩ π σ ([ a ] t) = cong (λ t → [ permute π a ] t) (∙distrib⟨⟩ π σ t)
  ∙distrib⟨⟩ π σ (t₁ ∷ t₂) = cong₂ _∷_ (∙distrib⟨⟩ π σ t₁) (∙distrib⟨⟩ π σ t₂)
  ∙distrib⟨⟩ π σ (f $ t)   = cong (λ t → f $ t) (∙distrib⟨⟩ π σ t)
