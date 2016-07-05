
open import Relation.Binary using (Decidable ; REL ; Rel ; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to ≡[_])

module Nominal where

open import Level renaming (zero to lz ; suc to ls)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Data.Product using (Σ ; _,_ ; _×_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin) renaming (zero to fz ; suc to fs)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.List using (List ; [] ; _∷_ ; _++_) renaming ([_] to [_]ᴸ)
open import Data.List.All using (All ; [] ; _∷_)
open import Data.Empty using (⊥ ; ⊥-elim)

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

infix 4 _∈_ _∉_ _∈[_-_]
data _∈_ {a} {A : Set a} (x : A) : List A → Set where
  ₀   : ∀ {Γ}
      → x ∈ x ∷ Γ
  ₁₊_ : ∀ {y Γ}
      → x ∈ Γ
      → x ∈ y ∷ Γ

_∉_ : ∀ {a} {A : Set a} (x : A) → List A → Set
x ∉ xs = ¬ (x ∈ xs)

_∈[_-_] : ∀ {a} {A : Set a} (x : A) → List A → List A → Set
x ∈[ xs - ys ] = x ∈ xs × x ∉ ys

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
  open Perm.Properties public

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

  Subst : Cx → Set 
  Subst Γ = Substitution Γ (λ X → Term Γ (sortⱽ X))

  substVar : ∀ {Γ} → (X : Var Γ) → Subst Γ → Term Γ (sortⱽ X)
  substVar {Γ} X σ with substitute Γ X σ
  ...| just (Y , X≡Y , val) = subst (λ x → Term Γ (proj₁ x)) (sym X≡Y) val
  ...| nothing              = id · X

  infixl 6 _⟨_⟩
  _⟨_⟩ : ∀ {Γ s} → Term Γ s → Subst Γ → Term Γ s
  atom a ⟨ σ ⟩    = atom a
  (π · X) ⟨ σ ⟩   = π ∙ substVar X σ
  ([ a ] t) ⟨ σ ⟩ = [ a ] (t ⟨ σ ⟩)
  (t ∷ u) ⟨ σ ⟩   = (t ⟨ σ ⟩) ∷ (u ⟨ σ ⟩)
  (f $ t) ⟨ σ ⟩   = f $ (t ⟨ σ ⟩)

  #Cx : Cx → Set
  #Cx Γ = List (Atom × Var Γ)

  ∉∷ : ∀ {a b} {A : Set a} {B : Set b}
     → {p q : A × B} {ps : List (A × B)}
     → proj₁ p ≢ proj₁ q ⊎ proj₂ p ≢ proj₂ q
     → p ∉ ps
     → p ∉ q ∷ ps
  ∉∷ (inj₁ ¬p) ¬ps ₀ = ¬p refl
  ∉∷ (inj₂ ¬q) ¬ps ₀ = ¬q refl
  ∉∷ ¬p ¬ps   (₁₊ i) = ¬ps i

  infix 4 _∈#?_
  _∈#?_ : ∀ {Γ} (p : Atom × Var Γ) (Δ : #Cx Γ) → Dec (p ∈ Δ)
  p ∈#? []      = no λ ()
  p ∈#? ((b , Y) ∷ Δ) with proj₁ p ≟ᴬ b | proj₂ p ≟ⱽ Y | p ∈#? Δ
  ...| yes a≡b | yes X≡Y | _ = yes (subst (λ q → p ∈ q ∷ Δ) (cong₂ _,_ a≡b X≡Y) ₀)
  ...| _       | no  X≢Y | yes p∈Δ = yes (₁₊ p∈Δ)
  ...| _       | no  X≢Y | no  p∉Δ = no (∉∷ (inj₂ X≢Y) p∉Δ)
  ...| no  a≢b | _       | yes p∈Δ = yes (₁₊ p∈Δ)
  ...| no  a≢b | _       | no  p∉Δ = no (∉∷ (inj₁ a≢b) p∉Δ)

  infix 4 _⊢_#_
  data _⊢_#_ {Γ : Cx} (Δ : #Cx Γ) (a : Atom) : ∀ {s} → Term Γ s → Set where
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
    #∷    : ∀ {s₁ s₂} {t₁ : Term Γ s₁} {t₂ : Term Γ s₂}
          → (a#t₁ : Δ ⊢ a # t₁)
          → (a#t₂ : Δ ⊢ a # t₂)
          → Δ ⊢ a # t₁ ∷ t₂
    #$    : ∀ {f} {t : Term Γ (domᶜ f)}
          → (a#t : Δ ⊢ a # t)
          → Δ ⊢ a # f $ t

  infix 4 _#_
  _#_ : ∀ {Γ s} → REL Atom (Term Γ s) lz
  _#_ {Γ} a t = Σ[ Δ ∈ #Cx Γ ] Δ ⊢ a # t

  _⊢_#?_ : ∀ {Γ s} (Δ : #Cx Γ) (a : Atom) (t : Term Γ s) → Dec (Δ ⊢ a # t)
  Δ ⊢ a #? atom b with a ≟ᴬ b
  ...| yes a≡b = no λ { (#atom a≢b) → a≢b a≡b }
  ...| no  a≢b = yes (#atom a≢b)
  Δ ⊢ a #? (π · X) with (permute (π ⁻¹) a , X) ∈#? Δ
  ...| yes p∈Δ = yes (#var p∈Δ)
  ...| no  p∉Δ = no λ { (#var p∈Δ) → p∉Δ p∈Δ }
  Δ ⊢ a #? ([ b ] t) with a ≟ᴬ b
  ...| yes a≡b = yes (#abs≡ a≡b)
  ...| no  a≢b with Δ ⊢ a #? t
  ...| yes a#t = yes (#abs≢ a≢b a#t)
  ...| no ¬a#t = no λ { (#abs≡ a≡b)     → a≢b a≡b
                      ; (#abs≢ a≢b a#t) → ¬a#t a#t
                      }
  Δ ⊢ a #? (t₁ ∷ t₂) with Δ ⊢ a #? t₁ | Δ ⊢ a #? t₂
  ...| yes a#t₁ | yes a#t₂ = yes (#∷ a#t₁ a#t₂)
  ...| _        | no ¬a#t₂ = no λ { (#∷ _ a#t₂) → ¬a#t₂ a#t₂ }
  ...| no ¬a#t₁ | _        = no λ { (#∷ a#t₁ _) → ¬a#t₁ a#t₁ }
  Δ ⊢ a #? (f $ t) with Δ ⊢ a #? t
  ...| yes a#t = yes (#$ a#t)
  ...| no ¬a#t = no λ { (#$ a#t) → ¬a#t a#t }

  -- _⊢_⟨_⟩ : ∀ {Γ} → #Cx Γ → #Cx Γ → Subst Γ → Set
  -- Δ' ⊢ Δ ⟨ σ ⟩ = All (λ p → Δ' ⊢ proj₁ p # substVar (proj₂ p) σ) Δ

  _⊢_⟨_⟩ : ∀ {Γ} → #Cx Γ → #Cx Γ → Subst Γ → Set
  Δ' ⊢ Δ ⟨ σ ⟩ = ∀ {p} → p ∈ Δ → Δ' ⊢ proj₁ p # substVar (proj₂ p) σ

  open PropEq.≡-Reasoning

  infix 4 _∈×_ _∈×?_ _∈atoms_ _∈atoms?_ _∈atoms*_ _∈atoms*?_

  _∈×_ : Atom → Atom × Atom → Set
  a ∈× p = a ≡ proj₁ p ⊎ a ≡ proj₂ p

  _∈×?_ : Decidable _∈×_
  a ∈×? p with a ≟ᴬ proj₁ p
  ...| yes a₁ = yes (inj₁ a₁)
  ...| no ¬a₁ with a ≟ᴬ proj₂ p
  ...| yes a₂ = yes (inj₂ a₂)
  ...| no ¬a₂ = no λ { (inj₁ a₁) → ¬a₁ a₁
                     ; (inj₂ a₂) → ¬a₂ a₂
                     }

  _∈atoms*_ : Atom → Permutation → Set
  a ∈atoms*    id = ⊥
  a ∈atoms* p ◂ π = a ∈× p ⊎ a ∈atoms* π

  _∈atoms*?_ : Decidable _∈atoms*_
  a ∈atoms*?    id = no λ z → z
  a ∈atoms*? p ◂ π with a ∈×? p
  ...| yes a₁ = yes (inj₁ a₁)
  ...| no ¬a₁ with a ∈atoms*? π
  ...| yes a₂ = yes (inj₂ a₂)
  ...| no ¬a₂ = no λ { (inj₁ a₁) → ¬a₁ a₁
                     ; (inj₂ a₂) → ¬a₂ a₂
                     }

  _∈atoms_ : ∀ {Γ s} → Atom → Term Γ s → Set
  a ∈atoms atom b    = a ≡ b
  a ∈atoms (π · _)   = a ∈atoms* π
  a ∈atoms ([ b ] t) = a ≡ b ⊎ a ∈atoms t
  a ∈atoms t₁ ∷ t₂   = a ∈atoms t₁ ⊎ a ∈atoms t₂
  a ∈atoms _ $ t     = a ∈atoms t

  _∈atoms?_ : ∀ {Γ s} → Decidable (_∈atoms_ {Γ} {s})
  a ∈atoms? atom b    = a ≟ᴬ b
  a ∈atoms? (π · _)   = a ∈atoms*? π
  a ∈atoms? ([ b ] t) with a ≟ᴬ b
  ...| yes a≡b = yes (inj₁ a≡b)
  ...| no  a≢b with a ∈atoms? t
  ...| yes a∈t = yes (inj₂ a∈t)
  ...| no  a∉t = no λ { (inj₁ a≡b) → a≢b a≡b
                      ; (inj₂ a∈t) → a∉t a∈t
                      }
  a ∈atoms? t₁ ∷ t₂ with a ∈atoms? t₁
  ...| yes a∈t₁ = yes (inj₁ a∈t₁)
  ...| no  a∉t₁ with a ∈atoms? t₂
  ...| yes a∈t₂ = yes (inj₂ a∈t₂)
  ...| no  a∉t₂ = no λ { (inj₁ a∈t₁) → a∉t₁ a∈t₁
                       ; (inj₂ a∈t₂) → a∉t₂ a∈t₂
                       }
  a ∈atoms? _ $ t = a ∈atoms? t

  atoms* : Permutation → List Atom
  atoms* id = []
  atoms* ((a , b) ◂ π) = a ∷ b ∷ atoms* π

  atoms : ∀ {Γ s} → Term Γ s → List Atom
  atoms (atom a) = [ a ]ᴸ
  atoms (π · _) = atoms* π
  atoms ([ a ] t) = a ∷ atoms t
  atoms (t₁ ∷ t₂) = atoms t₁ ++ atoms t₂
  atoms (_ $ t) = atoms t

  record freshly-extends[∉_] {Γ : Cx} (as : List Atom) (Δ' Δ : #Cx Γ) : Set where
    field
      extends⊆  : Δ' ⊆ Δ
      extends∈  : ∀ {a p}
                → p ∈[ Δ' - Δ ]
                → a ∈ as
                → proj₁ p ≢ a
      extends∈# : ∀ {p q}
                → p ∈[ Δ' - Δ ]
                → q ∈ Δ
                → proj₁ p ≢ proj₁ q

  open freshly-extends[∉_] public

  freshly-extends : ∀ {Γ} (Δ' Δ : #Cx Γ) → Set
  freshly-extends = freshly-extends[∉ [] ]

  -- Lemma 2.16
  ∘∙ : ∀ {Γ s} π₁ π₂ (t : Term Γ s) → (π₁ ∘ π₂) ∙ t ≡ π₁ ∙ π₂ ∙ t
  ∘∙ π₁ π₂ (atom a)  = cong atom (∘permute π₁ π₂ a)
  ∘∙ π₁ π₂ (π · X)   = cong (λ π → π · X) (∘assoc π₁ π₂ π)
  ∘∙ π₁ π₂ ([ a ] t) = cong₂ [_]_ (∘permute π₁ π₂ a) (∘∙ π₁ π₂ t)
  ∘∙ π₁ π₂ (t₁ ∷ t₂) = cong₂ _∷_ (∘∙ π₁ π₂ t₁) (∘∙ π₁ π₂ t₂)
  ∘∙ π₁ π₂ (f $ t)   = cong (λ t → f $ t) (∘∙ π₁ π₂ t)

  -- Lemma 2.20 -- all trivial

  #permute⁻¹ : ∀ {Γ s a} {Δ : #Cx Γ} {t : Term Γ s}
        → (π : Permutation)
        → Δ ⊢ permute (π ⁻¹) a # t
        → Δ ⊢ a # π ∙ t
  #permute⁻¹ π (#atom a≢b)     = #atom λ a≡πb → a≢b (inverse-permuteᵣ π a≡πb)
  #permute⁻¹ {Δ = Δ} π (#var {π = π'} {X = X} i) =
    #var (subst (λ x → (x , X) ∈ Δ)
           (trans (sym (∘permute (π' ⁻¹) (π ⁻¹) _)) (≃⟦ sym (∘⁻¹ π π') ⟧ _)) i)
  #permute⁻¹ π (#abs≡ a≡b)     = #abs≡ (trans (sym (inverse-permuteᵣ (π ⁻¹) (sym a≡b))) (≃⟦ (involutive⁻¹ π) ⟧ _))
  #permute⁻¹ π (#abs≢ a≢b a#t) = #abs≢ (λ a≡πb → a≢b (inverse-permuteᵣ π a≡πb)) (#permute⁻¹ π a#t)
  #permute⁻¹ π (#∷ a#t₁ a#t₂)  = #∷ (#permute⁻¹ π a#t₁) (#permute⁻¹ π a#t₂)
  #permute⁻¹ π (#$ a#t)        = #$ (#permute⁻¹ π a#t)

  -- Lemma 2.21
  #weaken : ∀ {Γ s a} {Δ Δ' : #Cx Γ} {t : Term Γ s}
          → Δ ⊆ Δ'
          → Δ ⊢ a # t
          → Δ' ⊢ a # t
  #weaken δ (#atom a≢b)     = #atom a≢b
  #weaken δ (#var i)        = #var (δ i)
  #weaken δ (#abs≡ a≡b)     = #abs≡ a≡b
  #weaken δ (#abs≢ a≢b a#t) = #abs≢ a≢b (#weaken δ a#t)
  #weaken δ (#∷ a#t₁ a#t₂)  = #∷ (#weaken δ a#t₁) (#weaken δ a#t₂)
  #weaken δ (#$ a#t)        = #$ (#weaken δ a#t)

  -- -- Lemma 2.23
  #strengthen : ∀ {Γ s a} {Δ Δ' : #Cx Γ} {t : Term Γ s}
              → freshly-extends[∉ a ∷ atoms t ] Δ' Δ
              → Δ' ⊢ a # t
              → Δ ⊢ a # t
  #strengthen #δ (#atom a≢b)          = #atom a≢b
  #strengthen #δ (#var i)             = #var (extends⊆ #δ i)
  #strengthen #δ (#abs≡ a≡b)          = #abs≡ a≡b
  #strengthen #δ (#$ a#t)             = #$ (#strengthen #δ a#t)
  #strengthen {Γ = Γ} {a = a} {Δ} {Δ'} {t₁ ∷ t₂} #δ (#∷ a#t₁ a#t₂) =
    #∷ (#strengthen #δ₁ a#t₁) (#strengthen #δ₂ a#t₂)
    where
    extends∈₁ : ∀ {a' p} → p ∈[ Δ' - Δ ] → a' ∈ a ∷ atoms t₁ → proj₁ p ≢ a'
    extends∈₁ i j = extends∈ #δ i (⊆++ₗ (atoms t₂) j)
    extends∈₂ : ∀ {a' p} → p ∈[ Δ' - Δ ] → a' ∈ a ∷ atoms t₂ → proj₁ p ≢ a'
    extends∈₂ i ₀      = extends∈ #δ i ₀
    extends∈₂ i (₁₊ j) = extends∈ #δ i (₁₊ (⊆++ᵣ (atoms t₁) j))
    #δ₁ : freshly-extends[∉ a ∷ atoms t₁ ] Δ' Δ
    #δ₁ = record
      { extends⊆  = extends⊆ #δ
      ; extends∈  = extends∈₁
      ; extends∈# = extends∈# #δ
      }
    #δ₂ : freshly-extends[∉ a ∷ atoms t₂ ] Δ' Δ
    #δ₂ = record
      { extends⊆  = extends⊆ #δ
      ; extends∈  = extends∈₂
      ; extends∈# = extends∈# #δ
      }
  #strengthen {Γ = Γ} {a = a} {Δ} {Δ'} {[ b ] t} #δ (#abs≢ a≢b a#t) =
    #abs≢ a≢b (#strengthen #δ' a#t)
    where
    #δ' : freshly-extends[∉ a ∷ atoms t ] Δ' Δ
    #δ' = record
      { extends⊆  = extends⊆ #δ
      ; extends∈  = extends∈'
      ; extends∈# = extends∈# #δ
      }
      where
      extends∈' : ∀ {a' p} → p ∈[ Δ' - Δ ] → a' ∈ a ∷ atoms t → proj₁ p ≢ a'
      extends∈' i ₀      = extends∈ #δ i ₀
      extends∈' i (₁₊ j) = extends∈ #δ i (₁₊ ₁₊ j)

  -- Lemma 2.24
  #permute : ∀ {Γ s a} {Δ : #Cx Γ} {t : Term Γ s}
           → (π : Permutation)
           → Δ ⊢ a # t
           → Δ ⊢ permute π a # π ∙ t
  #permute π (#atom a≉b)       = #atom λ πa≈πb → a≉b (permute-injective π πa≈πb)
  #permute π (#abs≡ a≈b)       = #abs≡ (cong (permute π) a≈b)
  #permute π (#abs≢ a≉b a#t)   = #abs≢ (λ πa≈πb → a≉b (permute-injective π πa≈πb)) (#permute π a#t)
  #permute π (#∷ a#t₁ a#t₂)    = #∷ (#permute π a#t₁) (#permute π a#t₂)
  #permute π (#$ a#t)          = #$ (#permute π a#t)
  #permute π (#var {π = π'} i) = #var
    ( subst (λ x → (x , _) ∈ _)
      ( begin
        permute (π' ⁻¹) _                       ≡⟨ cong (permute (π' ⁻¹)) (sym (permute⁻¹∘ π _)) ⟩
        permute (π' ⁻¹) (permute (π ⁻¹ ∘ π) _)  ≡⟨ sym (∘permute (π' ⁻¹) (π ⁻¹ ∘ π) _) ⟩
        permute (π' ⁻¹ ∘ π ⁻¹ ∘ π) _            ≡⟨ cong (λ π → permute π _)
                                                   ( begin
             π' ⁻¹ ∘ π ⁻¹ ∘ π                     ≡⟨ sym (∘assoc (π' ⁻¹) (π ⁻¹) π) ⟩
            (π' ⁻¹ ∘ π ⁻¹) ∘ π                    ≡⟨ cong (λ π' → π' ∘ π) (sym (∘⁻¹ π π')) ⟩
            (π ∘ π') ⁻¹ ∘ π                       ∎)
                                                 ⟩
        permute ((π ∘ π') ⁻¹ ∘ π) _             ≡⟨ ∘permute ((π ∘ π') ⁻¹) π _ ⟩
        permute ((π ∘ π') ⁻¹) (permute π _)     ∎)
      i
    )

  #substitute : ∀ {Γ s a} {Δ Δ' : #Cx Γ} {t : Term Γ s}
              → (σ : Subst Γ)
              → Δ' ⊢ Δ ⟨ σ ⟩
              → Δ ⊢ a # t
              → Δ' ⊢ a # (t ⟨ σ ⟩)
  #substitute σ δ (#atom a≢b)     = #atom a≢b
  #substitute σ δ (#var i)        = #permute⁻¹ _ (δ i)
  #substitute σ δ (#abs≡ a≡b)     = #abs≡ a≡b
  #substitute σ δ (#abs≢ a≢b a#t) = #abs≢ a≢b (#substitute σ δ a#t)
  #substitute σ δ (#∷ a#t₁ a#t₂)  = #∷ (#substitute σ δ a#t₁) (#substitute σ δ a#t₂)
  #substitute σ δ (#$ a#t)        = #$ (#substitute σ δ a#t)

  ∙distrib⟨⟩ : ∀ {Γ s} π (σ : Subst Γ) (t : Term Γ s) → π ∙ t ⟨ σ ⟩ ≡ (π ∙ t) ⟨ σ ⟩
  ∙distrib⟨⟩ π σ (atom a)  = refl
  ∙distrib⟨⟩ π σ (π' · X)  = sym (∘∙ π π' (substVar X σ))
  ∙distrib⟨⟩ π σ ([ a ] t) = cong (λ t → [ permute π a ] t) (∙distrib⟨⟩ π σ t)
  ∙distrib⟨⟩ π σ (t₁ ∷ t₂) = cong₂ _∷_ (∙distrib⟨⟩ π σ t₁) (∙distrib⟨⟩ π σ t₂)
  ∙distrib⟨⟩ π σ (f $ t)   = cong (λ t → f $ t) (∙distrib⟨⟩ π σ t)

  infixr 3 _#∪_
  _#∪_ : ∀ {Γ} → #Cx Γ → #Cx Γ → #Cx Γ
  [] #∪ Δ' = Δ'
  p ∷ Δ #∪ Δ' with p ∈#? Δ'
  ...| yes p∈Δ' = Δ #∪ Δ'
  ...| no  p∉Δ' = p ∷ (Δ #∪ Δ')

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
  ...| yes (Δ₁ , a#t₁) | yes (Δ₂ , a#t₂) = yes (Δ₁ ++ Δ₂ , #∷ (#weaken (⊆++ₗ Δ₂) a#t₁) (#weaken (⊆++ᵣ Δ₁) a#t₂))
  ...| _               | no ¬a#t₂        = no λ { (Δ , #∷ _    a#t₂) → ¬a#t₂ (Δ , a#t₂) }
  ...| no ¬a#t₁        | _               = no λ { (Δ , #∷ a#t₁ _   ) → ¬a#t₁ (Δ , a#t₁) }
  a #? f $ t with a #? t
  ...| yes (Δ , a#t)                     = yes (Δ , #$ a#t)
  ...| no ¬a#t                           = no λ { (Δ , #$ a#t) → ¬a#t (Δ , a#t) }
