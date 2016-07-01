
open import Level renaming (zero to lz ; suc to ls)
open import Relation.Binary using (DecSetoid)

module Data.Permutation {c ℓ} (S : DecSetoid c ℓ) where

open import Relation.Binary using (Rel ; Decidable ; IsEquivalence)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Empty

open DecSetoid S

infix 4 _≉_
_≉_ : Rel Carrier ℓ
x ≉ y = ¬ (x ≈ y)

infixr 0 _¬▹_
_¬▹_ : ∀ {x y z} → x ≈ y → y ≉ z → x ≉ z
_¬▹_ x≈y y≉z x≈z = y≉z (trans (sym x≈y) x≈z)

infixr 0 _▹_
_▹_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
_▹_ {x} {y} {z} = trans {x} {y} {z}

infixr 5 _◂_
data Permutation : Set c where
  id  : Permutation
  _◂_ : (p : Carrier × Carrier)
      → (π : Permutation)
      → Permutation

open import Data.Sum

infix 4 _∈-nontriv_
data _∈-nontriv_ (x : Carrier) : Permutation → Set (c ⊔ ℓ) where
  ◂₁_ : ∀ {p π}
      → x ≈ proj₁ p
      → x ∈-nontriv p ◂ π
  ◂₂_ : ∀ {p π}
      → x ≈ proj₂ p
      → x ∈-nontriv p ◂ π
  ◂ᵣ_ : ∀ {p π}
      → x ∈-nontriv π
      → x ∈-nontriv p ◂ π

_∈-nontriv?_ : Decidable _∈-nontriv_
x ∈-nontriv? id = no λ ()
x ∈-nontriv? (p ◂ π) with x ≟ proj₁ p | x ≟ proj₂ p
...| yes x₁ | _ = yes (◂₁ x₁)
...| no ¬x₁ | yes x₂ = yes (◂₂ x₂)
...| no ¬x₁ | no ¬x₂ with x ∈-nontriv? π
...| yes r = yes (◂ᵣ r)
...| no ¬r = no λ
  { (◂₁ x₁) → ¬x₁ x₁
  ; (◂₂ x₂) → ¬x₂ x₂
  ; (◂ᵣ r)  → ¬r r
  }

swap : Carrier × Carrier → Carrier → Carrier
swap p x with x ≟ proj₁ p | x ≟ proj₂ p
...| yes p₁ | yes p₂ = x
...| yes p₁ | no ¬p₂ = proj₂ p
...| no ¬p₁ | yes p₂ = proj₁ p
...| no ¬p₁ | no ¬p₂ = x

permute : Permutation → Carrier → Carrier
permute id      x = x
permute (p ◂ π) x = swap p (permute π x)

permute* : Permutation → Permutation → Permutation
permute* π₁ id             = id
permute* π₁ ((x , y) ◂ π₂) = (permute π₁ x , permute π₁ y) ◂ permute* π₁ π₂

infixl 6 _▸_
_▸_ : Permutation → Carrier × Carrier → Permutation
id ▸ p      = p ◂ id
(q ◂ π) ▸ p = q ◂ π ▸ p

_⁻¹ : Permutation → Permutation
id ⁻¹      = id
(p ◂ π) ⁻¹ = π ⁻¹ ▸ p

infixr 9 _∘_
_∘_ : Permutation → Permutation → Permutation
id       ∘ π₁ = π₁
(p ◂ π₂) ∘ π₁ = p ◂ π₂ ∘ π₁

infix 4 _≋_
infixr 5 _◂≋_
data _≋_ : Permutation → Permutation → Set (c ⊔ ℓ) where
  id≋  : id ≋ id
  _◂≋_ : ∀ {p q π₁ π₂}
       → proj₁ p ≈ proj₁ q
       × proj₂ p ≈ proj₂ q
       → π₁ ≋ π₂
       → p ◂ π₁ ≋ q ◂ π₂

private
  ≋refl : ∀ {π} → π ≋ π
  ≋refl {id}    = id≋
  ≋refl {p ◂ π} = (refl , refl) ◂≋ ≋refl {π}
  ≋sym : ∀ {π₁ π₂} → π₁ ≋ π₂ → π₂ ≋ π₁
  ≋sym id≋ = id≋
  ≋sym (p ◂≋ prf) = (sym (proj₁ p) , sym (proj₂ p)) ◂≋ ≋sym prf
  ≋trans : ∀ {π₁ π₂ π₃} → π₁ ≋ π₂ → π₂ ≋ π₃ → π₁ ≋ π₃
  ≋trans id≋ id≋ = id≋
  ≋trans (p ◂≋ prf₁) (q ◂≋ prf₂) = (trans (proj₁ p) (proj₁ q) , trans (proj₂ p) (proj₂ q)) ◂≋ ≋trans prf₁ prf₂

  ≋isEquivalence : IsEquivalence _≋_
  ≋isEquivalence = record
    { refl  = ≋refl
    ; sym   = ≋sym
    ; trans = ≋trans
    }
  
  infix 4 _≋?_
  _≋?_ : Decidable _≋_
  id ≋? id     = yes id≋
  id ≋? p ◂ π₂ = no λ ()
  p ◂ π₁ ≋? id = no λ ()
  p ◂ π₁ ≋? q ◂ π₂ with proj₁ p ≟ proj₁ q | proj₂ p ≟ proj₂ q
  ...| no ¬prf₁ | _        = no λ
    { ((prf₁ , _) ◂≋ _) → ¬prf₁ prf₁
    }
  ...| _        | no ¬prf₂ = no λ
    { ((_ , prf₂) ◂≋ _) → ¬prf₂ prf₂
    }
  ...| yes prf₁ | yes prf₂ with π₁ ≋? π₂
  ...| yes prf₃ = yes ((prf₁ , prf₂) ◂≋ prf₃)
  ...| no ¬prf₃ = no λ
    { (_ ◂≋ prf₃) → ¬prf₃ prf₃
    }

decSetoid : DecSetoid c (c ⊔ ℓ)
decSetoid = record
  { Carrier = Permutation
  ; _≈_ = _≋_
  ; isDecEquivalence = record
    { isEquivalence = ≋isEquivalence
    ; _≟_ = _≋?_
    }
  }

module Properties where
  open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; cong ; subst) renaming
    ( refl  to ≡refl
    ; sym   to ≡sym
    ; trans to ≡trans
    )
  open import Function using (const ; _$_) renaming
    ( id  to [id]
    ; _∘_ to _[∘]_
    )

  ≡↦≋ : ∀ {π₁ π₂} → π₁ ≡ π₂ → π₁ ≋ π₂
  ≡↦≋ {π₁} π₁≡π₂ = subst (λ π → π₁ ≋ π) π₁≡π₂ ≋refl

  ∘id : ∀ π → π ∘ id ≡ π
  ∘id id      = ≡refl
  ∘id (p ◂ π) = cong (λ π₁ → p ◂ π₁) (∘id π)

  ▸⁻¹ : ∀ {p} π → (π ▸ p) ⁻¹ ≡ p ◂ π ⁻¹
  ▸⁻¹ id      = ≡refl
  ▸⁻¹ (q ◂ π) = cong (λ π → π ▸ q) (▸⁻¹ π)

  involutive⁻¹ : ∀ π → π ⁻¹ ⁻¹ ≡ π
  involutive⁻¹ id      = ≡refl
  involutive⁻¹ (p ◂ π) = ≡trans (▸⁻¹ (π ⁻¹)) (cong (λ π₁ → p ◂ π₁) (involutive⁻¹ π))

  ∘assoc : ∀ π₁ π₂ π₃ → ((π₁ ∘ π₂) ∘ π₃) ≡ π₁ ∘ (π₂ ∘ π₃)
  ∘assoc id       π₂ π₃ = ≡refl
  ∘assoc (p ◂ π₁) π₂ π₃ = cong (λ π → p ◂ π) (∘assoc π₁ π₂ π₃)

  ∘▸ : ∀ {p} π₁ π₂ → (π₁ ∘ π₂) ▸ p ≡ π₁ ∘ (π₂ ▸ p)
  ∘▸ id       π₂ = ≡refl
  ∘▸ (p ◂ π₁) π₂ = cong (λ π → p ◂ π) (∘▸ π₁ π₂)

  ▸∘ : ∀ {p} π₁ π₂ → (π₁ ▸ p) ∘ π₂ ≡ π₁ ∘ (p ◂ π₂)
  ▸∘ id       π₂ = ≡refl
  ▸∘ (p ◂ π₁) π₂ = cong (λ π → p ◂ π) (▸∘ π₁ π₂)

  ∘⁻¹ : ∀ π₁ π₂ → (π₁ ∘ π₂) ⁻¹ ≡ π₂ ⁻¹ ∘ π₁ ⁻¹
  ∘⁻¹ id       π₂ = ≡sym (∘id (π₂ ⁻¹))
  ∘⁻¹ (p ◂ π₁) π₂ = ≡trans (cong (λ π → π ▸ p) (∘⁻¹ π₁ π₂)) (∘▸ (π₂ ⁻¹) (π₁ ⁻¹))



  swapₗᵣ : ∀ p {x} → x ≈ proj₁ p → x ≈ proj₂ p → swap p x ≈ x
  swapₗᵣ p {x} x≈p₁ x≈p₂ with x ≟ proj₁ p | x ≟ proj₂ p
  ...| yes x₁ | yes x₂ = refl
  ...| yes x₁ | no ¬x₂ = sym x≈p₂
  ...| no ¬x₁ | yes x₂ = sym x≈p₁
  ...| no ¬x₁ | no ¬x₂ = refl

  swapₗ : ∀ p {x} → x ≈ proj₁ p → swap p x ≈ proj₂ p
  swapₗ p {x} px₁ with x ≟ proj₁ p | x ≟ proj₂ p
  ...| yes x₁ | yes x₂ = x₂
  ...| yes x₁ | no ¬x₂ = refl
  ...| no ¬x₁ | _      = ⊥-elim (¬x₁ px₁)

  swapᵣ : ∀ p {x} → x ≈ proj₂ p → swap p x ≈ proj₁ p
  swapᵣ p {x} px₂ with x ≟ proj₁ p | x ≟ proj₂ p
  ...| yes x₁ | yes x₂ = x₁
  ...| no ¬x₁ | yes x₂ = refl
  ...| _      | no ¬x₂ = ⊥-elim (¬x₂ px₂)

  swap₋ : ∀ p {x} → (x ≉ proj₁ p) → (x ≉ proj₂ p) → swap p x ≈ x
  swap₋ p {x} x≉p₁ x≉p₂ with x ≟ proj₁ p | x ≟ proj₂ p
  ...| yes x₁ | yes x₂ = refl
  ...| yes x₁ | no ¬x₂ = ⊥-elim (x≉p₁ x₁)
  ...| no ¬x₁ | yes x₂ = ⊥-elim (x≉p₂ x₂)
  ...| no ¬x₁ | no ¬x₂ = refl

  swap₁ : ∀ p → swap p (proj₁ p) ≈ proj₂ p
  swap₁ p with proj₁ p ≟ proj₁ p | proj₁ p ≟ proj₂ p
  ...| no ¬p₁ | _      = ⊥-elim (¬p₁ refl)
  ...| yes p₁ | yes p₂ = p₂
  ...| yes p₁ | no ¬p₂ = refl

  swap₂ : ∀ p → swap p (proj₂ p) ≈ proj₁ p
  swap₂ p with proj₂ p ≟ proj₁ p | proj₂ p ≟ proj₂ p
  ...| _      | no ¬p₂ = ⊥-elim (¬p₂ refl)
  ...| yes p₁ | yes p₂ = p₁
  ...| no ¬p₁ | yes p₂ = refl


  cong-swap : ∀ p {x y} → x ≈ y → swap p x ≈ swap p y
  cong-swap p {x} {y} x≈y with y ≟ proj₁ p | y ≟ proj₂ p
  ...| yes y₁ | yes y₂ = swapₗᵣ p (x≈y ▹ y₁) (x≈y ▹ y₂) ▹ x≈y
  ...| yes y₁ | no ¬y₂ = swapₗ p (x≈y ▹ y₁)
  ...| no ¬y₁ | yes y₂ = swapᵣ p (x≈y ▹ y₂)
  ...| no ¬y₁ | no ¬y₂ = swap₋ p (x≈y ¬▹ ¬y₁) (x≈y ¬▹ ¬y₂) ▹ x≈y

  swap-involutive : ∀ p {x} → swap p (swap p x) ≈ x
  swap-involutive p {x} with x ≟ proj₁ p | x ≟ proj₂ p
  ...| yes x₁ | yes x₂ = swapₗᵣ p x₁ x₂
  ...| yes x₁ | no ¬x₂ = swap₂ p ▹ sym x₁
  ...| no ¬x₁ | yes x₂ = swap₁ p ▹ sym x₂
  ...| no ¬x₁ | no ¬x₂ = swap₋ p ¬x₁ ¬x₂

  inverse-swapₗ : ∀ p {x y} → swap p x ≈ y → x ≈ swap p y
  inverse-swapₗ p px≈y = sym (swap-involutive p) ▹ cong-swap p px≈y

  inverse-swapᵣ : ∀ p {x y} → x ≈ swap p y → swap p x ≈ y
  inverse-swapᵣ p x≈py = sym (inverse-swapₗ p (sym x≈py))

  cong-permute : ∀ π {x y} → x ≈ y → permute π x ≈ permute π y
  cong-permute id      = [id]
  cong-permute (p ◂ π) = cong-swap p [∘] cong-permute π

  ∘permute : ∀ π₁ π₂ x → permute (π₁ ∘ π₂) x ≈ permute π₁ (permute π₂ x)
  ∘permute id       _  _ = refl
  ∘permute (p ◂ π₁) π₂ x = cong-swap p (∘permute π₁ π₂ x)

  infix 4 _≃_
  _≃_ : Rel Permutation (c ⊔ ℓ)
  π₁ ≃ π₂ = ∀ x → permute π₁ x ≈ permute π₂ x

  ≃isEquivalence : IsEquivalence _≃_
  ≃isEquivalence = record
    { refl  = λ _ → refl
    ; sym   = λ p x → sym (p x)
    ; trans = λ p q x → p x ▹ q x
    }

  permute▸ : ∀ π {p x} → permute (π ▸ p) x ≈ permute π (swap p x)
  permute▸ id      = refl
  permute▸ (q ◂ π) = cong-swap q (permute▸ π)

  inverse-permute : ∀ π {x y} → permute π x ≈ y → x ≈ permute (π ⁻¹) y
  inverse-permute id      = [id]
  inverse-permute (p ◂ π) px≈y =
      inverse-permute π (inverse-swapₗ p px≈y)
    ▹ sym (permute▸ (π ⁻¹))

  permute⁻¹∘ : ∀ π → π ⁻¹ ∘ π ≃ id
  permute⁻¹∘ id      _ = refl
  permute⁻¹∘ (p ◂ π) x =
    subst (λ π' → permute π' x ≈ x)
          (≡sym (▸∘ (π ⁻¹) (p ◂ π)))
    $ ∘permute (π ⁻¹) (p ◂ p ◂ π) x
    ▹ cong-permute (π ⁻¹) (swap-involutive p)
    ▹ sym (∘permute (π ⁻¹) π x)
    ▹ permute⁻¹∘ π x

  permute∘⁻¹ : ∀ π → π ∘ π ⁻¹ ≃ id
  permute∘⁻¹ id      _ = refl
  permute∘⁻¹ (p ◂ π) x = 
    subst (λ π' → swap p (permute π' x) ≈ x)
          (∘▸ π (π ⁻¹))
    $ inverse-swapᵣ p
      ( permute▸ (π ∘ π ⁻¹)
      ▹ permute∘⁻¹ π (swap p x)
      )
