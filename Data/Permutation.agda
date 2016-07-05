
open import Level renaming (zero to lz ; suc to ls)
open import Relation.Binary using (DecSetoid)

module Data.Permutation {c ℓ} (S : DecSetoid c ℓ) where

open import Relation.Binary using (Rel ; Decidable ; IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Data.Empty
open import Data.Nat using (ℕ ; zero ; suc) renaming
  ( _+_ to _+ⁿ_
  ; _*_ to _*ⁿ_
  )
open import Data.Integer using
  ( ℤ ; +_ ; -[1+_] ; _+_ ; _-_ ; -_ ; _*_ ; _⊖_)
{-
open import Data.Nat using (ℕ ; zero ; suc) renaming
  ( _+_ to _+ℕ_
  ; _*_ to _*ℕ_
  )
open import Data.Nat.Properties.Simple using
  ( +-right-identity
  )
-}

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

infixl 20 _^[+_] _^[_]
_^[+_] : Permutation → ℕ → Permutation
π ^[+ 0     ] = id
π ^[+ suc n ] = π ∘ π ^[+ n ]

_^[_] : Permutation → ℤ → Permutation
π ^[    + n   ] = π ^[+ n ]
π ^[ -[1+ n ] ] = (π ⁻¹) ^[+ suc n ]

{-
same-orbit : Permutation → Carrier → Carrier → Set ℓ
same-orbit π x y = Σ[ n ∈ ℕ ] permute (π ^[ n ]) x ≈ y
-}

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
  open import Data.Nat.Properties.Simple using
    ( +-comm
    ; *-comm
    )
  import Data.Integer.Properties
  open Data.Integer.Properties.RingSolver using
    ( prove ; solve ; con ; var
    ; _:=_ ; _:+_ ; _:*_ ; _:-_ ; :-_ ; _:^_
    )
  open import Algebra
  open import Algebra.Structures

  infixr 0 _≡▹_
  _≡▹_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _≡▹_ = ≡trans

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

  ∘exchangeₗ : ∀ π₁ π₂ π₃ π₄ → (π₁ ∘ π₂ ∘ π₃) ∘ π₄ ≡ (π₁ ∘ π₂) ∘ (π₃ ∘ π₄)
  ∘exchangeₗ π₁ π₂ π₃ π₄ =
      ≡trans (cong (λ π' → π' ∘ π₄) (≡sym (∘assoc π₁ π₂ π₃)))
    $ ∘assoc (π₁ ∘ π₂) π₃ π₄

  ∘exchangeᵢ : ∀ π₁ π₂ π₃ π₄ → π₁ ∘ (π₂ ∘ π₃) ∘ π₄ ≡ (π₁ ∘ π₂) ∘ (π₃ ∘ π₄)
  ∘exchangeᵢ π₁ π₂ π₃ π₄ =
      ≡trans (cong (_∘_ π₁) (∘assoc π₂ π₃ π₄))
    $ ≡sym (∘assoc π₁ π₂ (π₃ ∘ π₄))
      

  ∘▸ : ∀ {p} π₁ π₂ → (π₁ ∘ π₂) ▸ p ≡ π₁ ∘ (π₂ ▸ p)
  ∘▸ id       π₂ = ≡refl
  ∘▸ (p ◂ π₁) π₂ = cong (λ π → p ◂ π) (∘▸ π₁ π₂)

  ▸∘ : ∀ {p} π₁ π₂ → (π₁ ▸ p) ∘ π₂ ≡ π₁ ∘ (p ◂ π₂)
  ▸∘ id       π₂ = ≡refl
  ▸∘ (p ◂ π₁) π₂ = cong (λ π → p ◂ π) (▸∘ π₁ π₂)

  ∘⁻¹ : ∀ π₁ π₂ → (π₁ ∘ π₂) ⁻¹ ≡ π₂ ⁻¹ ∘ π₁ ⁻¹
  ∘⁻¹ id       π₂ = ≡sym (∘id (π₂ ⁻¹))
  ∘⁻¹ (p ◂ π₁) π₂ = ≡trans (cong (λ π → π ▸ p) (∘⁻¹ π₁ π₂)) (∘▸ (π₂ ⁻¹) (π₁ ⁻¹))

  expℕ∘ : ∀ m n π → π ^[+ m +ⁿ n ] ≡ π ^[+ m ] ∘ π ^[+ n ] 
  expℕ∘ 0       n π = ≡refl
  expℕ∘ (suc m) n π = ≡trans (cong (λ π' → π ∘ π') (expℕ∘ m n π))
                             (≡sym (∘assoc π (π ^[+ m ]) (π ^[+ n ])))

  comm-expℕ∘ : ∀ m n π → π ^[+ m ] ∘ π ^[+ n ] ≡ π ^[+ n ] ∘ π ^[+ m ]
  comm-expℕ∘ m n π = ≡trans (≡sym (expℕ∘ m n π))
                   $ ≡trans (cong (λ n → π ^[+ n ]) (+-comm m n))
                   $ expℕ∘ n m π

  comm-expℕ∘1+ : ∀ n π → π ∘ π ^[+ n ] ≡ π ^[+ n ] ∘ π
  comm-expℕ∘1+ 0       π = ∘id π
  comm-expℕ∘1+ (suc n) π = ≡trans (cong (_∘_ π) (comm-expℕ∘1+ n π))
                                  (≡sym (∘assoc π (π ^[+ n ]) π))

  expℕ^ : ∀ m n π → π ^[+ m *ⁿ n ] ≡ π ^[+ n ] ^[+ m ]
  expℕ^ 0       n π = ≡refl
  expℕ^ (suc m) n π = ≡trans (expℕ∘ n (m *ⁿ n) π) 
                             (cong (λ π' → π ^[+ n ] ∘ π') (expℕ^ m n π))

  comm-expℕ^ : ∀ m n π → π ^[+ m ] ^[+ n ] ≡ π ^[+ n ] ^[+ m ]
  comm-expℕ^ m n π = ≡trans (≡sym (expℕ^ n m π))
                   $ ≡trans (cong (λ n → π ^[+ n ]) (*-comm n m))
                   $ expℕ^ m n π

  expℕ-1+ : ∀ n π → π ^[+ n ] ∘ π ≡ π ∘ π ^[+ n ]
  expℕ-1+ 0       π = ≡sym (∘id π)
  expℕ-1+ (suc n) π = ≡trans (∘assoc π (π ^[+ n ]) π)
                             (cong (_∘_ π) (expℕ-1+ n π))

  expℕ⁻¹ : ∀ n π → (π ^[+ n ]) ⁻¹ ≡ (π ⁻¹) ^[+ n ]
  expℕ⁻¹ 0       π = ≡refl
  expℕ⁻¹ (suc n) π = ≡trans (∘⁻¹ π (π ^[+ n ]))
                   $ ≡trans (cong (λ π' → π' ∘ π ⁻¹) (expℕ⁻¹ n π))
                            (expℕ-1+ n (π ⁻¹))

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

  swap-injective : ∀ p {x y} → swap p x ≈ swap p y → x ≈ y
  swap-injective p {x} {y} px≈py with x ≟ proj₁ p | x ≟ proj₂ p | y ≟ proj₁ p | y ≟ proj₂ p
  ...| yes x₁ | _      | yes y₁ | _      = x₁ ▹ sym y₁
  ...| no ¬x₁ | yes x₂ | _      | yes y₂ = x₂ ▹ sym y₂
  ...| _      | yes x₂ | no ¬y₁ | yes y₂ = x₂ ▹ sym y₂
  ...| yes x₁ | no ¬x₂ | no ¬y₁ | yes y₂ = x₁ ▹ sym px≈py ▹ sym y₂
  ...| no ¬x₁ | yes x₂ | yes y₁ | no ¬y₂ = x₂ ▹ sym px≈py ▹ sym y₁
  ...| yes x₁ | no ¬x₂ | no ¬y₁ | no ¬y₂ = ⊥-elim (¬y₂ (sym px≈py))
  ...| no ¬x₁ | yes x₂ | no ¬y₁ | no ¬y₂ = ⊥-elim (¬y₁ (sym px≈py))
  ...| no ¬x₁ | no ¬x₂ | yes y₁ | no ¬y₂ = ⊥-elim (¬x₂ px≈py)
  ...| no ¬x₁ | no ¬x₂ | no ¬y₁ | yes y₂ = ⊥-elim (¬x₁ px≈py)
  ...| yes x₁ | yes x₂ | no ¬y₁ | no ¬y₂ = px≈py
  ...| no ¬x₁ | no ¬x₂ | yes y₁ | yes y₂ = px≈py
  ...| no ¬x₁ | no ¬x₂ | no ¬y₁ | no ¬y₂ = px≈py

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

  ∘permute : ∀ π₁ π₂ x → permute (π₁ ∘ π₂) x ≡ permute π₁ (permute π₂ x)
  ∘permute id       π₂ x = ≡refl
  ∘permute (p ◂ π₁) π₂ x = cong (swap p) (∘permute π₁ π₂ x)

  permute-injective : ∀ π {x y} → permute π x ≈ permute π y → x ≈ y
  permute-injective id      πx≈πy = πx≈πy
  permute-injective (p ◂ π) πx≈πy = permute-injective π (swap-injective p πx≈πy)

  permute▸ : ∀ π {p x} → permute (π ▸ p) x ≡ permute π (swap p x)
  permute▸ id      = ≡refl
  permute▸ (p ◂ π) = cong (swap p) (permute▸ π)

  infix 4 _≃_
  _≃_ : Rel Permutation (c ⊔ ℓ)
  π₁ ≃ π₂ = ∀ x → permute π₁ x ≈ permute π₂ x

  ≃⟦_⟧ : ∀ {π₁ π₂} → π₁ ≡ π₂ → π₁ ≃ π₂
  ≃⟦_⟧ {π₁} {π₂} eq x = subst (λ π' → permute π₁ x ≈ permute π' x) eq refl

  ≈⟦_⟧ : ∀ {x y} → x ≡ y → x ≈ y
  ≈⟦_⟧ {x} eq = subst (λ z → x ≈ z) eq refl

  inverse-permuteₗ : ∀ π {x y} → permute π x ≈ y → x ≈ permute (π ⁻¹) y
  inverse-permuteₗ id      = [id]
  inverse-permuteₗ (p ◂ π) px≈y =
      inverse-permuteₗ π (inverse-swapₗ p px≈y)
    ▹ sym ≈⟦ permute▸ (π ⁻¹) ⟧

  inverse-permuteᵣ : ∀ π {x y} → x ≈ permute π y → permute (π ⁻¹) x ≈ y
  inverse-permuteᵣ id      x≈py = x≈py
  inverse-permuteᵣ (p ◂ π) x≈py =
      ≈⟦ permute▸ (π ⁻¹) ⟧
    ▹ inverse-permuteᵣ π (inverse-swapᵣ p x≈py)

  permute⁻¹∘ : ∀ π → π ⁻¹ ∘ π ≃ id
  permute⁻¹∘ id      _ = refl
  permute⁻¹∘ (p ◂ π) x =
      ≃⟦ ▸∘ (π ⁻¹) (p ◂ π) ⟧ x
    ▹ ≈⟦ ∘permute (π ⁻¹) (p ◂ p ◂ π) x ⟧
    ▹ cong-permute (π ⁻¹) (swap-involutive p)
    ▹ sym ≈⟦ ∘permute (π ⁻¹) π x ⟧
    ▹ permute⁻¹∘ π x

  permute∘⁻¹ : ∀ π → π ∘ π ⁻¹ ≃ id
  permute∘⁻¹ id      _ = refl
  permute∘⁻¹ (p ◂ π) x = 
      cong-swap p
      ( ≃⟦ ≡sym (∘▸ π (π ⁻¹)) ⟧ x )
    ▹ inverse-swapᵣ p
      ( ≈⟦ permute▸ (π ∘ π ⁻¹) ⟧
      ▹ permute∘⁻¹ π (swap p x)
      )

  private
    ≃refl : ∀ {π} → π ≃ π
    ≃refl _ = refl
    ≃sym : ∀ {π₁ π₂} → π₁ ≃ π₂ → π₂ ≃ π₁
    ≃sym p x = sym (p x)
    ≃trans : ∀ {π₁ π₂ π₃} → π₁ ≃ π₂ → π₂ ≃ π₃ → π₁ ≃ π₃
    ≃trans p q x = trans (p x) (q x)
    cong-∘ : _∘_ Preserves₂ _≃_ ⟶ _≃_ ⟶ _≃_
    cong-∘ {π₁} {π₂} {π₃} {π₄} p q x =
        ≈⟦ ∘permute π₁ π₃ x ⟧
      ▹ p (permute π₃ x)
      ▹ cong-permute π₂ (q x)
      ▹ sym (≈⟦ ∘permute π₂ π₄ x ⟧)
    cong⁻¹ : _⁻¹ Preserves _≃_ ⟶ _≃_
    cong⁻¹ {π₁} {π₂} p x =
        inverse-permuteₗ π₂
      $ sym (p (permute (π₁ ⁻¹) x))
      ▹ sym (≈⟦ ∘permute π₁ (π₁ ⁻¹) x ⟧)
      ▹ permute∘⁻¹ π₁ x

  {-
  inverse-expℕₗ : ∀ n π → π ∘ π ^[+ n ] ∘ π ⁻¹ ≃ π ^[+ n ]
  inverse-expℕₗ 0       π = permute∘⁻¹ π
  inverse-expℕₗ (suc n) π x =
      ∘permute π ((π ∘ π ^[+ n ]) ∘ (π ⁻¹)) x
    ▹ cong-permute π
      ( ⟦ ∘assoc π (π ^[+ n ]) (π ⁻¹) ⟧ x
      ▹ inverse-expℕₗ n π x
      )
    ▹ sym (∘permute π (π ^[+ n ]) x)

  inverse-expℕᵣ : ∀ n π → π ⁻¹ ∘ π ^[+ n ] ∘ π ≃ π ^[+ n ]
  inverse-expℕᵣ 0       π   = permute⁻¹∘ π
  inverse-expℕᵣ (suc n) π x =
      ⟦ ∘exchangeᵢ (π ⁻¹) π (π ^[+ n ]) π ⟧ x
    ▹ ∘permute (π ⁻¹ ∘ π) (π ^[+ n ] ∘ π) x
    ▹ cong-permute (π ⁻¹ ∘ π) (⟦ ≡sym (comm-expℕ∘1+ n π) ⟧ x)
    ▹ permute⁻¹∘ π (permute (π ∘ π ^[+ n ]) x)

  ceℕ : ∀ m n π → π ^[+ m ] ∘ π ⁻¹ ^[+ n ] ≃ π ⁻¹ ^[+ n ] ∘ π ^[+ m ]
  ceℕ m n π x =
      ∘permute (π ^[+ m ]) (π ⁻¹ ^[+ n ]) x
    ▹ cong-permute (π ^[+ m ]) (sym (⟦ expℕ⁻¹ n π ⟧ x))
    ▹ {!!}

  comm-expℕ∘⁻¹ : ∀ m n π → π ^[+ m ] ∘ (π ⁻¹) ^[+ n ] ≃ (π ⁻¹) ^[+ n ] ∘ π ^[+ m ]
  comm-expℕ∘⁻¹ 0       n       π x = sym (⟦ ∘id ((π ⁻¹) ^[+ n ]) ⟧ x)
  comm-expℕ∘⁻¹ (suc m) 0       π x = ⟦ ∘id (π ∘ π ^[+ m ]) ⟧ x
  comm-expℕ∘⁻¹ (suc m) (suc n) π x =
      ∘permute (π ^[+ suc m ]) ((π ⁻¹) ^[+ suc n ]) x
    ▹ ⟦ comm-expℕ∘1+ m π ⟧ (permute ((π ⁻¹) ^[+ suc n ]) x)
    ▹ sym (∘permute (π ^[+ m ] ∘ π) ((π ⁻¹) ^[+ suc n ]) x)
    ▹ sym (⟦ ∘exchangeᵢ (π ^[+ m ]) π (π ⁻¹) ((π ⁻¹) ^[+ n ]) ⟧ x)
    ▹ sym (⟦ ∘assoc (π ^[+ m ]) (π ∘ π ⁻¹) ((π ⁻¹) ^[+ n ]) ⟧ x)
    ▹ ∘permute (π ^[+ m ] ∘ π ∘ π ⁻¹) ((π ⁻¹) ^[+ n ]) x
    ▹ ∘permute (π ^[+ m ]) (π ∘ π ⁻¹) (permute ((π ⁻¹) ^[+ n ]) x)
    ▹ cong-permute (π ^[+ m ]) (permute∘⁻¹ π (permute ((π ⁻¹) ^[+ n ]) x))
    -- ▹ sym (⟦ ∘id (π ^[+ m ]) ⟧ (permute ((π ⁻¹) ^[+ n ]) x))
    -- ▹ sym (∘permute (π ^[+ m ]) id (permute ((π ⁻¹) ^[+ n ]) x))
    ▹ cong-permute (π ^[+ m ]) (sym (∘permute id ((π ⁻¹) ^[+ n ]) x))
    ▹ sym (∘permute (π ^[+ m ]) ((π ⁻¹) ^[+ n ]) x)
    ▹ comm-expℕ∘⁻¹ m n π x
    ▹ ∘permute ((π ⁻¹) ^[+ n ]) (π ^[+ m ]) x
    ▹ cong-permute ((π ⁻¹) ^[+ n ])
      ( ∘permute id (π ^[+ m ]) x
      ▹ sym (permute⁻¹∘ π (permute (π ^[+ m ]) x))
      ▹ sym (∘permute (π ⁻¹ ∘ π) (π ^[+ m ]) x)
      )
    ▹ sym (∘permute ((π ⁻¹) ^[+ n ]) ((π ⁻¹ ∘ π) ∘ π ^[+ m ]) x)
    ▹ ⟦ ∘exchangeᵢ ((π ⁻¹) ^[+ n ]) (π ⁻¹) π (π ^[+ m ]) ⟧ x
    ▹ ∘permute ((π ⁻¹) ^[+ n ] ∘ π ⁻¹) (π ∘ π ^[+ m ]) x
    ▹ sym (⟦ comm-expℕ∘1+ n (π ⁻¹) ⟧ (permute (π ^[+ suc m ]) x))
    ▹ sym (∘permute ((π ⁻¹) ^[+ suc n ]) (π ^[+ suc m ]) x)

  expℕ∘⁻¹ : ∀ m n π → π ^[ m ⊖ n ] ≃ π ^[+ m ] ∘ (π ⁻¹) ^[+ n ]
  expℕ∘⁻¹ m       0       π x = sym (⟦ ∘id (π ^[+ m ]) ⟧ x)
  expℕ∘⁻¹ 0       (suc n) π x = refl
  expℕ∘⁻¹ (suc m) (suc n) π x =
      expℕ∘⁻¹ m n π x
    ▹ ∘permute (π ^[+ m ]) ((π ⁻¹) ^[+ n ]) x
    ▹ sym (inverse-expℕₗ m π (permute ((π ⁻¹) ^[+ n ]) x))
    ▹ sym (∘permute (π ∘ π ^[+ m ] ∘ π ⁻¹) ((π ⁻¹) ^[+ n ]) x)
    ▹ ⟦ ∘exchangeₗ π (π ^[+ m ]) (π ⁻¹) ((π ⁻¹) ^[+ n ]) ⟧ x

  exp∘ : ∀ m n π → π ^[ m + n ] ≃ π ^[ m ] ∘ π ^[ n ]
  exp∘ (+ m)      (+ n)      π x = ⟦ expℕ∘ m n π ⟧ x
  exp∘ (+ m)      (-[1+ n ]) π x = expℕ∘⁻¹ m (suc n) π x
  exp∘ (-[1+ m ]) (+ n )     π x = expℕ∘⁻¹ n (suc m) π x
                                 ▹ comm-expℕ∘⁻¹ n (suc m) π x
  exp∘ (-[1+ m ]) (-[1+ n ]) π x =
      ∘permute (π ⁻¹) (π ⁻¹ ∘ (π ⁻¹) ^[+ m +ⁿ n ]) x
    ▹ cong-permute (π ⁻¹)
      ( ∘permute (π ⁻¹) ((π ⁻¹) ^[+ m +ⁿ n ]) x
      ▹ cong-permute (π ⁻¹)
        ( ⟦ expℕ∘ m n (π ⁻¹) ⟧ x
        ▹ ∘permute ((π ⁻¹) ^[+ m ]) ((π ⁻¹) ^[+ n ]) x
        )
      ▹ sym (∘permute (π ⁻¹) ((π ⁻¹) ^[+ m ]) (permute ((π ⁻¹) ^[+ n ]) x))
      ▹ ⟦ comm-expℕ∘1+ m (π ⁻¹) ⟧ (permute ((π ⁻¹) ^[+ n ]) x)
      ▹ sym (∘permute ((π ⁻¹) ^[+ m ] ∘ π ⁻¹) ((π ⁻¹) ^[+ n ]) x)
      ▹ ⟦ ∘assoc ((π ⁻¹) ^[+ m ]) (π ⁻¹) ((π ⁻¹) ^[+ n ]) ⟧ x
      )
    ▹ sym (∘permute (π ⁻¹) ((π ⁻¹) ^[+ m ] ∘ π ⁻¹ ∘ (π ⁻¹) ^[+ n ]) x)
    ▹ sym (⟦ ∘assoc (π ⁻¹) ((π ⁻¹) ^[+ m ]) ((π ⁻¹) ∘ (π ⁻¹) ^[+ n ]) ⟧ x)
  -}

  ≃isEquivalence : IsEquivalence _≃_
  ≃isEquivalence = record
    { refl  = λ {π} → ≃refl {π}
    ; sym   = λ {π₁ π₂} → ≃sym {π₁} {π₂}
    ; trans = λ {π₁ π₂ π₃} → ≃trans {π₁} {π₂} {π₃}
    }

  isSemigroup : IsSemigroup _≃_ _∘_
  isSemigroup = record
    { isEquivalence = ≃isEquivalence
    ; assoc = λ π₁ π₂ π₃ x → subst (λ π → _≈_ (permute ((π₁ ∘ π₂) ∘ π₃) x) (permute π x)) (∘assoc π₁ π₂ π₃) refl
    ; ∙-cong = λ {π₁ π₂ π₃ π₄} → cong-∘ {π₁} {π₂} {π₃} {π₄}
    }

  ≃semigroup : Semigroup _ _
  ≃semigroup = record
    { Carrier     = Permutation
    ; _≈_         = _≃_
    ; _∙_         = _∘_
    ; isSemigroup = isSemigroup
    }

  isMonoid : IsMonoid _≃_ _∘_ id
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity = (λ π x → refl) , (λ π x → subst (λ π' → permute (π ∘ id) x ≈ permute π' x) (∘id π) refl)
    }

  ≃monoid : Monoid _ _
  ≃monoid = record
    { Carrier  = Permutation
    ; _≈_      = _≃_
    ; _∙_      = _∘_
    ; ε        = id
    ; isMonoid = isMonoid
    }

  isGroup : IsGroup _≃_ _∘_ id _⁻¹
  isGroup = record
    { isMonoid = isMonoid
    ; inverse = permute⁻¹∘ , permute∘⁻¹
    ; ⁻¹-cong = λ {π₁ π₂} → cong⁻¹ {π₁} {π₂}
    }

  ≃group : Group _ _
  ≃group = record
    { Carrier = Permutation
    ; _≈_     = _≃_
    ; _∙_     = _∘_
    ; ε       = id
    ; _⁻¹     = _⁻¹
    ; isGroup = isGroup
    }
