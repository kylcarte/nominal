
open import Level renaming (zero to lz ; suc to ls)
open import Relation.Binary using (DecSetoid)

module Data.Substitution {c ℓ} (decSetoid : DecSetoid c ℓ) where

open import Relation.Binary using (Rel ; Decidable ; IsEquivalence)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Data.Product using (Σ ; Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Maybe using (Maybe ; just ; nothing)

open DecSetoid decSetoid

infixr 5 _∷_
data Substitution {p} (P : Carrier → Set p) : Set (p ⊔ c ⊔ ℓ) where
  []  : Substitution P
  _∷_ : (p : Σ Carrier P)
      → (σ : Substitution P)
      → Substitution P

substitute : ∀ {p} {P : Carrier → Set p} → (x : Carrier) → Substitution P → Maybe (Σ[ y ∈ Carrier ] x ≈ y × P y)
substitute x [] = nothing
substitute x (p ∷ σ) with x ≟ proj₁ p
...| yes x≈y = just (proj₁ p , x≈y , proj₂ p)
...| no  x≉y = substitute x σ
