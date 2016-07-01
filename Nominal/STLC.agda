
module Nominal.STLC where

open import Relation.Binary using (Decidable)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.String renaming (String to Atom ; _≟_ to _≟ᴬ_)
open import Data.Product

data STLC : Set where
  lam app sub subᵒ : STLC

infix 4 _≟ᶜ_
_≟ᶜ_ : Decidable (_≡_ {A = STLC})
lam ≟ᶜ lam = yes refl
lam ≟ᶜ app = no λ ()
lam ≟ᶜ sub = no λ ()
lam ≟ᶜ subᵒ = no λ ()
app ≟ᶜ lam = no λ ()
app ≟ᶜ app = yes refl
app ≟ᶜ sub = no λ ()
app ≟ᶜ subᵒ = no λ ()
sub ≟ᶜ lam = no λ ()
sub ≟ᶜ app = no λ ()
sub ≟ᶜ sub = yes refl
sub ≟ᶜ subᵒ = no λ ()
subᵒ ≟ᶜ lam = no λ ()
subᵒ ≟ᶜ app = no λ ()
subᵒ ≟ᶜ sub = no λ ()
subᵒ ≟ᶜ subᵒ = yes refl

open import Nominal

arity : STLC → Arity
arity lam  = [𝔸] 𝕋 , 𝕋
arity app  = 𝕋 ⊗ 𝕋 , 𝕋
arity sub = [𝔸] 𝕋 ⊗ 𝕋 , 𝕋
arity subᵒ = [𝔸] [𝔸] 𝕋 ⊗ 𝕋 , ([𝔸] 𝕋)

open Nominal.Terms Atom _≟ᴬ_ STLC _≟ᶜ_ arity

f = {!domᶜ!}
