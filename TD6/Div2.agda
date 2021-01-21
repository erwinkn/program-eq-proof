open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Nat.Properties using (+-suc)

open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

{- 5.1 Extrinsic approach -}

div2 : ℕ → ℕ
div2 zero = zero
div2 (suc zero) = zero
div2 (suc (suc n)) = 1 + div2 n

test5 : ℕ
test5 = div2 (suc (suc (suc (suc (suc zero)))))

suc-≡ : {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
suc-≡ refl = refl

div2-correct : (n : ℕ) → (2 * div2 n ≡ n) ∨ (suc (2 * div2 n) ≡ n)
div2-correct zero = left refl
div2-correct (suc zero) = right refl
div2-correct (suc (suc n)) with div2-correct n
div2-correct (suc (suc n)) | left even rewrite +-suc (div2 n) (div2 n + 0) = left (suc-≡ (suc-≡ even))
div2-correct (suc (suc n)) | right odd rewrite +-suc (div2 n) (div2 n + 0) = right (suc-≡ (suc-≡ odd))

{- 5.2 Intrinsic approach -}

{- There might be a more elegant way to rewrite this rather than using trans directly here -}
div2' : (n : ℕ) → Σ ℕ (λ q → (2 * q ≡ n) ∨ (suc (2 * q) ≡ n))
div2' zero = zero , (left refl)
div2' (suc zero) = zero , (right refl)
div2' (suc (suc n)) with proj₂ (div2' n)
...                 | left even =
                            1 + proj₁ (div2' n) ,
                            left ( suc-≡ (trans (+-suc (proj₁ (div2' n)) (proj₁ (div2' n) + 0)) (suc-≡ even) ))
...                 | right odd =
                            1 + proj₁ (div2' n) ,
                            right (suc-≡ (suc-≡ (trans (+-suc (proj₁ (div2' n)) (proj₁ (div2' n) + 0)) odd)))
