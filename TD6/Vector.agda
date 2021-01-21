open import Data.List

{- --- 6. Vectors --- -}

{- 6.1 Warmup -}

{- Problem: what do we return for the empty list ? -}
head2 : {A : Set} → List A → A
head2 [] = {!!}
head2 (x ∷ l) = x

{- 6.2 Definition -}
open import Data.Nat

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

{- 6.3 Head and tail -}
head-vec : {A : Set} → {n : ℕ} → Vec A (suc n) → A
head-vec (x :: v) = x

tail-vec : {A : Set} → {n : ℕ} → Vec A (suc n) → Vec A n
tail-vec (x :: v) = v

{- 6.4 Concatenation -}
concat-vec : {A : Set} → {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
concat-vec [] v2 = v2
concat-vec (x :: v1) v2 = x :: (concat-vec v1 v2)

{- 6.5 Reversal -}
snoc-vec : {A : Set} → {n : ℕ} → A → Vec A n → Vec A (suc n)
snoc-vec a [] = a :: []
snoc-vec a (x :: v) = x :: (snoc-vec a v)

rev-vec : {A : Set} → {n : ℕ} → Vec A n → Vec A n
rev-vec [] = []
rev-vec (x :: v) = snoc-vec x (rev-vec v)

{- 6.6 Accessing an element -}
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} (i : Fin n) → Fin (suc n)

{- 6.7 Zipping -}
open import Data.Product hiding (zip)

zip-vec : {A : Set} → {n : ℕ} → Vec A n → Vec A n → Vec (A × A) n
zip-vec [] [] = []
zip-vec (x₁ :: y₁) (x₂ :: y₂) = (x₁ , x₂) :: (zip-vec y₁ y₂)
