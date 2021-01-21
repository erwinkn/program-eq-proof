{- --- 3. Natural numbers --- -}

{- 3.1 Definition -}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{- 3.2 Addition -}
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{- 3.3 Multiplication -}
_*_ : ℕ → ℕ → ℕ
zero * b = zero
suc a * b = b + (a * b)

{- 3.4 Equality is a congruence for successor -}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_
   
suc-≡ : {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
suc-≡ refl = refl

{- 3.5 Some properties -}
zeroL : (n : ℕ) → zero + n ≡ n
zeroL n = refl

zeroR : (n : ℕ) → n + zero ≡ n
zeroR zero = refl
zeroR (suc n) = suc-≡ (zeroR n)

+-assoc : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
+-assoc zero n p = refl
+-assoc (suc m) n p = suc-≡ (+-assoc m n p)

one : ℕ
one = suc zero

+-assoc1 : (m n : ℕ) → ((m + n) + one) ≡ (m + (n + one))
+-assoc1 m n = +-assoc m n one

{- Falsity type, needed for the next property -}
data ⊥ : Set where

{- ¬ : Set → Set
¬ A = A → ⊥ -}

open import Relation.Nullary

suc-notzero : (n : ℕ) → ¬ (zero ≡ suc n)
suc-notzero n ()

{- 3.6 The recurrence principle -}
rec : (P : ℕ → Set) → (P zero) → ((n : ℕ) → (P n) → (P (suc n))) → ((n : ℕ) → P n)
rec p z h zero = z
rec p z h (suc n) = h n (rec p z h n)

{- 3.7 Properties of equality -}
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

p : {m n : ℕ} → (e : m ≡ n) → suc-≡ e ≡ cong suc e
p refl = refl

subst : {A : Set} (P : A → Set) → {x y : A} → x ≡ y → P x → P y
subst P refl p = p

{- 3.8 Commutativity of addition -}
+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = suc-≡ (+-suc m n)

+-commut : (m n : ℕ) → m + n ≡ n + m
+-commut m zero = zeroR m
+-commut m (suc n) = trans (+-suc m n) (suc-≡ (+-commut m n))

{- 3.9 Injectivity of successor -}
suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

{- 3.10 Decidability of equality -}
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

ℕ-≡-dec : (m n : ℕ) → (m ≡ n) ∨ ¬ (m ≡ n)
ℕ-≡-dec zero zero = left refl
ℕ-≡-dec zero (suc n) = right (suc-notzero n)
ℕ-≡-dec (suc m) zero = right λ ()
ℕ-≡-dec (suc m) (suc n) with ℕ-≡-dec m n
ℕ-≡-dec (suc m) (suc n) | left e = left (suc-≡ e)
ℕ-≡-dec (suc m) (suc n) | right e' = right λ x → e' (suc-inj x)

{- 3.11 Recurrence for equality -}
J : (A : Set) → (P : (x : A) → (y : A) → (p : x ≡ y) → Set) → (r : (x : A) → P x x refl) → (x : A) → (y : A) → (p : x ≡ y) → P x y p
J A P r x .x refl = r x


