{- --- 4. Lists --- -}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

open import Data.Nat
open import Relation.Binary.PropositionalEquality

{- 4.1 Length -}

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ l) = 1 + (length l)


{- 4.2 List reversal -}

concat : {A : Set} → List A → List A → List A
concat [] l = l
concat (x ∷ k) l = x ∷ (concat k l)

concat-length : {A : Set} → (k l : List A) → length (concat k l) ≡ (length k) + (length l)
concat-length [] l = refl
concat-length (x ∷ k) l rewrite concat-length k l = refl

concat-assoc : {A : Set} → (j k l : List A) → concat (concat j k) l ≡ concat j (concat k l)
concat-assoc [] k l = refl
concat-assoc (x ∷ j) k l rewrite concat-assoc j k l = refl


{- 4.3 List reversal -}

snoc : {A : Set} → A -> List A → List A
snoc a [] = a ∷ []
snoc a (x ∷ l) = x ∷ (snoc a l)

rev : {A : Set} → List A → List A
rev [] = []
rev (x ∷ l) = snoc x (rev l)

snoc-length : {A : Set} → (a : A) → (l : List A) → length (snoc a l) ≡ suc (length l)
snoc-length a [] = refl
snoc-length a (x ∷ l) rewrite snoc-length a l = refl 

rev-length : {A : Set} → (l : List A) → (length (rev l)) ≡ (length l)
rev-length [] = refl
rev-length (x ∷ l) rewrite snoc-length x (rev l) | rev-length l = refl

snoc-rev : {A : Set} → (a : A) → (l : List A) → rev (snoc a l) ≡ a ∷ (rev l)
snoc-rev a [] = refl
snoc-rev a (x ∷ l) rewrite snoc-rev a l = refl

double-rev : {A : Set} → (l : List A) → rev (rev l) ≡ l
double-rev [] = refl
double-rev (x ∷ l) rewrite snoc-rev x (rev l) | double-rev l = refl


{- 4.4 Filtering -}
open import Data.Bool

filter : {A : Set} → (p : A → Bool) → (l : List A) → List A
filter p [] = []
filter p (x ∷ l) with p x
filter p (x ∷ l) | false = filter p l
filter p (x ∷ l) | true = x ∷ (filter p l)

empty-list : {A : Set} → (l : List A) → filter (λ _ → false) l ≡ []
empty-list [] = refl
empty-list (x ∷ l) = empty-list l

identity-list : {A : Set} → (l : List A) → filter (λ _ → true) l ≡ l
identity-list [] = refl
identity-list (x ∷ l) rewrite identity-list l = refl
