open import Data.Product renaming (_×_ to _∧_)

×-comm : {A B : Set} → (A ∧ B) → (B ∧ A)
×-comm (fst , snd) = snd , fst


id : {A : Set} → A → A
id a = a

K : {A B : Set} → A → B → A
K a b = a

app : {A B : Set} → (A → B) → A → B
app f a = f a

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

comp : {A B C : Set} → (A → B) → (B → C) → (A → C)
comp ab bc = λ x → bc (ab x)

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S g f = λ x → g x (f x)


proj1 : {A B : Set} → (A ∧ B) → A
proj1 (fst , snd) = fst

proj2 : {A B : Set} → (A ∧ B) → B
proj2 (fst , snd) = snd

diagonal : {A B : Set} → A → (A ∧ A)
diagonal a = a , a

commut : {A B : Set} → (A ∧ B) → (B ∧ A)
commut (fst , snd) = snd , fst

curry1 : {A B C : Set} → (A ∧ B → C) → (A → B → C)
curry1 f = λ x x₁ → f (x , x₁)

curry2 : {A B C : Set} → (A → B → C) → (A ∧ B → C)
curry2 f (fst , snd) = f fst snd

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) ∧ (B → A)

currying : {A B C : Set} → (A ∧ B → C) ↔ (A → B → C)
currying = curry1 , curry2

distrib : {A B C : Set} → (A → (B ∧ C)) ↔ ((A → B) ∧ (A → C))
distrib = (λ x → (λ x₁ → proj1 (x x₁)) , λ x₁ → proj2 (x x₁)) , λ x x₁ → ((proj1 x) x₁) , ((proj2 x) x₁)


data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

or-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
or-elim (left x) = λ x₁ x₂ → x₁ x
or-elim (right x) = λ x₁ x₂ → x₂ x

or-comm : {A B : Set} → (A ∨ B) → (B ∨ A)
or-comm (left x) = right x
or-comm (right x) = left x

or-dist : {A B C : Set} → (A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C))
or-dist (fst , left x) = left (fst , x)
or-dist (fst , right x) = right (fst , x)


data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ A = A → ⊥

contr : {A B : Set} → (A → B) → (¬ B → ¬ A)
contr f = λ x x₁ → x (f x₁)

non-contr : {A : Set} → ¬ (A ∧ ¬ A)
non-contr (fst , snd) = snd fst

nni : {A : Set} → A → ¬ (¬ A)
nni a = λ x → x a

⊥-nne : ¬ (¬ ⊥) → ⊥
⊥-nne x = x ⊥-elim

¬-elim : {A B : Set} → ¬ A → A → B
¬-elim n a = ⊥-elim (n a)

nnlem : {A : Set} → ¬ (¬ (A ∨ ¬ A))
nnlem = (λ x → x (right λ y → x (left y)))

rp2 : {A : Set} → (A → ¬ A) → (¬ A → A) → ⊥
rp2 a na = nnlem (λ x → or-elim x (λ x₁ → a x₁ x₁) λ x₁ → x₁ (na x₁))


data ⊤ : Set where
  tt : ⊤

ti : {A : Set} → (⊤ → A) → A
ti f = f tt

dmnt : ¬ ⊤ → ⊥
dmnt f = f tt

dmtn : ⊥ → ¬ ⊤
dmtn = λ x x₁ → x


lem : Set₁
lem = (A : Set) → A ∨ ¬ A

nne : Set₁
nne = (A : Set) → ¬ (¬ A) → A

nne-lem : nne → lem
nne-lem x A = x (A ∨ ¬ A) nnlem

lem-nne : lem → nne
lem-nne x A y = or-elim (x A) (λ x₁ → x₁) λ x₁ → ¬-elim y x₁

_↔₁_ : (A B : Set₁) → Set₁
A ↔₁ B = (A → B) ∧ (B → A)

peirce : Set₁
peirce = (A B : Set) → ((A → B) → A) → A

lem-peirce : lem ↔₁ peirce
lem-peirce = (λ x A B x₁ → or-elim (x A) id λ x₂ → x₁ λ x₃ → ¬-elim x₂ x₃) , λ x A → x (A ∨ ¬ A) ⊥ λ x₁ → right λ x₂ → x₁ (left x₂)

nne-peirce : nne ↔₁ peirce
nne-peirce = (λ x A B x₁ → x A λ x₂ → x₂ (x₁ λ x₃ → ¬-elim x₂ x₃)) , (λ x A x₁ → x A ⊥ λ x₂ → ¬-elim x₁ x₂)
