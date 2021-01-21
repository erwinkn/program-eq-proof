open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.List hiding (length ; head)

{- --- 1. Order on natural numbers --- -}
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}                 → zero  ≤ n
  s≤s : {m n : ℕ} (m≤n : m ≤ n) → suc m ≤ suc n

{- 1.1 Compatibility with successor -}
≤-pred : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
≤-pred (s≤s i) = i

≤-suc : {m n : ℕ} → (m ≤ n) → suc m ≤ suc n
≤-suc i = s≤s i

{- 1.2 Reflexivity -}
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

{- 1.3 Transitivity -}
≤-trans : {m n p : ℕ} → (m ≤ n) → (n ≤ p) → (m ≤ p)
≤-trans z≤n i2 = z≤n
≤-trans (s≤s i1) (s≤s i2) = ≤-suc (≤-trans i1 i2)

{- 1.4 Totality -}
_≤?_ : (m n : ℕ) → (m ≤ n) ∨ (n ≤ m)
zero ≤? n = left z≤n
suc m ≤? zero = right z≤n
suc m ≤? suc n with m ≤? n
... | left e = left (≤-suc e)
... | right e = right (≤-suc e)

{- --- 2. Insertion sort --- -}

{- 2.1 Insertion -}
insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (x₁ ∷ l) with x ≤? x₁
... | left e = x ∷ (x₁ ∷ l)
... | right e = x₁ ∷ (insert x l)

{- 2.2 Sorting -}
sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ l) = insert x (sort l)

test : List ℕ
test = sort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

{- 2.3 The bounded below predicate -}
data _≤*_ : ℕ → List ℕ → Set where
  [] : {x : ℕ} → x ≤* []
  _∷_ : {x y : ℕ} → {l : List ℕ} → (x ≤ y) → (x ≤* l) → (x ≤* (y ∷ l))

{- 2.4 The sorted predicate -}
data sorted : (l : List ℕ) → Set where
  [] : sorted []
  _∷_ : {x : ℕ} → {l : List ℕ} → (x ≤* l) → sorted l → (sorted (x ∷ l))

{- 2.5 Insert is sorting -}

≤*-trans : {x y : ℕ} → (l : List ℕ) → x ≤ y → y ≤* l → x ≤* l
≤*-trans [] x≤y y≤*l = []
≤*-trans (x₁ ∷ l) x≤y (y≤x₁ ∷ y≤*l) = ≤-trans x≤y y≤x₁ ∷ ≤*-trans l x≤y y≤*l

sorted-lemma : {x y : ℕ} → (l : List ℕ) → x ≤ y → sorted (y ∷ l) → x ≤* (y ∷ l)
sorted-lemma l x≤y (y≤*l ∷ s) = x≤y ∷ (≤*-trans l x≤y y≤*l)

insert-lemma : (x y : ℕ) → (l : List ℕ) → y ≤ x → y ≤* l → y ≤* insert x l
insert-lemma x y [] y≤x y≤*l = y≤x ∷ []
insert-lemma x y (x₁ ∷ l) y≤x (y≤x₁ ∷ y≤*l) with x ≤? x₁
... | right x₁≤x = y≤x₁ ∷ insert-lemma x y l y≤x y≤*l
... | left x≤x₁ = y≤x ∷ (y≤x₁ ∷ y≤*l)

insert-sorting : (x : ℕ) → (l : List ℕ) → sorted l → sorted (insert x l)
insert-sorting x [] s = [] ∷ []
insert-sorting x (y ∷ l) (y≤*l ∷ s) with x ≤? y
... | left x≤y = (x≤y ∷ (≤*-trans l x≤y y≤*l)) ∷ (y≤*l ∷ s)
... | right y≤x = insert-lemma x y l y≤x y≤*l ∷ (insert-sorting x l s)

{- 2.6 Sort is sorting -}
sort-sorting : (l : List ℕ) → sorted (sort l)
sort-sorting [] = []
sort-sorting (x ∷ l) = insert-sorting x (sort l) (sort-sorting l)

{- 2.7 The problem of specification -}

{- Empty lists are always sorted, so always return an empty list -}
f : List ℕ → List ℕ
f l = []

f-sorting : (l : List ℕ) → sorted (f l)
f-sorting _ = []

{- 2.8 Intrinsic approach -}
mutual
  data Sorted : Set where
    nil : Sorted
    cons : (x : ℕ) → (l : Sorted) → x ≤ (head x l) → Sorted
    
  head : ℕ → Sorted → ℕ
  head d nil = d
  head d (cons x l x₁) = x

mutual
  insert' : (x : ℕ) → Sorted → Sorted
  insert' x nil = nil
  insert' x (cons x₁ l x₁≤hd) with x ≤? x₁
  ... | left x≤x₁ = cons x (cons x₁ l x₁≤hd) x≤x₁
  ... | right x₁≤x = cons x₁ (insert' x l) (ins-lemma x x₁ l x₁≤x x₁≤hd)

  {- In other words, y ≤ x and y ≤* l gives us y ≤* (insert x l) -}
  ins-lemma : (x y : ℕ) → (l : Sorted) → y ≤ x → y ≤ head y l → y ≤ head y (insert' x l)
  ins-lemma x y nil y≤x y≤hd = ≤-refl y
  ins-lemma x y (cons x₁ l x₁≤hd) y≤x y≤hd with x ≤? x₁
  ... | left x≤x₁ = y≤x
  ... | right x₁≤x = y≤hd


sort' : (l : List ℕ) → Sorted
sort' [] = nil
sort' (x ∷ l) = insert' x (sort' l)


{- --- 4. Merge sort --- -}

{- 4.1 Splitting -}
split : {A : Set} → List A → List A × List A
split [] = [] , []
split (x ∷ []) = (x ∷ []) , []
split (x ∷ y ∷ l) =
  let (l₁ , l₂) = split l in
  x ∷ l₁ , y ∷ l₂

test-split : List ℕ × List ℕ
test-split = split (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

{- 4.2 Merging -}
merge : (l m : List ℕ) → List ℕ
merge [] m = m
merge l [] = l
merge (x ∷ l) (y ∷ m) with x ≤? y
... | left x≤y = x ∷ y ∷ (merge l m)
... | right y≤x = y ∷ x ∷ (merge l m)

{- 4.3 Sorting -}

{-# TERMINATING #-}
mergesort : List ℕ → List ℕ
mergesort [] = []
mergesort (x ∷ []) = x ∷ []
mergesort l =
  let (l₁ , l₂) = split l in
  merge (mergesort l₁) (mergesort l₂)

test-merge : List ℕ
test-merge = mergesort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

{- 4.4 Splitting is decreasing -}
data _<_ : ℕ → ℕ → Set where
  s<s : {m n : ℕ} (m<n : suc m ≤ n) → m < n

length : {A : Set} (l : List A) → ℕ
length [] = zero
length (x ∷ l) = suc (length l)

test-length : ℕ
test-length = length (4 ∷ [])


split₁-lemma : {A : Set} → {x : A} → (l : List A) → length (fst (split (x ∷ l))) ≤ suc (length (fst (split l)))
split₁-lemma [] = ≤-refl 1
split₁-lemma (_ ∷ []) = s≤s z≤n
split₁-lemma (_ ∷ _ ∷ l) = s≤s (split₁-lemma l)

{- This is strange, Agda's pattern matching shouldn't accept the `x ∷ []` case -}
<-split₁ : {A : Set} → (x y : A) → (l : List A)
                    → length (fst (split (x ∷ y ∷ l))) < length (x ∷ y ∷ l)
<-split₁ x y [] = s<s (≤-refl 2)
<-split₁ x y (z ∷ l) with <-split₁ x y l
... | s<s h = s<s (s≤s (≤-trans (s≤s (split₁-lemma l)) h))

split₂-lemma : {A : Set} → {x : A} → (l : List A) → length (snd (split (x ∷ l))) ≤ suc (length (snd (split l)))
split₂-lemma [] = z≤n
split₂-lemma (_ ∷ []) = s≤s z≤n
split₂-lemma (_ ∷ _ ∷ l) = s≤s (split₂-lemma l)

{- This is strange, Agda's pattern matching shouldn't accept the `x ∷ []` case -}
<-split₂ : {A : Set} → (x y : A) → (l : List A)
                    → length (snd (split (x ∷ y ∷ l))) < length (x ∷ y ∷ l)
<-split₂ x y [] = s<s (≤-refl 2)
<-split₂ x y (z ∷ l) with <-split₂ x y l
... | s<s h = s<s (s≤s (≤-trans (s≤s (split₂-lemma l)) h))


{- 4.5 The fuel definition of merge -}
mergesort-fuel : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → List ℕ
mergesort-fuel zero l l≤n = l
mergesort-fuel n [] l≤n = []
mergesort-fuel n (x ∷ []) l≤n = x ∷ []
mergesort-fuel (suc n) (x ∷ y ∷ l) l≤n = let (l₁ , l₂) = split (x ∷ y ∷ l) in
  merge (mergesort-fuel n l₁ {!!}) (mergesort-fuel n l₂ {!!})
