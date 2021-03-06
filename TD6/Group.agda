open import Relation.Binary.PropositionalEquality

record Group : Set₁ where
  field
    X : Set
    _·_ : X → X → X
    e : X
    i : X → X
    assoc  : (x y z : X) → (x · y) · z ≡ x · (y · z)
    unit-l : (x : X) → e · x ≡ x
    unit-r : (x : X) → x · e ≡ x
    inv-l  : (x : X) → i x · x ≡ e
    inv-r  : (x : X) → x · i x ≡ e

inv-u-l : {G : Group} → (x x' y : Group.X) → (x Group.· y) ≡ Group.e → (x' Group.· y) ≡ Group.e → x ≡ x'
inv-u-l x x' y p q = ?
