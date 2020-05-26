{-# OPTIONS --without-K --exact-split --safe #-}

module Homotopy_Equivalence where

open import Basic_Types
open import Identity

-- ------------------------------------
-- In homotopy type theory, a homotopy is just a point-wise equality (path)
-- between to (dependent) functions f and g
infix  2 _~_

_~_ : ∀ {A : Set} {B : A → Set} → ∀ (f g : ∀ (x : A) → B x) → Set
_~_ {A} f g = ∀ (x : A) → f x ≡ g x

-- operations on homotopies, which give them groupoid-like structures
hp-refl : ∀ {A : Set} {B : A → Set} → ∀ (f : ∀ (a : A) → B a) → f ~ f
hp-refl {A} f = λ (x : A) → refl (f x)

hp-inv : ∀ {A : Set} {B : A → Set} {f g : ∀ (a : A) → B a} → f ~ g → g ~ f
hp-inv {A} H = λ (x : A) → inv (H x)

hp-concat : ∀ {A : Set} {B : A → Set} {f g h : ∀ (a : A) → B a} →
            f ~ g → g ~ h → f ~ h
hp-concat {A} H K = λ (x : A) → (H x) ∙ (K x)

-- naturality of homotopies
<<<<<<< HEAD
hpna : ∀ {A B : Set} {x y : A} → ∀ (p : x ≡ y) → ∀ (f g : A → B) → ∀ (H : f ~ g) →
       (H x) ∙ (ap g p) ≡ (ap f p) ∙ (H y)
hpna {_} {_} {x} {x} (refl x) f g H = (right_unit (H x)) ∙ (inv (left_unit (H x)))

=======


>>>>>>> a0dc66dca08059f740d9290f3d1cad1bb007d721
infix  3 _·_

_·_ : ∀ {A : Set} {B : A → Set} {f g h : ∀ (a : A) → B a} →
      f ~ g → g ~ h → f ~ h
H · K = hp-concat H K

hp-ass : ∀ {A : Set} {B : A → Set} {f g h k : ∀ (a : A) → B a} →
         ∀ (H : f ~ g) (K : g ~ h) (L : h ~ k) → H · (K · L) ~ (H · K) · L
hp-ass {A} H K L = λ (x : A) → p-ass (H x) (K x) (L x)

hp-left_unit : ∀ {A : Set} {B : A → Set} {f g : ∀ (a : A) → B a} →
               ∀ (H : f ~ g) → (hp-refl f) · H ~ H
hp-left_unit {A} H = λ (x : A) → left_unit (H x)

hp-right_unit : ∀ {A : Set} {B : A → Set} {f g : ∀ (a : A) → B a} →
                ∀ (H : f ~ g) → H · (hp-refl g) ~ H
hp-right_unit {A} H = λ (x : A) → right_unit (H x)

-- whiskering operations
whis-r : ∀ {A B C : Set} {f g : A → B} → ∀ (H : f ~ g) → ∀ (h : B → C) →
         (comp h f) ~ (comp h g)
<<<<<<< HEAD
whis-r {A} H h = λ (x : A) → ap h (H x)
=======
whis-f {A} h H = λ (x : A) → ap h (H x)
>>>>>>> a0dc66dca08059f740d9290f3d1cad1bb007d721

whis-l : ∀ {A B C : Set} {g h : B → C} → ∀ (H : g ~ h) → ∀ (f : A → B) →
         (comp g f) ~ (comp h f)
whis-l {A} H f = λ (x : A) → H (f x)

-- ------------------------------------
-- equivalences
-- first, let's consider quasi-equivalences
qinv : ∀ {A B : Set} → ∀ (f : A → B) → Set
qinv {A} {B} f = Σ g ∶ (B → A) , (((comp f g) ~ id) × ((comp g f) ~ id))

isequiv : ∀ {A B : Set} → ∀ (f : A → B) → Set
isequiv {A} {B} f = (Σ g ∶ (B → A) , ((comp f g) ~ id)) × (Σ h ∶ (B → A) , ((comp h f) ~ id))

isequivid : ∀ {A : Set} → isequiv (id {A})
isequivid {A} = ((id {A} , hp-refl (id {A})) , (id {A} , hp-refl (id {A})))

-- the relation between quasi-inverse and equivalence is as following:
q→e : ∀ {A B : Set} → ∀ (f : A → B) → qinv f → isequiv f
q→e f q = ((π₁ q , π₁ (π₂ q)) , (π₁ q , π₂ (π₂ q)))

e→q : ∀ {A B : Set} → ∀ (f : A → B) → isequiv f → qinv f
e→q {A} {B} f ((g , fgid) , (h , hfid)) = (comp h (comp f g) , (e→q1 , e→q2))
  where e→q1 : comp f (comp h (comp f g)) ~ id
        e→q1 = (whis-l {B} {A} {B} (whis-r {A} {A} {B} hfid f) g) · fgid
        e→q2 : comp (comp h (comp f g)) f ~ id
        e→q2 = (whis-l {A} {B} {A} (whis-r {B} {B} {A} fgid h) f) · hfid
-- the above two lemmas shows that quasi-equivalence and equivalence are
-- logically equivalent

-- ------------------------------------
-- type equivalence
infix  3 _≃_

_≃_ : ∀ (A B : Set) → Set
A ≃ B = Σ f ∶ (A → B) , (isequiv f)

-- type equivalence is an equivalence relation on Set
≃-refl : ∀ (A : Set) → A ≃ A
≃-refl A = id {A} , isequivid {A}

-- ------------------------------------
-- The higher groupoid structure of type formers
-- Cartesian product types
p×1 : ∀ {A B : Set} {x y : A × B} → x ≡ y → π₁ x ≡ π₁ y
p×1 {_} {_} {x} {x} (refl x) = refl (π₁ x)

p×2 : ∀ {A B : Set} {x y : A × B} → x ≡ y → π₂ x ≡ π₂ y
p×2 {_} {_} {x} {x} (refl x) = refl (π₂ x)

p≡p× : ∀ {A B : Set} {x y : A × B} → ∀ (p : x ≡ y) → (π₁ x ≡ π₁ y) × (π₂ x ≡ π₂ y)
p≡p× = λ p → (p×1 p , p×2 p)

p×≡p : ∀ {A B : Set} {x1 y1 : A} {x2 y2 : B} →
      ((x1 ≡ y1) × (x2 ≡ y2)) → (x1 , x2) ≡ (y1 , y2)
p×≡p {_} {_} {x1} {x1} {x2} {x2} (refl x1 , refl x2) = refl (x1 , x2)
