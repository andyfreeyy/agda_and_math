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
whis-f : ∀ {A B C : Set} {f g : A → B} → ∀ (h : B → C) → ∀ (H : f ~ g) →
         (comp h f) ~ (comp h g)
whis-f {A} h H = λ (x : A) → ap h (H x)

whis-h : ∀ {A B C : Set} {g h : B → C} → ∀ (H : g ~ h) → ∀ (f : A → B) →
         (comp g f) ~ (comp h f)
whis-h {A} H f = λ (x : A) → H (f x)


-- ------------------------------------
-- Bi-invertible maps
-- given f : A → B, whether f has a section
sec : ∀ {A B : Set} → ∀ (f : A → B) → Set
sec {A} {B} f = Σ g ∶ (B → A) , (id ~ comp f g)

-- given f : A → B, whether f has a retraction
retr : ∀ {A B : Set} → ∀ (f : A → B) → Set
retr {A} {B} f = Σ h ∶ (B → A) , (id ~ comp h f)

-- equivalence
is_equ : ∀ {A B : Set} → ∀ (f : A → B) → Set
is_equ f = sec f × retr f

-- the equivalence type between to types
_≃_ : ∀ (A B : Set) → Set
A ≃ B = Σ f ∶ (A → B) , is_equ f
-- notice the implementation here is really succinct, for it voids the use of
-- a record type, which is very hard to use. All the implicit use of a record
-- type goes into the definition of a Σ type, and we have its constructor
-- available.

-- an invertible map
is_inver : ∀ {A B : Set} → ∀ (f : A → B) → Set
is_inver {A} {B} f = Σ g ∶ (B → A) , ((id ~ comp f g) × (id ~ comp g f))

-- the left inverse and right inverse of a function is homotopic
eq→hp : ∀ {A B : Set} {f : A → B} → ∀ (p : is_equ f) → π₁ (π₁ p) ~ π₁ (π₂ p)
eq→hp {_} {B} (s , t) = λ (y : B) → (π₂ t (π₁ s y)) ∙ inv (ap (π₁ t) (π₂ s y))

-- the right inverse of an equivalence map is also a left inverse
eq→r→l : ∀ {A B : Set} {f : A → B} → ∀ (p : is_equ f) → id ~ comp (π₁ (π₁ p)) f
eq→r→l {A} {_} {f} (s , t) = λ (x : A) → π₂ t x ∙ inv (eq→hp (s , t) (f x))

-- combining the following lemmas, we can prove that an equivalence map can
-- be assigned an invertible structure
eq→inver : ∀ {A B : Set} {f : A → B} → ∀ (p : is_equ f) → is_inver f
eq→inver (s , t) = (π₁ s , (π₂ s , eq→r→l (s , t)))
-- it should be noticed that there are other ways to assign an invertible
-- structure on f, here we choose to provide its right inverse as its inverse


-- ------------------------------------
-- the identity type of a Σ-type
pair_eq : ∀ {A : Set} {B : A → Set} → ∀ (s t : Σ A B) → s ≡ t →
          Σ α ∶ (π₁ s ≡ π₁ t) , (tr {A} {B} α (π₂ s) ≡ π₂ t)
pair_eq s s (refl s) = (refl (π₁ s) , refl (π₂ s))

-- this equality is indeed an equivalence
-- is_pari_eq_equ : ∀ {A : Set} {B : A → Set} {s t : Σ A B} →
--                  is_equ (pair_eq s t)
-- is_pari_eq_equ =
