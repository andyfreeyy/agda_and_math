{-# OPTIONS --without-K --exact-split --safe #-}

module Identity where

open import Basic_Types

-- ------------------------------------
-- the identity type, or path type
infix  1 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ (a : A) → a ≡ a

-- path induction
p-ind : ∀ {A : Set} {B : ∀ (x y : A) (p : x ≡ y) → Set} →
       (∀ (z : A) → B z z (refl z)) → ∀ (x y : A) (p : x ≡ y) → B x y p
p-ind f z z (refl z) = f z

-- the groupoid structure of path type
concat : ∀ {A : Set} → ∀ (x y : A) (p : x ≡ y) → ∀ (z : A) (q : y ≡ z) → x ≡ z
concat {A} = p-ind {A} {λ (x y : A) (p : x ≡ y) → ∀ (z : A) (q : y ≡ z) → x ≡ z}
                   (λ (w : A) → λ (z : A) (q : w ≡ z) → q)

infix  3 _∙_
_∙_ : ∀ {A : Set} {x y z : A} → ∀ (p : x ≡ y) (q : y ≡ z) → x ≡ z
_∙_ {_} {x} {y} {z} p q = concat x y p z q

inv : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → y ≡ x
inv {A} {x} {y} = p-ind {A} {λ (x y : A) (p : x ≡ y) → y ≡ x}
                 (λ (z : A) → refl z) x y

p-ass : ∀ {A : Set} {x y z w : A} → ∀ (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
        p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
p-ass {_} {x} {x} {x} {x} (refl x) (refl x) (refl x) =
      refl (((refl x) ∙ (refl x)) ∙ (refl x))

left_unit : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → (refl x) ∙ p ≡ p
left_unit {_} {x} {x} (refl x) = refl (refl x)

right_unit : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → p ∙ (refl y) ≡ p
right_unit {_} {x} {x} (refl x) = refl (refl x)
-- ------------------------------------
-- the action on paths
ap : ∀ {A B : Set} {x y : A} → ∀ (f : A → B) (p : x ≡ y) → f x ≡ f y
ap {A} {_} {x} {x} f (refl x) = refl (f x)

-- the transport action, which is action on dependent types
tr : ∀ {A : Set} {B : A → Set} → ∀ {x y : A} → ∀ (p : x ≡ y) → B x → B y
tr {A} {B} {x} {y} = p-ind {A} {λ (x y : A) (p : x ≡ y) → B x → B y}
                           (λ (z : A) (b : B z) → b) x y
-- If you think about this, this is not obvious from a classical point of view.
-- The existence of the transport function tells us that the dependent type
-- B : A → Set is always going to be continuous, since whenever we have a path
-- in the base A from x to y, and whenever we're given a point in B x, we can
-- construct a value in B y, using the path inthe base.

apd : ∀ {A : Set} {B : A → Set} → ∀ (f : (∀ (a : A) → B a)) →
      ∀ (x y : A) (p : x ≡ y) → tr {A} {B} {x} {y} p (f x) ≡ f y
apd {A} {B} f x x (refl x) = refl (tr {A} {B} {x} {x} (refl x) (f x))
-- notice here that, in the proof system of agda, the induction principle is
-- builtin for a data type, for their constructor is given expicitly. Hence,
-- one way to prove identity type is to use p-ind, which is itself proved by
-- agda using implicit path induction, or we can use agda's induction expicitly
-- which is the case when we construct apd and ass-p

-- path lifting
lift : ∀ {A : Set} {B : A → Set} → ∀ {x y : A} → ∀ (p : x ≡ y) → ∀ (b : B x) →
       (x , b) ≡ y , (tr {A} {B} p b)
lift {A} {B} {x} {x} (refl x) b = refl (x , b)
-- ------------------------------------
-- the following is some exercises
module Ex₁ where
  ex1 : ∀ {A : Set} {B : A → Set} {x y z : A} → ∀ (p : x ≡ y) (q : y ≡ z) →
        ∀ (b : B x) → (tr {A} {B} q (tr {A} {B} p b)) ≡ tr {A} {B} (p ∙ q) b
  ex1 {_} {_} {x} {x} {x} (refl x) (refl x) b = refl b
-- here is some note for agda: here if you don's supply in {A} {B} for tr, then
-- agda will complain that it cannot solve the constraint for something. This
-- is because, although you supply in p, which depends on x and y, and x and y
-- depends on A and B, but this dependence relation, though transitive, is not
-- known implicitly in agda, hence you should supply in {A} and {B} explicitly

  ex2 : ∀ {A : Set} {B : A → Set} {x y z : A} → ∀ (p : x ≡ y) (q : y ≡ z) →
        inv (p ∙ q) ≡ (inv q) ∙ (inv p)
  ex2 {_} {_} {x} {x} {x} (refl x) (refl x) = refl (refl x)
