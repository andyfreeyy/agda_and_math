{-# OPTIONS --without-K --exact-split --safe #-}

module Identity where

open import Basic_Types

-- ------------------------------------
-- the identity type, or path type
infix  1 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ (a : A) → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}


-- path induction
p-ind : ∀ {A : Set} {B : ∀ (x y : A) (p : x ≡ y) → Set} →
       (∀ (z : A) → B z z (refl z)) → ∀ (x y : A) (p : x ≡ y) → B x y p
p-ind f z z (refl z) = f z
-- notice here that, in the proof system of agda, the induction principle is
-- builtin for a data type, for their constructor is given expicitly. Hence,
-- one way to prove identity type is to use p-ind, which is itself proved by
-- agda using implicit path induction, or we can use agda's induction expicitly
-- which is the case when we construct apd and ass-p

-- the groupoid structure of path type
concat : ∀ {A : Set} → ∀ (x y : A) (p : x ≡ y) → ∀ (z : A) (q : y ≡ z) → x ≡ z
concat {A} x x (refl x) x (refl x) = refl x

infix  3 _∙_
_∙_ : ∀ {A : Set} {x y z : A} → ∀ (p : x ≡ y) (q : y ≡ z) → x ≡ z
_∙_ {_} {x} {y} {z} p q = concat x y p z q

inv : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → y ≡ x
inv {_} {x} {x} (refl x) = refl x

-- the groupoid structure of identities, viewed as higher paths
p-ass : ∀ {A : Set} {x y z w : A} → ∀ (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
        p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
p-ass {_} {x} {x} {x} {x} (refl x) (refl x) (refl x) =
      refl (((refl x) ∙ (refl x)) ∙ (refl x))

left_unit : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → (refl x) ∙ p ≡ p
left_unit {_} {x} {x} (refl x) = refl (refl x)

right_unit : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → p ∙ (refl y) ≡ p
right_unit {_} {x} {x} (refl x) = refl (refl x)

rinv-unit : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → (inv p) ∙ p ≡ refl y
rinv-unit {_} {x} {x} (refl x) = refl (refl x)

linv-unit : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → p ∙ (inv p) ≡ refl x
linv-unit {_} {x} {x} (refl x) = refl (refl x)

invinv : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) → inv (inv p) ≡ p
invinv {_} {x} {x} (refl x) = refl (refl x)

-- ------------------------------------
-- loop spaces
Ω : ∀ {A : Set} (a : A) → Set
Ω {_} a = a ≡ a

-- commutativity on 2-dimensional loops
-- prove the commutativity by proving a general result in the groupoid
pwr : ∀ {A : Set} {a b c : A} {p q : a ≡ b} → ∀ (r : b ≡ c) → ∀ (α : p ≡ q) →
      p ∙ r ≡ q ∙ r
pwr {_} {_} {b} {b} {p} {p} (refl b) (refl p) = refl (p ∙ (refl b))

pwl : ∀ {A : Set} {a b c : A} {q r : b ≡ c} → ∀ (p : a ≡ b) → ∀ (β : q ≡ r) →
      p ∙ q ≡ p ∙ r
pwl {_} {_} {_} {_} {q} {q} p (refl q) = refl (p ∙ q)

_*_ : ∀ {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} →
      ∀ (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
_*_ {_} {_} {_} {_} {p} {q} {r} {s} α β = α∙r ∙ q∙β
  where α∙r : p ∙ r ≡ q ∙ r
        α∙r = pwr r α
        q∙β : q ∙ r ≡ q ∙ s
        q∙β = pwl q β

_*'_ : ∀ {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} →
       ∀ (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
_*'_ {_} {_} {_} {_} {p} {q} {r} {s} α β = p∙β ∙ α∙s
  where p∙β : p ∙ r ≡ p ∙ s
        p∙β = pwl p β
        α∙s : p ∙ s ≡ q ∙ s
        α∙s = pwr s α

pwr-ru : ∀ {A : Set} {a : A} (p : a ≡ a) (α : refl a ≡ p) →
         pwr (refl a) α ≡ α ∙ (inv (right_unit p))
pwr-ru {_} {_} (refl a) (refl (refl a)) = refl (refl (refl a))

pwl-lu : ∀ {A : Set} {a : A} (p : a ≡ a) (α : refl a ≡ p) →
         pwl (refl a) α ≡ α ∙ (inv (left_unit p))
pwl-lu {_} {_} (refl a) (refl (refl a)) = refl (refl (refl a))

*≡*' : ∀ {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} →
       ∀ (α : p ≡ q) (β : r ≡ s) → (α * β) ≡ (α *' β)
*≡*' {_} {a} {a} {a} {refl a} {refl a} {refl a} {refl a}
     (refl (refl a)) (refl (refl a))
     = refl ((refl ((refl a) ∙ (refl a))) ∙ (refl ((refl a) ∙ (refl a))))

∙≡* : ∀ {A : Set} {a : A} → ∀ (α β : Ω (refl a)) → α ∙ β ≡ α * β
∙≡* {_} {a} α β = inv (redua)
  where redul : α * β ≡ α ∙ (pwl (refl a) β)
        redul = (pwr (pwl (refl a) β) (pwr-ru (refl a) α)) ∙
                (pwr (pwl (refl a) β) (right_unit α))
        redua : α * β ≡ α ∙ β
        redua = (redul ∙ (pwl α (pwl-lu (refl a) β))) ∙ (pwl α (right_unit β))

*'≡∙ : ∀ {A : Set} {a : A} → ∀ (α β : Ω (refl a)) → α *' β ≡ β ∙ α
*'≡∙ {_} {a} α β = redua'
  where redul' : α *' β ≡ β ∙ (pwr (refl a) α)
        redul' = (pwr (pwr (refl a) α) (pwl-lu (refl a) β)) ∙
                 (pwr (pwr (refl a) α) (right_unit β))
        redua' : α *' β ≡ β ∙ α
        redua' = redul' ∙ ((pwl β (pwr-ru (refl a) α)) ∙ (pwl β (right_unit α)))

-- finally, we are able to prove that the higher path group is commutative
Ω²-comm : ∀ {A : Set} {a : A} → ∀ (α β : Ω (refl a)) → α ∙ β ≡ β ∙ α
Ω²-comm α β = ((∙≡* α β) ∙ (*≡*' α β)) ∙ (*'≡∙ α β)

-- ------------------------------------
-- functions behave functorially
-- the action on paths
ap : ∀ {A B : Set} {x y : A} → ∀ (f : A → B) (p : x ≡ y) → f x ≡ f y
ap {_} {_} {x} {x} f (refl x) = refl (f x)

-- ap acts like a functor
ap∙ : ∀ {A B : Set} {x y z : A} → ∀ (f : A → B) (p : x ≡ y) (q : y ≡ z) →
      ap f (p ∙ q) ≡ (ap f p) ∙ (ap f q)
ap∙ {_} {_} {x} {x} {x} f (refl x) (refl x) = inv (left_unit (refl (f x)))

apinv : ∀ {A B : Set} {x y : A} → ∀ (f : A → B) (p : x ≡ y) →
        ap f (inv p) ≡ inv (ap f p)
apinv {_} {_} {x} {x} f (refl x) = refl (refl (f x))

apcomp : ∀ {A B C : Set} {x y : A} → ∀ (f : A → B) (g : B → C) (p : x ≡ y) →
         ap g (ap f p) ≡ ap (comp g f) p
apcomp {_} {_} {_} {x} {x} f g (refl x) = refl (refl (g (f x)))

apid : ∀ {A : Set} {x y : A} → ∀ (p : x ≡ y) →
       ap id p ≡ p
apid {_} {x} {x} (refl x) = refl (refl x)

-- the transport action, which is action on dependent types
tr : ∀ {A : Set} {B : A → Set} → ∀ {x y : A} → ∀ (p : x ≡ y) → B x → B y
tr {A} {B} {x} {x} (refl x) = id

<<<<<<< HEAD
=======
trc : ∀ {A B : Set} {x y : A} (p : x ≡ y) (b : B) → tr {A} {λ x → B} p b ≡ b
trc {_} {_} {x} {x} (refl x) b = refl b
>>>>>>> a0dc66dca08059f740d9290f3d1cad1bb007d721
-- If you think about this, this is not obvious from a classical point of view.
-- The existence of the transport function tells us that the dependent type
-- B : A → Set is always going to be continuous, since whenever we have a path
-- in the base A from x to y, and whenever we're given a point in B x, we can
-- construct a value in B y, using the path in the base.

-- path lifting
lift : ∀ {A : Set} {B : A → Set} → ∀ {x y : A} → ∀ (p : x ≡ y) → ∀ (b : B x) →
       (x , b) ≡ y , (tr {A} {B} p b)
lift {A} {B} {x} {x} (refl x) b = refl (x , b)

-- the dependent mapping functor
<<<<<<< HEAD
apd : ∀ {A : Set} {B : A → Set} {x y : A} → ∀ (f : (∀ (a : A) → B a)) →
      ∀ (p : x ≡ y) → tr {A} {B} {x} {y} p (f x) ≡ f y
apd {A} {B} {x} {x} f (refl x) = refl (tr {A} {B} {x} {x} (refl x) (f x))

-- the dependent and non-dependent ap(d) is closely related
trc : ∀ {A B : Set} {x y : A} (p : x ≡ y) (b : B) → tr {A} {λ x → B} p b ≡ b
trc {_} {_} {x} {x} (refl x) b = refl b

-- and now we can prove the following:
apd≡ap : ∀ {A B : Set} {x y : A} →
         ∀ (f : A → B) (p : x ≡ y) → apd f p ≡ trc p (f x) ∙ (ap f p)
apd≡ap {_} {_} {x} {x} f (refl x) = refl (refl (f x))

-- some useful properties about transport
tr∙ : ∀ {A : Set} {B : A → Set} {x y z : A} → ∀ (p : x ≡ y) (q : y ≡ z) →
      ∀ (b : B x) → tr {A} {B} q (tr {A} {B} p b) ≡ tr {A} {B} (p ∙ q) b
tr∙ {_} {_} {x} {x} {x} (refl x) (refl x) b = refl b

trcomp : ∀ {A B : Set} {P : B → Set} {x y : A} → ∀ (f : A → B) (p : x ≡ y) →
         ∀ (b : P (f x)) → tr {A} {λ a → P (f a)} p b ≡ tr {B} {P} (ap f p) b
trcomp {_} {_} {_} {x} {x} f (refl x) b = refl b

trhi : ∀ {A : Set} {P Q : A → Set} {x y : A} → ∀ (f : ∀ (x : A) → P x → Q x) →
       ∀ (p : x ≡ y) (b : P x) → f y (tr {A} {P} p b) ≡ tr {A} {Q} p (f x b)
trhi {_} {_} {_} {x} {x} f (refl x) b = refl (f x b)
=======
apd : ∀ {A : Set} {B : A → Set} → ∀ (f : (∀ (a : A) → B a)) →
      ∀ (x y : A) (p : x ≡ y) → tr {A} {B} {x} {y} p (f x) ≡ f y
apd {A} {B} f x x (refl x) = refl (tr {A} {B} {x} {x} (refl x) (f x))

-- apd helps to construct a
>>>>>>> a0dc66dca08059f740d9290f3d1cad1bb007d721
