{-# OPTIONS --without-K --exact-split --safe #-}

module Basic_Types where

-- Already in the builtin's of agda, there are Π types, which is ∀, and lambda
-- abstraction, which is λ{ } and function types, which is →.


-- ------------------------------------
-- Some operations for function types
-- The curly brackts ∀{} should be viewed as contexts.

-- identity function
id : ∀ {A : Set} → A → A
id = λ{ x → x }

-- function composition
comp : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
comp {A} {B} {C} = λ (f : B → C) (g : A → B) (x : A) → f (g x)
-- The judgemental equality of association of functions is builtin in agda,
-- i.e., all the rules of derivation in the basic language of type theory,
-- e.g., the β-, η- reduction is automatic in agda.

-- swapping the argument
swap : ∀ {A B : Set} {C : A → B → Set} →
      (∀ (a : A) (b : B) → C a b) → (∀ (b : B) (a : A) → C a b)
swap {A} {B} {C} = λ { p → λ (b : B) (a : A) → p a b }


-- ------------------------------------
-- the unit type
data 𝟙 : Set where
  ⋆ : 𝟙

𝟙-ind : ∀ {A : 𝟙 → Set} → ∀ (a : A ⋆) → ∀ (x : 𝟙) → A x
𝟙-ind {A} a = 𝟙-indhelper
  where 𝟙-indhelper : ∀ (x : 𝟙) → A x
        𝟙-indhelper ⋆ = a

-- ------------------------------------
-- the empty type
data 𝟘 : Set where

𝟘-ind : ∀ {A : 𝟘 → Set} → ∀ (x : 𝟘) → A x
𝟘-ind {A} ()

-- define negation
¬_ : ∀ (A : Set) → Set
¬ A = A → 𝟘

-- ------------------------------------
-- the boolean type
data 𝟚 : Set where
  tt ff : 𝟚

𝟚-ind : ∀ {A : 𝟚 → Set} → A ff → A tt → ∀ (x : 𝟚) → A x
𝟚-ind Aff _ ff = Aff
𝟚-ind _ Att tt = Att

-- ------------------------------------
-- natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- ℕ induction
ℕ-ind : ∀ {A : ℕ → Set} →
        ∀ (a : A 0) → (∀ (n : ℕ) → A n → A (succ n)) → ∀ (m : ℕ) → A m
ℕ-ind {A} a p = ℕ-indhelper
  where ℕ-indhelper : ∀ (m : ℕ) → A m
        ℕ-indhelper 0        = a
        ℕ-indhelper (succ n) = p n (ℕ-indhelper n)
-- From this exercise, we can actually see that the idea of induction is
-- builtin in agda, since we essentially use the induction builtin in agda
-- to prove ℕ-ind.

-- ℕ recursion, which is a special case for ℕ induction, where the type is not
-- dependent on ℕ
ℕ-rec : ∀ {A : Set} →
        ∀ (a : A) → (∀ (n : ℕ) → A → A) → ∀ (m : ℕ) → A
ℕ-rec {A} = ℕ-ind {λ { n → A }}

-- for example, we can use ℕ-rec to define addition
add : ℕ → ℕ → ℕ
add = ℕ-rec {ℕ → ℕ} (id {ℕ}) (λ (n : ℕ) (p : ℕ → ℕ) → comp succ p)

-- ------------------------------------
-- the sum type
record Σ (A : Set) (B : A → Set) : Set where
  constructor
    _,_
  field
    a : A
    b : B a

-- the two projections
π₁ : ∀ {A : Set} {B : A → Set} → Σ A B → A
π₁ (x , y) = x

π₂ : ∀ {A : Set} {B : A → Set} → ∀ (z : Σ A B) → B (π₁ z)
π₂ (x , y) = y

syntax Σ A (λ a → b) = Σ a ∶ A , b

-- Σ induction
Σ-ind : ∀ {A : Set} {B : A → Set} {P : Σ A B → Set} →
       (∀ (a : A) (b : B a) → P (a , b)) → ∀ (z : Σ A B) → P z
Σ-ind {A} {B} {P} = λ (f : ∀ (a : A) (b : B a) → P (a , b)) →
                    λ (z : Σ A B) → f (π₁ z) (π₂ z)

-- cartesion product type
_×_ : Set → Set → Set
A × B = Σ a ∶ A , B

×-ind : ∀ {A : Set} {B : Set} {P : A × B → Set} →
       (∀ (a : A) (b : B) → P (a , b)) → ∀ (z : A × B) → P z
×-ind {A} {B} {P} = Σ-ind {A} {λ (a : A) → B} {P}

-- ------------------------------------
-- the coproduct type

data _⊎_ (A : Set) (B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

⊎-ind : ∀ {A : Set} {B : Set} {P : A ⊎ B → Set} →
       (∀ (a : A) → P (inl a)) → (∀ (b : B) → P (inr b)) →
        ∀ (u : A ⊎ B) → P u
⊎-ind f _ (inl x) = f x
⊎-ind _ g (inr y) = g y
