-- ---------------------------------
-- this is the agda file implementing my own work on logic, viz. a relational
-- framework for logic.
-- ---------------------------------

module RL where

-- this file use agda standard library

open import Agda.Builtin.Equality
open import Relation.Nullary
open import Data.Empty

-- ---------------------------------
-- Logical Frame
-- ---------------------------------

record Frame : Set₁ where
  field
    Φ : Set
    bot : Φ
    top : Φ
    _⇌_ : Φ → Φ → Set
    symm : ∀ (x y : Φ) → x ⇌ y → y ⇌ x
    alre : ∀ (x : Φ) → ¬ (x ≡ bot) → x ⇌ x
    ⊥-contra : ∀ (x : Φ) → ¬ (x ⇌ bot)
    ⊤-validi : ∀ (x : Φ) → ¬ (x ≡ bot) → (x ⇌ top)

self-cons→non-contra : {A : Frame} (x : Frame.Φ A) → Frame._⇌_ A x x → x ≡ (Frame.bot A) → ⊥
self-cons→non-contra {A} x p q rewrite q = Frame.⊥-contra A (Frame.bot A) p

module Example₁ where

  data tf : Set where
    𝟘x 𝟙x : tf

  data _↔_ : tf → tf → Set where
    t-t : 𝟙x ↔ 𝟙x

  symm-tf : ∀ (x y : tf) → x ↔ y → y ↔ x
  symm-tf 𝟙x 𝟙x t-t = t-t

  alre-tf : ∀ (x : tf) → ¬ (x ≡ 𝟘x) → x ↔ x
  alre-tf 𝟙x _ = t-t
  alre-tf 𝟘x p = ⊥-elim (p refl)

  𝟙x-validi : ∀ (x : tf) → ¬ (x ≡ 𝟘x) → (x ↔ 𝟙x)
  𝟙x-validi 𝟙x _  = t-t
  𝟙x-validi 𝟘x ¬p = ⊥-elim (¬p refl)

  𝟘x-contra : ∀ (x : tf) → ¬ (x ↔ 𝟘x)
  𝟘x-contra x ()

  tfFrame : Frame
  tfFrame = record { Φ        = tf
                   ; bot      = 𝟘x
                   ; top      = 𝟙x
                   ; _⇌_      = _↔_
                   ; symm     = symm-tf
                   ; alre     = alre-tf
                   ; ⊥-contra = 𝟘x-contra
                   ; ⊤-validi = 𝟙x-validi }

-- ---------------------------------
-- Logical Consequence
-- ---------------------------------

record _⊢_ {A : Frame} (a b : Frame.Φ A) : Set where
  field
    fromCons : ∀ (x : Frame.Φ A) → Frame._⇌_ A x a → Frame._⇌_ A x b

bot-cons : {A : Frame} (x : Frame.Φ A)
           → ∀ (y : Frame.Φ A) → Frame._⇌_ A y (Frame.bot A) → Frame._⇌_ A y x
bot-cons {A} x y p = ⊥-elim (Frame.⊥-contra A y p)

bot-to-every : {A : Frame} (x : Frame.Φ A) → _⊢_ {A} (Frame.bot A) x
bot-to-every {A} x = record { fromCons = bot-cons {A} x }

-- top-cons : {A : Frame} (x : Frame.Φ A)
--            → ∀ (y : Frame.Φ A) → Frame._⇌_ A y x → Frame._⇌_ A y (Frame.top A)
-- top-cons {A} x y p = {!   !}
--
-- top-from-every : {A : Frame} (x : Frame.Φ A) → _⊢_ {A} x (Frame.top A)
-- top-from-every {A} x = record { fromCons = {!   !} }

module Example₂ where
  open Example₁

  𝟘x-𝟙x-cons : ∀ (x : tf) → x ↔ 𝟘x → x ↔ 𝟙x
  𝟘x-𝟙x-cons x ()

  𝟘x⊢𝟙x : _⊢_ {tfFrame} 𝟘x 𝟙x
  𝟘x⊢𝟙x = record { fromCons = 𝟘x-𝟙x-cons }

  𝟘x⊢𝟙x-frombot : _⊢_ {tfFrame} 𝟘x 𝟙x
  𝟘x⊢𝟙x-frombot = bot-to-every {tfFrame} 𝟙x
