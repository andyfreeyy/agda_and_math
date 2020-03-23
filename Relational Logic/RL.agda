-- ---------------------------------
-- this is the agda file implementing my own work on logic, viz. a relational
-- framework for logic.

-- These codes have been checked by Agda 2.6.0
-- ---------------------------------

module RL where

-- this file use agda standard library

open import Agda.Builtin.Equality
open import Relation.Nullary
open import Data.Empty
open import Data.Product

-- ---------------------------------
-- Logical Frame
-- ---------------------------------
record Frame : Set₁ where
  field
    Φ : Set -- the set of language
    bot : Φ -- contradiction
    top : Φ -- validity
    _⇌_ : Φ → Φ → Set -- ⇌ is interpreted as consistency relation
    symm : ∀ (x y : Φ) → x ⇌ y → y ⇌ x -- ⇌ is symmetric
    alre : ∀ (x : Φ) → ¬ (x ≡ bot) → x ⇌ x -- except for ⊥, ⇌ is reflexive
    ⊥-contra : ∀ (x : Φ) → ¬ (x ⇌ bot) -- ⊥ is in-⇌ with any x∈Φ
    ⊤-validi : ∀ (x : Φ) → ¬ (x ≡ bot) → (x ⇌ top) -- ⊤ ⇌ everything e.x. ⊥

substitution : {A : Frame} (x y z : Frame.Φ A) -- ∀x,y,z∈Φ.(x≡y ∧ x⇌z → y⇌z)
               → x ≡ y → Frame._⇌_ A x z → Frame._⇌_ A y z
substitution {A} x y z p q rewrite p = q

cons→non-contra : {A : Frame} (x : Frame.Φ A) -- ∀x∈Φ.(∃y∈Φ.(x⇌y) → x≠⊥)
                  → ∃[ y ] Frame._⇌_ A x y → ¬ (x ≡ Frame.bot A)
cons→non-contra {A} x (y , f) q = Frame.⊥-contra A y w
  where
  s : Frame._⇌_ A (Frame.bot A) y
  s = substitution {A} x (Frame.bot A) y q f
  w : Frame._⇌_ A y (Frame.bot A)
  w = Frame.symm A (Frame.bot A) y s

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

  tfFrame : Frame -- the smallest possible normal frame
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
record _⊢_ {A : Frame} (a b : Frame.Φ A) : Set where -- logical consequence
  field -- a⊢b ⇔ ∀x∈Φ.(x⇌a → x⇌b)
    fromCons : ∀ (x : Frame.Φ A) → Frame._⇌_ A x a → Frame._⇌_ A x b

-- ---------------------------------
-- properties of ⊢
refl-⊢ : {A : Frame} (a : Frame.Φ A) → _⊢_ {A} a a -- reflexive
refl-⊢ {A} a = record { fromCons = p }
  where
  p : ∀ (x : Frame.Φ A) → Frame._⇌_ A x a → Frame._⇌_ A x a
  p x q = q

trans-⊢ : {A : Frame} (a b c : Frame.Φ A) -- transitive
          → _⊢_ {A} a b → _⊢_ {A} b c → _⊢_ {A} a c
trans-⊢ {A} a b c p q = record { fromCons = f }
  where
  f : ∀ (x : Frame.Φ A) → Frame._⇌_ A x a → Frame._⇌_ A x c
  f x h = _⊢_.fromCons q x (_⊢_.fromCons p x h)
-- ---------------------------------

-- ---------------------------------
-- ∀x∈Φ.(⊥⊢x)
bot-cons : {A : Frame} (x : Frame.Φ A) -- ∀x∈Φ.∀y∈Φ.(y⇌⊥ → y⇌x)
           → ∀ (y : Frame.Φ A) → Frame._⇌_ A y (Frame.bot A) → Frame._⇌_ A y x
bot-cons {A} x y p = ⊥-elim (Frame.⊥-contra A y p)

bot-to-every : {A : Frame} (x : Frame.Φ A) → _⊢_ {A} (Frame.bot A) x
bot-to-every {A} x = record { fromCons = bot-cons {A} x }
-- ---------------------------------

-- ---------------------------------
-- ∀x∈Φ.(x⊢⊤)
top-cons : {A : Frame} (y x : Frame.Φ A) -- ∀y∈Φ.∀x∈Φ.(x⇌y → x⇌⊤)
            → Frame._⇌_ A x y → Frame._⇌_ A x (Frame.top A)
top-cons {A} y x p = Frame.⊤-validi A x (cons→non-contra {A} x (y , p))

top-from-every : {A : Frame} (x : Frame.Φ A) → _⊢_ {A} x (Frame.top A)
top-from-every {A} x = record { fromCons = top-cons {A} x }
-- ---------------------------------

-- ---------------------------------
-- the criteria for a Reasoning frame
-- ---------------------------------
record Reasoning (A : Frame) : Set₁ where
  field -- basically, reas says every consistent pair is testified
    reas : ∀ (x y : Frame.Φ A) → Frame._⇌_ A x y
           → ∃[ z ] ((¬ (z ≡ Frame.bot A)) × ((_⊢_ {A} z x) × (_⊢_ {A} z y)))
