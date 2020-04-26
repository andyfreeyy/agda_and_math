-- ---------------------------------
-- This file proves all the essential theorems about integers in Chapter 1
-- ---------------------------------

module Integers where

open import Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _*_ ; _∸_ ; _≤_ ; _<_ ; _≥_ ; _>_ )
open import Data.Product
open import Agda.Builtin.Equality
open import Relation.Nullary
open import Data.Empty

-- proposition 1.6.2

data dvi : ℕ → ℕ → Set where
  mul : ∀ {m n} → ∃[ p ] (m * p ≡ n) → dvi m n

Prop1.6.2(a) : ∀ (u v : ℕ) → u * v ≡ 1 → (u ≡ 1 , v ≡ 1)
Prop1.6.2(a) u v p = (h , f)
  where
  h : u ≡ 1
  h =
