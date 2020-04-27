{-# OPTIONS --without-K --exact-split --safe #-}

module Contract where

open import Basic_Types
open import Identity
open import Homotopy_Equivalence

-- a contractable space means there is a point which is path-connected to any
-- other point in the same space

is_contr : Set → Set
is_contr A = Σ a ∶ A , (∀ (x : A) → a ≡ x)
