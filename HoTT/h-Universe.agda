{-# OPTIONS --without-K --exact-split --safe #-}

module h-Universe where

open import Basic_Types

record 𝓤 : Set₁ where
  field
    El : ∀ (X : Set) → Set
