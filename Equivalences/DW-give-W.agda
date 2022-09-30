
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Constructors.DW-types

module Equivalences.DW-give-W
  (A : Set) (B : A → Set)
  where

  -- Unit type without η
  data ⊤ : Set where
    tt : ⊤

  W' : Set
  W' = DW (λ _ a → B a) (λ _ _ _ → tt) tt

  sup' : (a : A) → (f : B a → W') → W'
  sup' a f = dsup tt a f

  W-rec' : (M : W' → Set₁)
           (c : (a : A) (f : B a → W') (h : (b : B a) → M (f b)) → M (sup' a f))
          → (w : W') → M w

  W-rec' M c (dsup tt n f) = c n f (λ b → W-rec' M c (f b))
