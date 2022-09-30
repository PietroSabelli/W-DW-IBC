
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit     -- Unit type with η
open import Constructors.WP-types


module Equivalences.WP-give-W (A : Set) (B : A → Set) where

  W' : Set
  W' = WP (λ _ a _ → B a) tt

  sup' : (a : A) → (f : B a → W') → W'
  sup' a f = ind tt a λ { tt b → f b }

  W-rec' : (M : W' → Set₁)
           (c : (a : A) (f : B a → W') (h : (b : B a) → M (f b)) → M (sup' a f))
          → (w : W') → M w

  W-rec' M c (ind tt a f) = c a (λ b → f tt b ) λ b → W-rec' M c (f tt b)

  W-conv' : (M : W' → Set₁)
            (c : (a : A) (f : B a → W') (h : (b : B a) → M (f b)) → M (sup' a f))
            → (a : A) (f : B a → W') → W-rec' M c (sup' a f) ≡ c a f λ b → W-rec' M c (f b)

  W-conv' M c a f = refl
