
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Constructors.DW-types

module Equivalences.DW-give-WP
  {I : Set}
  {N : I → Set}
  (R : (i : I) → N i → I → Set)
  where

  Br : (i : I) → N i → Set
  Br i n = Σ I (R i n)

  ar : (i : I) (n : N i) → Br i n → I
  ar i n (j , r) = j

  WP' : I → Set
  WP' = DW Br ar

  ind' : (i : I) (n : N i) → ((j : I) → R i n j → WP' j) → WP' i

  ind' i n f = dsup i n λ b → f (ar i n b) (snd b)

  WP-rec' : (M : (i : I) → WP' i → Set₁)
            (c : (i : I)
                 (n : N i)
                 (f : (j : I) → R i n j → WP' j)
                 (h : (j : I) (r : R i n j) → M j (f j r))
                 → M i (ind' i n f))
           → (i : I) (w : WP' i) → M i w

  WP-rec' M c i (dsup i n f) = c i n (λ j z → f (j , z)) (λ j r → WP-rec' M c j (f (j , r)))

  WP-conv' : (M : (i : I) → WP' i → Set₁)
             (c : (i : I)
                 (n : N i)
                 (f : (j : I) → R i n j → WP' j)
                 (h : (j : I) (r : R i n j) → M j (f j r))
                 → M i (ind' i n f))
           → (i : I) (n : N i) (f : (j : I) → R i n j → WP' j)
           → WP-rec' M c i (ind' i n f) ≡ c i n f λ j r → WP-rec' M c j (f j r)

  WP-conv' M c i n f = refl
