
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

module Constructors.WP-types
  {I : Set}
  {N : I → Set}
  (R : (i : I) → N i → I → Set)
  where

  data WP : I → Set where
    ind : (i : I) (n : N i) → ((j : I) → R i n j → WP j) → WP i

  WP-rec : (M : (i : I) → WP i → Set₁)
            (c : (i : I)
                 (n : N i)
                 (f : (j : I) → R i n j → WP j)
                 (h : (j : I) (r : R i n j) → M j (f j r))
                 → M i (ind i n f))
           → (i : I) (w : WP i) → M i w

  WP-rec M c i (ind i n f) = c i n f λ j r → WP-rec M c j (f j r)

  WP-conv : (M : (i : I) → WP i → Set₁)
            (c : (i : I)
                 (n : N i)
                 (f : (j : I) → R i n j → WP j)
                 (h : (j : I) (r : R i n j) → M j (f j r))
                 → M i (ind i n f))
           → (i : I) (n : N i) (f : (j : I) → R i n j → WP j)
           → WP-rec M c i (ind i n f) ≡ c i n f λ j r → WP-rec M c j (f j r)

  WP-conv M c i n f = refl
