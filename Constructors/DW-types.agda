
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

{-
  For the notation and the rules of dependent W-types we follow
  J. Emmenegger in "W-TYPES IN SETOIDS"
  the only difference is the elimination rule that here acts
  also towards large types.
-}
module Constructors.DW-types
  {I : Set}
  {N : I → Set}
  (Br : (i : I) → N i → Set)
  (ar : (i : I) → (n : N i) → Br i n → I)
  where

  data DW : I → Set where
    dsup : (i : I)
         → (n : N i)
         → (f : (b : Br i n) → DW (ar i n b))
         → DW i


  DW-rec : (C : (i : I) → DW i → Set₁)
                 (c : (i : I)
                      (n : N i)
                      (f : (b : Br i n) → DW (ar i n b))
                      (p : (b : Br i n) → C (ar i n b) (f b))
                      → C i (dsup i n f))
                → (i : I) (w : DW i)
                → C i w

  DW-rec C c i (dsup i n f) = c i n f (λ b → DW-rec C c (ar i n b) (f b))

  DW-conv :  (C : (i : I) → DW i → Set₁)
             (c : (i : I)
                  (n : N i)
                  (f : (b : Br i n) → DW (ar i n b))
                  (p : (b : Br i n) → C (ar i n b) (f b))
                  → C i (dsup i n f))
            → (i : I) (n : N i) (f : (b : Br i n) → DW (ar i n b))
            → DW-rec C c i (dsup i n f)
              ≡
              c i n f (λ b → DW-rec C c (ar i n b) (f b))

  DW-conv C c i n f = refl
