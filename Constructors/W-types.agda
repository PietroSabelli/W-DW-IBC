
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

module Constructors.W-types where

data W {A : Set} (B : A → Set) : Set where
  sup : (a : A) → (f : B a → W B) → W B

-W : (X : Set) (Y : X → Set) → Set
-W X Y = W Y

syntax -W X (λ x → y) = W x ꞉ X , y

W-rec : {A : Set} {B : A → Set}
        (M : W B → Set₁)
        (c : (a : A) (f : B a → W B) (h : (b : B a) → M (f b)) → M (sup a f))
        → (w : W B) → M w

W-rec M c (sup a f) = c a f λ b → W-rec M c (f b)

W-conv : {A : Set} {B : A → Set}
         (M : W B → Set₁)
         (c : (a : A) (f : B a → W B) (h : (b : B a) → M (f b)) → M (sup a f))
         → (a : A) (f : B a → W B) → W-rec M c (sup a f) ≡ c a f λ b → W-rec M c (f b)

W-conv M c a f = refl
