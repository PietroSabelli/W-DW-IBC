
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality

{-
  For the notation and the rules of inductive basic cover in MLTT we refer to
  M. E. Maietti, S. Maschio, M. Rathjen.
    "A REALIZABILITY SEMANTICS FOR INDUCTIVE FORMAL
      TOPOLOGIES, CHURCH’S THESIS AND AXIOM OF CHOICE"

  Notice the reverse direction of the triangle
  in order to first accept V as a parameter.
-}
module Constructors.▹-types where

data _[_,_]▹_
  {A : Set}
  (V : A → Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  : A → Set
  where
  rf : (a : A) → V a → V [ I , C ]▹ a
  tr : (a : A) → (i : I a) → ((b : A) → C a i b → V [ I , C ]▹ b) → V [ I , C ]▹ a

module _
  {A : Set}
  (V : A → Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  where

  ▹-rec : (P : (a : A) → V [ I , C ]▹ a → Set₁)
          (q₁ : (a : A) (r : V a) → P a (rf a r))
          (q₂ : (a : A)
                (i : I a)
                (k : (b : A) → C a i b → V [ I , C ]▹ b)
                (f : (b : A) → (p : C a i b) → P b ((k b) p))
                → P a (tr a i k))
           → (a : A) (m : V [ I , C ]▹ a)
           → P a m

  ▹-rec P q₁ q₂ a (rf a r) = q₁ a r
  ▹-rec P q₁ q₂ a (tr a i k) = q₂ a i k (λ b p → ▹-rec P q₁ q₂ b (k b p))

  ▹-conv₁ : (P : (a : A) → V [ I , C ]▹ a → Set₁)
          (q₁ : (a : A) (r : V a) → P a (rf a r))
          (q₂ : (a : A)
                (i : I a)
                (k : (b : A) → C a i b → V [ I , C ]▹ b)
                (f : (b : A) → (p : C a i b) → P b ((k b) p))
               → P a (tr a i k))
         → (a : A) (r : V a)
         → ▹-rec P q₁ q₂ a (rf a r) ≡ q₁ a r

  ▹-conv₁ P q₁ q₂ a r = refl

  ▹-conv₂ : (P : (a : A) → V [ I , C ]▹ a → Set₁)
            (q₁ : (a : A) (r : V a) → P a (rf a r))
            (q₂ : (a : A)
                  (i : I a)
                  (k : (b : A) → C a i b → V [ I , C ]▹ b)
                  (f : (b : A) → (p : C a i b) → P b ((k b) p))
                  → P a (tr a i k))
           → (a : A) (i : I a) (r : (b : A) → C a i b → V [ I , C ]▹ b)
           → ▹-rec P q₁ q₂ a (tr a i r) ≡ q₂ a i r λ b p → ▹-rec P q₁ q₂ b (r b p)

  ▹-conv₂ P q₁ q₂ a i r = refl
