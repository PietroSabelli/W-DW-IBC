
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Constructors.WP-types

module Equivalences.WP-give-▹
  {A : Set}
  (V : A → Set)
  (I : A → Set)
  (C : (a : A) → I a → A → Set)
  where

  infixr 1 _⊎_

  data _⊎_ (A : Set) (B : Set) : Set where
    inj₁ : (x : A) → A ⊎ B
    inj₂ : (y : B) → A ⊎ B

  data ⊥ : Set where

  N : A → Set
  N a = I a ⊎ V a

  R : (a : A) → N a → A → Set
  R a (inj₁ i) = C a i
  R a (inj₂ r) = λ _ → ⊥

  absurd : (a : A) → ⊥ → WP R a
  absurd a ()

  canonical : {a : A} → WP R a → Set
  canonical (ind _ (inj₁ i) f) = ∀ b r → canonical (f b r)
  canonical (ind _ (inj₂ r) f) = f ≡ absurd

  ▹' : A → Set
  ▹' a = Σ (WP R a) canonical

  rf' : (a : A) → V a → ▹' a
  rf' a r = ind a (inj₂ r) absurd ,
            refl

  tr' : (a : A) → (i : I a) → ((b : A) → C a i b → ▹' b) → ▹' a
  tr' a i f = (ind a (inj₁ i) (λ j r → fst (f j r))) ,
              λ b r → snd (f b r)

  ▹-rec' : (P : (a : A) → ▹' a → Set₁)
           (q₁ : (a : A) (r : V a) → P a (rf' a r))
           (q₂ : (a : A)
                 (i : I a)
                 (k : (b : A) → C a i b → ▹' b)
                 (f : (b : A) → (p : C a i b) → P b ((k b) p))
                 → P a (tr' a i k))
           → (a : A) (m : ▹' a)
           → P a m

  ▹-rec' P q₁ q₂ a (ind a (inj₂ r) absurd , refl) = q₁ a r

  ▹-rec' P q₁ q₂ a (ind a (inj₁ i) f , c) =
    q₂ a i
    (λ b r → (f b r) , (c b r))
    λ b r → ▹-rec' P q₁ q₂ b ((f b r) , (c b r))


  ▹-conv₁' : (P : (a : A) → ▹' a → Set₁)
          (q₁ : (a : A) (r : V a) → P a (rf' a r))
          (q₂ : (a : A)
                (i : I a)
                (k : (b : A) → C a i b → ▹' b)
                (f : (b : A) → (p : C a i b) → P b ((k b) p))
               → P a (tr' a i k))
         → (a : A) (r : V a)
         → ▹-rec' P q₁ q₂ a (rf' a r) ≡ q₁ a r

  ▹-conv₁' P q₁ q₂ a r = refl

  ▹-conv₂' : (P : (a : A) → ▹' a → Set₁)
          (q₁ : (a : A) (r : V a) → P a (rf' a r))
          (q₂ : (a : A)
                (i : I a)
                (k : (b : A) → C a i b → ▹' b)
                (f : (b : A) → (p : C a i b) → P b ((k b) p))
                → P a (tr' a i k))
         → (a : A) (i : I a) (r : (b : A) → C a i b → ▹' b)
         → ▹-rec' P q₁ q₂ a (tr' a i r) ≡ q₂ a i r λ b p → ▹-rec' P q₁ q₂ b (r b p)

  ▹-conv₂' P q₁ q₂ a i r = refl
