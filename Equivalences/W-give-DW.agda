
{-# OPTIONS --without-K --exact-split --safe #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Constructors.W-types

module Equivalences.W-give-DW
  {I : Set} {N : I → Set}
  (Br : (i : I) → N i → Set)
  (ar : (i : I) → (n : N i) → Br i n → I)
  where

  _×_ : (A B : Set) → Set
  _×_ A B = Σ A (λ _ → B)

  Free-tree : Set
  Free-tree = W z ꞉ (Σ I N) , Br (fst z) (snd z)

  is-legal : Free-tree → I → Set
  is-legal (sup (i , n) f) j = (∀ b → is-legal (f b) (ar i n b)) × (i ≡ j)

  DW' : I → Set
  DW' i = Σ Free-tree (λ w → is-legal w i)

  dsup' : (i : I) (n : N i) (f : (b : Br i n) → DW' (ar i n b)) → DW' i

  dsup' i n f = sup (i , n) (λ b → fst (f b)) ,
                (λ b → snd (f b)) ,
                refl

  DW-rec' : (C : (i : I) → DW' i → Set₁)
                 (c : (i : I)
                      (n : N i)
                      (f : (b : Br i n) → DW' (ar i n b))
                      (p : (b : Br i n) → C (ar i n b) (f b))
                      → C i (dsup' i n f))
                → (i : I) (w : DW' i)
                → C i w

  DW-rec' C c i (w , l) =
    W-rec
    ( λ w → ∀ i l → C i (w , l) )
    ( λ { (i , n) f h j (l , refl) → c i n (λ b → (f b) , (l b)) λ b → h b (ar i n b) (l b) } )
    w i l

  DW-conv' :  (C : (i : I) → DW' i → Set₁)
             (c : (i : I)
                  (n : N i)
                  (f : (b : Br i n) → DW' (ar i n b))
                  (p : (b : Br i n) → C (ar i n b) (f b))
                  → C i (dsup' i n f))
            → (i : I) (n : N i) (f : (b : Br i n) → DW' (ar i n b))
            → DW-rec' C c i (dsup' i n f)
              ≡
              c i n f (λ b → DW-rec' C c (ar i n b) (f b))

  DW-conv' C c i n f = refl
