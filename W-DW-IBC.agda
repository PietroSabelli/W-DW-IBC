
{-# OPTIONS --without-K --exact-split --safe #-}

{-
  We work in the first-order fragment of MLTT formalized in
  https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes
-}
open import Universes public
open import HoTT-UF-Agda public

{-
  We define W-types, dependent W-types and
  a Curry-Howard presentation of inductively generated basic covers
  using Agda inductive definitions.
-}

data W {A : 𝓤₀ ̇} (B : A → 𝓤₀ ̇) : 𝓤₀ ̇ where
  sup : (a : A) → (f : B a → W B) → W B

-W : (X : 𝓤₀ ̇ ) (Y : X → 𝓤₀ ̇) → 𝓤₀ ̇
-W X Y = W Y

syntax -W X (λ x → y) = W x ꞉ X , y


{-
  For the notation and the rules of dependent W-types we follow
  J. Emmenegger. "W-TYPES IN SETOIDS"
-}
data DW
  {A : 𝓤₀ ̇}
  {N : A → 𝓤₀ ̇}
  (Br : (a : A) → N a → 𝓤₀ ̇)
  (ar : (a : A) → (n : N a) → Br a n → A)
  : A → 𝓤₀ ̇
  where
  dsup : (a : A)
       → (n : N a)
       → (f : (b : Br a n) → (DW Br ar) (ar a n b))
       → (DW Br ar) a


{-
  For the rules and the notation of inductive basic cover we refer to
  M. E. Maietti, S. Maschio, M. Rathjen.
    "A REALIZABILITY SEMANTICS FOR INDUCTIVE FORMAL
      TOPOLOGIES, CHURCH’S THESIS AND AXIOM OF CHOICE"

  Notice the reverse (with respect to the paper) direction of the triangle
  in order to first accept V as a parameter.
-}
data _[_,_]▹_
  {A : 𝓤₀ ̇}
  (V : A → 𝓤₀ ̇)
  (I : A → 𝓤₀ ̇)
  (C : (a : A) → I a → A → 𝓤₀ ̇)
  : A → 𝓤₀ ̇
  where
  rf : (a : A) → V a → V [ I , C ]▹ a
  tr : (a : A) → (i : I a) → ((b : A) → C a i b → V [ I , C ]▹ b) → V [ I , C ]▹ a


{-
  DW-types can be represented using W-types
-}
module W-give-DW
  {I : 𝓤₀ ̇} {N : I → 𝓤₀ ̇}
  (Br : (i : I) → N i → 𝓤₀ ̇)
  (ar : (i : I) → (n : N i) → Br i n → I)
  where

  Free-tree : 𝓤₀ ̇
  Free-tree = W z ꞉ (Σ i ꞉ I , N i) , Br (pr₁ z) (pr₂ z)

  is-legal : I → Free-tree → 𝓤₀ ̇
  is-legal root (sup (i , n) f) = (∀ b → is-legal (ar i n b) (f b)) × (i ≡ root)

  DW' : I → 𝓤₀ ̇
  DW' i = Σ w ꞉ Free-tree , is-legal i w

  dsup' : (i : I) (n : N i) (f : (b : Br i n) → DW' (ar i n b)) → DW' i

  dsup' i n f = sup (i , n) (λ b → pr₁ (f b)) ,
                (λ b → pr₂ (f b)) ,
                refl i

  rec' : (C : (i : I) → DW' i → 𝓤₀ ̇)
         (c : (i : I)
              (n : N i)
              (f : (b : Br i n) → DW' (ar i n b))
              (p : (b : Br i n) → C (ar i n b) (f b))
              → C i (dsup' i n f))
        → (i : I) (w : DW' i)
        → C i w

  rec' C c i (sup (i , n) f , l , refl i) =
    c i n (λ b → (f b) , (l b)) (λ b → rec' C c (ar i n b) (f b , l b))

  conv' : (C : (i : I) → DW' i → 𝓤₀ ̇)
          (c : (i : I) (n : N i) (f : (b : Br i n) → DW' (ar i n b))
              (p : (b : Br i n) → C (ar i n b) (f b))
              → C i (dsup' i n f))
          (i : I)
          (n : N i)
          (f : (b : Br i n) → DW' (ar i n b))
         → rec' C c i (dsup' i n f) ≡ c i n f (λ b → rec' C c (ar i n b) (f b))

  conv' C c i n f = refl _


{-
  Inductive basic covers can be represented using DW-types
-}
module DW-give-▹
  (A : 𝓤₀ ̇) (I : A → 𝓤₀ ̇)
  (C : (a : A) → I a → A → 𝓤₀ ̇)
  (V : A → 𝓤₀ ̇)
  where

  N : A → 𝓤₀ ̇
  N a = I a + V a

  Br : (a : A) → N a → 𝓤₀ ̇
  Br a (inl i) = Σ x ꞉ A , C a i x
  Br a (inr r) = 𝟘

  ar : (a : A) → (n : N a) → Br a n → A
  ar a (inl i) b = pr₁ b

  absurd : {A : 𝟘 → 𝓤 ̇} → (z : 𝟘) → A z
  absurd = λ ()

  canonical : {a : A} → DW Br ar a → 𝓤₀ ̇
  canonical (dsup _ (inr r) f) = absurd ≡ f
  canonical (dsup _ (inl i) f) = ∀ z → canonical (f z)

  ▹' : A → 𝓤₀ ̇
  ▹' a = Σ w ꞉ DW Br ar a , canonical w

  rf' : (a : A) → V a → ▹' a

  rf' a r = dsup a (inr r) absurd ,
            refl absurd

  tr' : (a : A) → (i : I a) → ((b : A) → C a i b → ▹' b) → ▹' a

  tr' a i r = dsup a (inl i) (λ z → pr₁ (r (pr₁ z) (pr₂ z))) ,
              λ z → pr₂ (r (pr₁ z) (pr₂ z))

  ind' : (P : (a : A) → ▹' a → 𝓤₀ ̇)
         (q₁ : (a : A) (r : V a) → P a (rf' a r))
         (q₂ : (a : A)
               (i : I a)
               (k : (b : A) → C a i b → ▹' b)
               (f : (b : A) → (p : C a i b) → P b ((k b) p))
               → P a (tr' a i k))
         → (a : A) (m : ▹' a)
         → P a m

  ind' P q₁ q₂ a (dsup a (inr r) absurd , refl _) = q₁ a r
  ind' P q₁ q₂ a (dsup a (inl i) f , l) =
    q₂ a i (λ b c → f (b , c) , l (b , c)) λ b c → ind' P q₁ q₂ b (f (b , c) , l (b , c))

  conv₁ : (P : (a : A) → ▹' a → 𝓤₀ ̇)
          (q₁ : (a : A) (r : V a) → P a (rf' a r))
          (q₂ : (a : A)
               (i : I a)
               (k : (b : A) → C a i b → ▹' b)
               (f : (b : A) → (p : C a i b) → P b ((k b) p))
               → P a (tr' a i k))
         → (a : A) (r : V a)
         → ind' P q₁ q₂ a (rf' a r) ≡ q₁ a r

  conv₁ P q₁ q₂ a r = refl _

  conv₂ : (P : (a : A) → ▹' a → 𝓤₀ ̇)
          (q₁ : (a : A) (r : V a) → P a (rf' a r))
          (q₂ : (a : A)
                (i : I a)
                (k : (b : A) → C a i b → ▹' b)
                (f : (b : A) → (p : C a i b) → P b ((k b) p))
                → P a (tr' a i k))
         → (a : A) (i : I a) (r : (b : A) → C a i b → ▹' b)
         → ind' P q₁ q₂ a (tr' a i r) ≡ q₂ a i r λ b p → ind' P q₁ q₂ b (r b p)

  conv₂ P q₁ q₂ a i r = refl _


{-
  The converse ***should*** also work.
  Namely, DW-types can be represented by inductive basic covers.
  Below we sketch a first attempt.
-}
module ▹-give-DW
  (I : 𝓤₀ ̇)
  (N : I → 𝓤₀ ̇)
  (Br : (i : I) → N i → 𝓤₀ ̇)
  (ar : (i : I) → (n : N i) → Br i n → I)
  where

  C : (i : I) (n : N i) → I → 𝓤₀ ̇
  C i n j = Σ b ꞉ Br i n , ar i n b ≡ j

  ∅ : I → Set
  ∅ i = 𝟘

  Step-DW' : I → 𝓤₀ ̇
  Step-DW' i = ∅ [ N , C ]▹ i

  alias : {i : I} {n : N i} (f : (j : I) → C i n j → Step-DW' j)
          → (j : I) → C i n j → Step-DW' j

  alias {i} {n} f j z =
    transport Step-DW' (pr₂ z) (f (ar i n (pr₁ z)) (pr₁ z , refl _))

  canonical : (i : I) → Step-DW' i → 𝓤₀ ̇

  canonical i (tr i n f) =
    (alias f ≡ f) × ∀ b → canonical (ar i n b) (f (ar i n b) (b , refl _))

  DW' : I → 𝓤₀ ̇
  DW' i = Σ w ꞉ Step-DW' i , canonical i w

  dsup' : (i : I) (n : N i) (f : (b : Br i n) → DW' (ar i n b)) → DW' i
  dsup' i n f = (tr i n (λ j z → transport Step-DW' (pr₂ z) (pr₁ (f (pr₁ z))))) ,
                refl _ ,
                λ b → pr₂ (f b)
