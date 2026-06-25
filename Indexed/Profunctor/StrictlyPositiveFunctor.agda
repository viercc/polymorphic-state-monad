{-# OPTIONS --without-K --safe #-}

open import Level
open import Function
  using (
    _∘_; _∘′_; _$_; id; const; constᵣ;
    case_of_
  )

open import Data.Product as Prod using () renaming (_,_ to pair)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit
open import Data.Empty

open import Data.Maybe using (Maybe; nothing; just; maybe; maybe′)

open import Relation.Binary.PropositionalEquality as ≡
   using (_≡_; _≗_)

open import Data.Irrelevant
   using (Irrelevant; _>>=_; _<*>_)
   renaming (map to irrmap; [_] to irr[_])
open import ExtensionalityUtil

open import Indexed.Profunctor
open import Indexed.Profunctor.Functor
open import Indexed.Profunctor.Sum
open import Indexed.Profunctor.Product

module Indexed.Profunctor.StrictlyPositiveFunctor (ext : Extensionality 1ℓ 1ℓ) where

open Ext1↓1↓ ext

open import Indexed.Profunctor.Fun {ℓ = 0ℓ} ext₀₀
open import Indexed.Profunctor.End ext

open Profunctor

-- Syntax of strictly positive functor
data SPos (I : Set) : Set₂ where
  idSP : SPos I
  constantSP : Profunctor 0ℓ I → SPos I
  sumSP : SPos I → SPos I → SPos I
  prodSP : SPos I → SPos I → SPos I
  kfunSP : Profunctor 0ℓ I → SPos I → SPos I

mapIndexSPos : ∀ {I J : Set} (f : I → J)
  → SPos I → SPos J
mapIndexSPos t idSP = idSP
mapIndexSPos t (constantSP A) = constantSP (mapIndex t A)
mapIndexSPos t (sumSP F₁ F₂) = sumSP (mapIndexSPos t F₁) (mapIndexSPos t F₂)
mapIndexSPos t (prodSP F₁ F₂) = prodSP (mapIndexSPos t F₁) (mapIndexSPos t F₂)
mapIndexSPos t (kfunSP A F) = kfunSP (mapIndex t A) (mapIndexSPos t F)

shiftSPos : ∀ {I : Set} → SPos I → SPos (Maybe I)
shiftSPos = mapIndexSPos just

-- Apply SPos to a Profunctor
module _ {I : Set} where
  ⟦_⟧ : SPos I → Profunctor 0ℓ I → Profunctor 0ℓ I
  ⟦ idSP ⟧ P = P
  ⟦ constantSP A ⟧ P = A
  ⟦ sumSP F₁ F₂ ⟧ P = ⟦ F₁ ⟧ P + ⟦ F₂ ⟧ P
  ⟦ prodSP F₁ F₂ ⟧ P = ⟦ F₁ ⟧ P × ⟦ F₂ ⟧ P
  ⟦ kfunSP A F ⟧ P = fun A (⟦ F ⟧ P)

-- ⟦_⟧ is functor *regarding any function P [ a , b ] -> Q [ a , b ]*,
-- not just natural transformations
module umap {I : Set} {a b : I → Set} where
  -- unnatural function
  arr : Profunctor 0ℓ I → Profunctor 0ℓ I → Set
  arr P Q = P [ a , b ] → Q [ a , b ]

  -- the "unnatural" or "uniform" map
  umap⟦_⟧ : ∀ (F : SPos I) (P Q : Profunctor 0ℓ I)
    → arr P Q → arr (⟦ F ⟧ P) (⟦ F ⟧ Q)
  umap⟦ idSP ⟧ _ _ α = α
  umap⟦ constantSP A ⟧ _ _ _ = id
  umap⟦ sumSP F₁ F₂ ⟧ P Q α = Sum.map (umap⟦ F₁ ⟧ P Q α) (umap⟦ F₂ ⟧ P Q α)
  umap⟦ prodSP F₁ F₂ ⟧ P Q α = Prod.map (umap⟦ F₁ ⟧ P Q α) (umap⟦ F₂ ⟧ P Q α)
  umap⟦ kfunSP A F ⟧ P Q α = (umap⟦ F ⟧ P Q α ∘′_) 

  umap⟦_⟧-cong : ∀ (F : SPos I) (P Q : Profunctor 0ℓ I) {α β : arr P Q}
    → (α ≗ β) → umap⟦ F ⟧ P Q α ≗ umap⟦ F ⟧ P Q β
  umap⟦ F ⟧-cong P Q {α} {β} eq = go F
    where
      go : ∀ (F' : SPos I) (fp : (⟦ F' ⟧ P) [ a , b ])
        → umap⟦ F' ⟧ P Q α fp ≡ umap⟦ F' ⟧ P Q β fp
      go idSP fp = eq fp
      go (constantSP _) _ = ≡.refl
      go (sumSP F₁ F₂) (Sum.inj₁ fp₁) = ≡.cong Sum.inj₁ (go F₁ fp₁)
      go (sumSP F₁ F₂) (Sum.inj₂ fp₂) = ≡.cong Sum.inj₂ (go F₂ fp₂)
      go (prodSP F₁ F₂) (pair fp₁ fp₂) = ≡.cong₂ pair (go F₁ fp₁) (go F₂ fp₂)
      go (kfunSP A F') a→fp = ext₀₀ λ a → go F' (a→fp a)

  umap⟦_⟧-id : ∀ (F : SPos I) (P : Profunctor 0ℓ I)
    → umap⟦ F ⟧ P P id ≗ id
  umap⟦ F ⟧-id P = go F
    where
      go : ∀ (F' : SPos I) (fp : (⟦ F' ⟧ P) [ a , b ])
        → umap⟦ F' ⟧ P P id fp ≡ fp
      go idSP _ = ≡.refl
      go (constantSP _) _ = ≡.refl
      go (sumSP F₁ F₂) (Sum.inj₁ fp₁) = ≡.cong Sum.inj₁ (go F₁ fp₁)
      go (sumSP F₁ F₂) (Sum.inj₂ fp₂) = ≡.cong Sum.inj₂ (go F₂ fp₂)
      go (prodSP F₁ F₂) (pair fp₁ fp₂) = ≡.cong₂ pair (go F₁ fp₁) (go F₂ fp₂)
      go (kfunSP A F') a→fp = ext₀₀ λ a → go F' (a→fp a)
  
  umap⟦_⟧-∘ : ∀ (F : SPos I) (P Q R : Profunctor 0ℓ I)
    → (qr : arr Q R) (pq : arr P Q)
    → umap⟦ F ⟧ P R (qr ∘′ pq) ≗ umap⟦ F ⟧ Q R qr ∘′ umap⟦ F ⟧ P Q pq
  umap⟦ F ⟧-∘ P Q R qr pq = go F
    where
      go : ∀ (F' : SPos I) (fp : (⟦ F' ⟧ P) [ a , b ])
        → umap⟦ F' ⟧ P R (qr ∘′ pq) fp ≡ umap⟦ F' ⟧ Q R qr (umap⟦ F' ⟧ P Q pq fp)
      go idSP _ = ≡.refl
      go (constantSP A) _ = ≡.refl
      go (sumSP F₁ F₂) (Sum.inj₁ fp₁) = ≡.cong Sum.inj₁ (go F₁ fp₁)
      go (sumSP F₁ F₂) (Sum.inj₂ fp₂) = ≡.cong Sum.inj₂ (go F₂ fp₂)
      go (prodSP F₁ F₂) (pair fp₁ fp₂) = ≡.cong₂ pair (go F₁ fp₁) (go F₂ fp₂)
      go (kfunSP A F') a→fp = ext₀₀ λ a → go F' (a→fp a)

module _ {I : Set} where
  open umap

  map⟦_⟧ : ∀ (F : SPos I) {P Q : Profunctor 0ℓ I}
    → P ⇒ Q → (⟦ F ⟧ P ⇒ ⟦ F ⟧ Q)
  map⟦ F ⟧ {P} {Q} α .φ = umap⟦ F ⟧ P Q (α .φ)

  map⟦ idSP ⟧ α .naturality = α .naturality
  map⟦ constantSP _ ⟧ α .naturality = irr[ (λ _ _ _ → ≡.refl) ]
  map⟦ sumSP F₁ F₂ ⟧ α .naturality =
    map⟦ F₁ ⟧ α .naturality >>= λ nat₁# →
    map⟦ F₂ ⟧ α .naturality >>= λ nat₂# →
    irr[ (λ f g → λ { 
      (Sum.inj₁ fp₁) → ≡.cong Sum.inj₁ (nat₁# f g fp₁);
      (Sum.inj₂ fp₂) → ≡.cong Sum.inj₂ (nat₂# f g fp₂)
    }) ]
  map⟦ prodSP F₁ F₂ ⟧ α .naturality = 
    map⟦ F₁ ⟧ α .naturality >>= λ nat₁# →
    map⟦ F₂ ⟧ α .naturality >>= λ nat₂# →
    irr[ (λ f g (pair fp₁ fp₂) →
      ≡.cong₂ pair (nat₁# f g fp₁) (nat₂# f g fp₂)
    )]
  map⟦ kfunSP A F ⟧ α .naturality =
    map⟦ F ⟧ α .naturality >>= λ nat# →
    irr[ (λ f g afp → ext₀₀ λ a → nat# f g (afp (dimap A g f a))) ]

  open IsFunctor

  instance
    SPosIsFunctor : ∀ {F : SPos I}
      → IsFunctor I I ⟦ F ⟧
    SPosIsFunctor {F} .promap = map⟦ F ⟧
    SPosIsFunctor {F} .promap-cong eq = irr[ umap⟦ F ⟧-cong _ _ eq ]
    SPosIsFunctor {F} .promap-id P = irr[ umap⟦ F ⟧-id P ]
    SPosIsFunctor {F} .promap-∘ qr pq = irr[ umap⟦ F ⟧-∘ _ _ _ (qr .φ) (pq .φ) ]

open MaybeIndex
open MaybeIndexProfunctor

private
  bang : ∀ {x : Set} → x → ⊤
  bang _ = tt
  
  module _ {I : Set} {a b : I → Set} where
    Fr-phantom : (F : SPos I) {y : Set}
      → (fr : ∀ x → (⟦ shiftSPos F ⟧ v0) [ a :: x , b :: y ])
      → {x x' : Set} (h : x' → x)
      → lmap-on-nothing (⟦ shiftSPos F ⟧ v0) h (fr x) ≡ fr x'
    Fr-phantom F fr h = _
  
  module _ {I : Set} {A : Profunctor 0ℓ I} where
    module _ {a b : I → Set} where
      shift⟦_⟧ : (F : SPos I)
        → (⟦ F ⟧ A) [ a , b ]
        → (⟦ shiftSPos F ⟧ v0) [ a :: ⊤ , b :: A [ a , b ] ]
      shift⟦ idSP ⟧ fa = fa
      shift⟦ constantSP _ ⟧ fa = fa
      shift⟦ sumSP F₁ F₂ ⟧ fa = Sum.map (shift⟦ F₁ ⟧) (shift⟦ F₂ ⟧) fa
      shift⟦ prodSP F₁ F₂ ⟧ fa = Prod.map shift⟦ F₁ ⟧ shift⟦ F₂ ⟧ fa
      shift⟦ kfunSP C F ⟧ c→fa = λ c → shift⟦ F ⟧ (c→fa c)

      unshift⟦_⟧ : (F : SPos I) {x : Set}
        → (⟦ shiftSPos F ⟧ v0) [ a :: x , b :: A [ a , b ] ]
        → (⟦ F ⟧ A) [ a , b ]
      unshift⟦ idSP ⟧ fa = fa
      unshift⟦ constantSP _ ⟧ fa = fa
      unshift⟦ sumSP F₁ F₂ ⟧ fa = Sum.map (unshift⟦ F₁ ⟧) (unshift⟦ F₂ ⟧) fa
      unshift⟦ prodSP F₁ F₂ ⟧ fa = Prod.map unshift⟦ F₁ ⟧ unshift⟦ F₂ ⟧ fa
      unshift⟦ kfunSP C F ⟧ c→fa = λ c → unshift⟦ F ⟧ (c→fa c)

      unshift-shift-id⟦_⟧ : (F : SPos I) (fa : (⟦ F ⟧ A) [ a , b ])
        → unshift⟦ F ⟧ (shift⟦ F ⟧ fa) ≡ fa
      unshift-shift-id⟦ F ⟧ fa = _

      shift-unshift-id⟦_⟧ : (F : SPos I) {x : Set}
        (let Fr = ⟦ shiftSPos F ⟧ v0)
        (fr : Fr [ a :: x , b :: A [ a , b ] ])
        → lmap-on-nothing Fr bang (shift⟦ F ⟧ (unshift⟦ F ⟧ fr)) ≡ fr
      shift-unshift-id⟦ F ⟧ fr = _

      shift-unshift-id⟦_⟧-⊤ : (F : SPos I) {x : Set}
        (let Fr = ⟦ shiftSPos F ⟧ v0)
        (fr : Fr [ a :: ⊤ , b :: A [ a , b ] ])
        → shift⟦ F ⟧ (unshift⟦ F ⟧ fr) ≡ fr
      shift-unshift-id⟦ F ⟧-⊤ fr = ≡.trans
        (≡.sym (dimap-on-nothing-id (⟦ shiftSPos F ⟧ v0) _))
        (shift-unshift-id⟦ F ⟧ fr)

    shift⟦_⟧-naturality : ∀ (F : SPos I) {a a' b b'}
      → {f : a' ~> a} {g : b ~> b'} (fa : (⟦ F ⟧ A) [ a , b ])
      → (let Fr = ⟦ shiftSPos F ⟧ v0)
      → shift⟦ F ⟧ (dimap (⟦ F ⟧ A) f g fa)
          ≡
        rmap-on-nothing Fr (dimap A f g)
          (dimap-on-just Fr f g (shift⟦ F ⟧ fa))
    shift⟦ idSP ⟧-naturality fa = ≡.refl
    shift⟦ constantSP C ⟧-naturality {f = f} {g = g} fa =
      ≡.sym (dimap-id C (dimap C f g fa))
      where
        open ≡.≡-Reasoning
    shift⟦ sumSP F₁ _ ⟧-naturality {f = f} {g = g} (Sum.inj₁ fa) = ≡.cong _⊎_.inj₁ (shift⟦ F₁ ⟧-naturality fa)
    shift⟦ sumSP _ F₂ ⟧-naturality {f = f} {g = g} (Sum.inj₂ fa) = ≡.cong _⊎_.inj₂ (shift⟦ F₂ ⟧-naturality fa)
    shift⟦ prodSP F₁ F₂ ⟧-naturality {f = f} {g = g} (pair fa₁ fa₂) = ≡.cong₂ pair (shift⟦ F₁ ⟧-naturality fa₁) (shift⟦ F₂ ⟧-naturality fa₂)
    shift⟦ kfunSP C F ⟧-naturality {f = f} {g = g} fa = ext₀₀ λ c → begin
        shift⟦ kfunSP C F ⟧ (dimap (⟦ kfunSP C F ⟧ A) f g fa) c
      ≡⟨⟩
        (shift⟦ F ⟧
          ∘′ dimap (⟦ F ⟧ A) f g
          ∘′ fa
          ∘′ dimap C g f) c
      ≡⟨ shift⟦ F ⟧-naturality (fa (dimap C g f c)) ⟩
        (rmap-on-nothing Fr (dimap A f g)
          ∘′ dimap-on-just Fr f g
          ∘′ shift⟦ F ⟧
          ∘′ fa
          ∘′ dimap C g f) c
      ≡⟨ ≡.cong
            (rmap-on-nothing Fr (dimap A f g)
              ∘′ dimap-on-just Fr f g
              ∘′ shift⟦ F ⟧
              ∘′ fa
              ∘′ dimap C g f)
            (dimap-id C c) ⟨
        (rmap-on-nothing Fr (dimap A f g)
          ∘′ dimap-on-just Fr f g
          ∘′ shift⟦ F ⟧
          ∘′ fa
          ∘′ dimap C g f
          ∘′ rmap-on-nothing (k C) {x = ⊤} (dimap A f g)) c
      ≡⟨⟩
        rmap-on-nothing c→Fr (dimap A f g)
          (dimap-on-just c→Fr f g (shift⟦ kfunSP C F ⟧ fa)) c
      ∎
      where
        open ≡.≡-Reasoning
        Fr = ⟦ shiftSPos F ⟧ v0
        c→Fr = fun (k C) Fr

    unshift⟦_⟧-naturality : ∀ (F : SPos I) {a a' b b'}
      → {f : a' ~> a} {g : b ~> b'} (fr : (⟦ shiftSPos F ⟧ v0) [ a :: ⊤ , b :: A [ a , b ] ])
      → (let Fr = ⟦ shiftSPos F ⟧ v0)
      → dimap (⟦ F ⟧ A) f g (unshift⟦ F ⟧ fr)
          ≡
        unshift⟦ F ⟧ (
          rmap-on-nothing Fr (dimap A f g) (dimap-on-just Fr f g fr)
        )
    unshift⟦ F ⟧-naturality {f = f} {g = g} fr = begin
        (dimap (⟦ F ⟧ A) f g ∘′ unshift⟦ F ⟧) fr
      ≡⟨ unshift-shift-id⟦ F ⟧ _ ⟨
        (unshift⟦ F ⟧ ∘′ shift⟦ F ⟧ ∘′ dimap (⟦ F ⟧ A) f g ∘′ unshift⟦ F ⟧) fr
      ≡⟨ {!   !} ⟩
        (unshift⟦ F ⟧ ∘′ rmap-on-nothing Fr (dimap A f g) ∘′ dimap-on-just Fr f g ∘′ shift⟦ F ⟧ ∘′ unshift⟦ F ⟧) fr
      ≡⟨ {!   !} ⟩
        (unshift⟦ F ⟧ ∘′ rmap-on-nothing Fr (dimap A f g) ∘′ dimap-on-just Fr f g) fr
      ∎
      where
        open ≡.≡-Reasoning
        Fr = ⟦ shiftSPos F ⟧ v0

-- The yoneda lemma
module _ {I : Set} (A : Profunctor 0ℓ I) where
  -- Yoneda F represent (∀ r. (A -> r) -> F r)
  private
    Yraw : SPos I → Profunctor 0ℓ (Maybe I)
    Yraw F = fun A→r Fr
      where
         A→r : Profunctor 0ℓ (Maybe I)
         A→r = fun (k A) v0

         Fr : Profunctor 0ℓ (Maybe I)
         Fr = ⟦ shiftSPos F ⟧ v0

  Yoneda : SPos I → Profunctor 1ℓ I
  Yoneda F = EndP (LiftP 1ℓ (Yraw F))

  private

    module _ (a b : I → Set) where
      -- lowerYraw : ∀ F → (∀ x → Yraw F [ a :: x , b :: x ]) → (⟦ F ⟧ A) [ a , b ]
      -- liftYraw : ∀ F → (⟦ F ⟧ A) [ a , b ] → (∀ x → Yraw F [ a :: x , b :: x ])
      -- 
      -- Because: 
      --   Yraw F [ a :: x , b :: x ]
      --    = fun (k A) v0 [ maybe′ b x , maybe′ a x ]
      --       → (⟦ shiftSPos F ⟧ v0) [ a :: x , b :: x ]
      --    = (k A [ a :: x , b :: x ] → v0 [ maybe′ b x , maybe′ a x ] )
      --       → (⟦ shiftSPos F ⟧ v0) [ a :: x , b :: x ]
      --    = (A [ a , b ] → x)
      --       → (⟦ shiftSPos F ⟧ v0) [ a :: x , b :: x ]

      lowerYraw : (F : SPos I)
        → (∀ x → (A [ a , b ] → x)
            → ⟦ shiftSPos F ⟧ v0 [ a :: x , b :: x ])
        → (⟦ F ⟧ A) [ a , b ]
      lowerYraw F yF = unshift⟦ F ⟧ (yF (A [ a , b ]) id)

      liftYraw : (F : SPos I)
        → ((⟦ F ⟧ A) [ a , b ])
        → (x : Set)
        → (A [ a , b ] → x)
        → (⟦ shiftSPos F ⟧ v0) [ a :: x , b :: x ]
      
      liftYraw F fa x cont = dimap-on-nothing (⟦ shiftSPos F ⟧ v0) bang cont (shift⟦ F ⟧ fa)

      liftYexnat : (F : SPos I)
        → (fa : (⟦ F ⟧ A) [ a , b ])
        → {x⁻ x⁺ : Set} (h : x⁻ → x⁺)
        → (cont : A [ a , b ] → x⁻)
        → lmap-on-nothing (Yraw F) h (liftYraw F fa x⁺) cont
           ≡
          rmap-on-nothing (Yraw F) h (liftYraw F fa x⁻) cont
      
      liftYexnat F fa {x⁻} {x⁺} h cont = begin
          lmap-on-nothing (Yraw F) h (liftYraw F fa x⁺) cont
        ≡⟨⟩
          lmap-on-nothing Fr h
            (liftYraw F fa x⁺ (h ∘′ cont'))
        ≡⟨⟩
          lmap-on-nothing Fr h
            (dimap-on-nothing Fr bang (h ∘′ cont')
               (shift⟦ F ⟧ fa))
        ≡⟨ dimap-on-nothing-∘ Fr _ _ _ _ (shift⟦ F ⟧ fa) ⟨
          dimap-on-nothing Fr bang (h ∘′ cont')
            (shift⟦ F ⟧ fa)
        ≡⟨ dimap-on-nothing-∘ Fr _ _ _ _ (shift⟦ F ⟧ fa) ⟩
          rmap-on-nothing Fr h
            (dimap-on-nothing Fr bang cont'
               (shift⟦ F ⟧ fa))
        ≡⟨⟩
          rmap-on-nothing Fr h (liftYraw F fa x⁻ cont')
        ≡⟨⟩
          rmap-on-nothing (Yraw F) h (liftYraw F fa x⁻) cont
        ∎
        where
          open ≡.≡-Reasoning

          Fr : Profunctor 0ℓ (Maybe I)
          Fr = ⟦ shiftSPos F ⟧ v0

          -- Equal to cont using dimap-id A,
          -- but that equality is not needed anywhere.
          cont' : A [ a , b ] → x⁻
          cont' = cont ∘′ dimap A idᵢ idᵢ
    
    module _ {a a' b b' : I → Set} (f : a' ~> a) (g : b ~> b') where
      liftYnat : (F : SPos I)
        → (fa : (⟦ F ⟧ A) [ a , b ])
        → (x : Set)
        → (cont : A [ a' , b' ] → x)
        → liftYraw a' b' F (dimap (⟦ F ⟧ A) f g fa) x cont
            ≡
          dimap-on-just (Yraw F) f g (liftYraw a b F fa x) cont

      liftYnat F fa x cont = begin
          liftYraw a' b' F (dimap (⟦ F ⟧ A) f g fa) x cont
        ≡⟨⟩
          dimap-on-nothing Fr bang cont
            (shift⟦ F ⟧ (dimap (⟦ F ⟧ A) f g fa))
        ≡⟨ ≡.cong (dimap-on-nothing Fr bang cont) (shift⟦ F ⟧-naturality fa) ⟩
          dimap-on-nothing Fr bang cont
            (rmap-on-nothing Fr (dimap A f g) (dimap-on-just Fr f g (shift⟦ F ⟧ fa)))
        ≡⟨ dimap-on-nothing-∘ Fr bang cont id (dimap A f g)
                ((dimap-on-just Fr f g (shift⟦ F ⟧ fa))) ⟨
          dimap-on-nothing Fr bang (cont ∘′ dimap A f g)
            (dimap-on-just Fr f g (shift⟦ F ⟧ fa))
        ≡⟨ dimap-on-just-nothing-comm Fr _ _ _ _ (shift⟦ F ⟧ fa) ⟨
          dimap-on-just Fr f g
            (dimap-on-nothing Fr bang (cont ∘′ dimap A f g)
              (shift⟦ F ⟧ fa))
        ≡⟨⟩
          dimap-on-just (Yraw F) f g (liftYraw a b F fa x) cont
        ∎
        where
          open ≡.≡-Reasoning
          Fr : Profunctor 0ℓ (Maybe I)
          Fr = ⟦ shiftSPos F ⟧ v0

  lowerY : ∀ (F : SPos I)
    → Yoneda F ⇒ ⟦ F ⟧ A
  lowerY F .φ {a} {b} yF = lowerYraw a b F (λ x → lower (yF .proj x))
  lowerY F .naturality = _

  liftY : ∀ (F : SPos I)
    → ⟦ F ⟧ A ⇒ Yoneda F
  liftY F .φ {a} {b} fa .proj = λ x → lift (liftYraw a b F fa x)
  liftY F .φ {a} {b} fa .extranaturality = irr[ (
      λ h → ≡.cong lift (ext₀₀ (liftYexnat a b F fa h))
    ) ]
  liftY F .naturality = irr[( λ f g fa → extEnd (LiftP 1ℓ (Yraw F)) λ x → ≡.cong lift (ext₀₀ (liftYnat f g F fa x)))]

  open NaturalIso

  yoneda : ∀ (F : SPos I)
    → Yoneda F ⇔ ⟦ F ⟧ A
  yoneda F .to = lowerY F
  yoneda F .from = liftY F
  yoneda F .to-from = _
  yoneda F .from-to = _
