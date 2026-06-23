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
      -- lowerYraw : ∀ F → (∀ x → Yraw F [ maybe′ a x , maybe′ b x ]) → (⟦ F ⟧ A) [ a , b ]
      -- liftYraw : ∀ F → (⟦ F ⟧ A) [ a , b ] → (∀ x → Yraw F [ maybe′ a x , maybe′ b x ])
      -- 
      -- Because: 
      --   Yraw F [ maybe′ a x , maybe′ b x ]
      --    = fun (k A) v0 [ maybe′ b x , maybe′ a x ]
      --       → (⟦ shiftSPos F ⟧ v0) [ maybe′ a x , maybe′ b x ]
      --    = (k A [ maybe′ a x , maybe′ b x ] → v0 [ maybe′ b x , maybe′ a x ] )
      --       → (⟦ shiftSPos F ⟧ v0) [ maybe′ a x , maybe′ b x ]
      --    = (A [ a , b ] → x)
      --       → (⟦ shiftSPos F ⟧ v0) [ maybe′ a x , maybe′ b x ]

      lowerYraw : (F : SPos I)
        → (∀ x → (A [ a , b ] → Lift 1ℓ x)
            → ⟦ shiftSPos F ⟧ v0 [ maybe′ a x , maybe′ b x ])
        → (⟦ F ⟧ A) [ a , b ]
      lowerYraw F yF = _

      liftYraw : (F : SPos I)
        → ((⟦ F ⟧ A) [ a , b ])
        → (x : Set)
        → (A [ a , b ] → x)
        → (⟦ shiftSPos F ⟧ v0) [ maybe′ a x , maybe′ b x ]
      
      liftYraw F fa x cont = go F fa
        where
          go : (F' : SPos I)
            → ((⟦ F' ⟧ A) [ a , b ])
            → (⟦ shiftSPos F' ⟧ v0) [ maybe′ a x , maybe′ b x ]
          go idSP fa' = cont fa'
          go (constantSP _) fa' = fa'
          go (sumSP F₁ _) (Sum.inj₁ fa₁) = Sum.inj₁ (go F₁ fa₁)
          go (sumSP _ F₂) (Sum.inj₂ fa₂) = Sum.inj₂ (go F₂ fa₂)
          go (prodSP F₁ F₂) (pair fa₁ fa₂) = pair (go F₁ fa₁) (go F₂ fa₂)
          go (kfunSP C F') c→fa = λ c → go F' (c→fa c)

      liftYexnat : (F : SPos I)
        → (fa : (⟦ F ⟧ A) [ a , b ])
        → {x⁻ x⁺ : Set} (h : x⁻ → x⁺)
        → (k : A [ a , b ] → x⁻)
        → lmap (Yraw F) (on-nothing h) (liftYraw F fa x⁺) k
           ≡
          rmap (Yraw F) (on-nothing h) (liftYraw F fa x⁻) k
      
      liftYexnat F fa {x⁻} {x⁺} h cont = go F fa
        where
          go : (F' : SPos I)
            → (fa' : (⟦ F' ⟧ A) [ a , b ])
            → lmap (Yraw F') (on-nothing h) (liftYraw F' fa' x⁺) cont
                ≡
              rmap (Yraw F') (on-nothing h) (liftYraw F' fa' x⁻) cont
          go idSP fa' = ≡.refl
          go (constantSP _) fa' = ≡.refl
          go (sumSP F₁ _) (Sum.inj₁ fa₁) = ≡.cong Sum.inj₁ (go F₁ fa₁)
          go (sumSP _ F₂) (Sum.inj₂ fa₂) = ≡.cong Sum.inj₂ (go F₂ fa₂)
          go (prodSP F₁ F₂) (pair fa₁ fa₂) = ≡.cong₂ pair (go F₁ fa₁) (go F₂ fa₂)
          go (kfunSP C F') c→fa = ext₀₀ λ c →
            begin
              lmap (Yraw (kfunSP C F')) (on-nothing h) (liftYraw (kfunSP C F') c→fa x⁺) cont c
            ≡⟨⟩
              lmap F'r (on-nothing h)
                (liftYraw F' (c→fa (dimap C idᵢ idᵢ c)) x⁺ rmap-h-cont)
            ≡⟨ ≡.cong (λ c' → lmap F'r (on-nothing h)
                (liftYraw F' (c→fa c') x⁺ rmap-h-cont))
              (dimap-id C c)
            ⟩
              lmap F'r (on-nothing h)
                (liftYraw F' (c→fa c) x⁺ rmap-h-cont)
            ≡⟨⟩
              lmap (Yraw F') (on-nothing h)
                (liftYraw F' (c→fa c) x⁺) cont
            ≡⟨ go F' (c→fa c) ⟩
              rmap (Yraw F') (on-nothing h)
                (liftYraw F' (c→fa c) x⁻) cont
            ≡⟨⟩
              rmap F'r (on-nothing h)
                (liftYraw F' (c→fa c) x⁻ lmap-h-cont)
            ≡⟨ ≡.cong (λ c' → rmap F'r (on-nothing h)
                (liftYraw F' (c→fa c') x⁻ lmap-h-cont))
              (≡.sym (dimap-id C c))
            ⟩
              rmap F'r (on-nothing h)
                (liftYraw F' (c→fa (dimap C idᵢ idᵢ c)) x⁻ lmap-h-cont)
            ≡⟨⟩
              rmap (Yraw (kfunSP C F')) (on-nothing h) (liftYraw (kfunSP C F') c→fa x⁻) cont c
            ∎
            where
              A→r F'r : Profunctor 0ℓ (Maybe I)
              A→r = fun (k A) v0
              F'r = ⟦ shiftSPos F' ⟧ v0

              lmap-h-cont : A→r [ maybe b x⁻ , maybe a x⁻ ]
              lmap-h-cont = lmap A→r {b = maybe a x⁻} (on-nothing h) cont

              rmap-h-cont : A→r [ maybe b x⁺ , maybe a x⁺ ]
              rmap-h-cont = rmap A→r {a = maybe b x⁺} (on-nothing h) cont

              open ≡.≡-Reasoning
    
    module _ {a a' b b' : I → Set} (f : a' ~> a) (g : b ~> b') where
      liftYnat : (F : SPos I)
        → (fa : (⟦ F ⟧ A) [ a , b ])
        → (x : Set)
        → (cont : A [ a' , b' ] → x)
        → liftYraw a' b' F (dimap (⟦ F ⟧ A) f g fa) x cont
            ≡
          dimap (Yraw F) (on-just f) (on-just g) (liftYraw a b F fa x) cont
      liftYnat F-orig fa-orig x cont = go F-orig fa-orig
        where
          go : (F : SPos I)
            → (fa : (⟦ F ⟧ A) [ a , b ])
            → liftYraw a' b' F (dimap (⟦ F ⟧ A) f g fa) x cont
                ≡
              dimap (Yraw F) (on-just f) (on-just g) (liftYraw a b F fa x) cont
          go idSP fa = ≡.refl
          go (constantSP _) fa = ≡.refl
          go (sumSP F₁ F₂) (Sum.inj₁ fa₁) = ≡.cong Sum.inj₁ (go F₁ fa₁)
          go (sumSP F₁ F₂) (Sum.inj₂ fa₂) = ≡.cong Sum.inj₂ (go F₂ fa₂)
          go (prodSP F₁ F₂) (pair fa₁ fa₂) = ≡.cong₂ pair (go F₁ fa₁) (go F₂ fa₂)
          go (kfunSP C F) c→fa = ext₀₀ λ c → go F (c→fa (dimap C g f c))

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
  yoneda F .to = _
  yoneda F .from = liftY F
  yoneda F .to-from = _
  yoneda F .from-to = _
