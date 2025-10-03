{-# OPTIONS --without-K --safe #-}
open import Level

open import Data.Irrelevant as Irr
open import Axiom.Extensionality.Propositional

open import Relation.Binary.PropositionalEquality as ≡
   using (_≡_)

module ExtensionalityUtil where
  1ℓ 2ℓ 3ℓ : Level
  1ℓ = suc 0ℓ
  2ℓ = suc 1ℓ
  3ℓ = suc 2ℓ

  -- Extensionality under irrelevance

  IrrExtensionality : (a b : Level) → Set _
  IrrExtensionality a b = Irrelevant (Extensionality a b)

  record Ext1 : Set 2ℓ where
    field
      ext₀₀ : Extensionality 0ℓ 0ℓ
      ext₀₁ : Extensionality 0ℓ 1ℓ
      ext₁₀ : Extensionality 1ℓ 0ℓ
      ext₁₁ : Extensionality 1ℓ 1ℓ
  
  lower-extensionality₁ : ∀ a b → 
    Extensionality (1ℓ ⊔ a) (1ℓ ⊔ b) → Ext1
  lower-extensionality₁ a b ext =
    record {
      ext₀₀ = lower-extensionality (1ℓ ⊔ a) (1ℓ ⊔ b) ext;
      ext₀₁ = lower-extensionality (1ℓ ⊔ a) (1ℓ ⊔ b) ext;
      ext₁₀ = lower-extensionality (1ℓ ⊔ a) (1ℓ ⊔ b) ext;
      ext₁₁ = lower-extensionality (1ℓ ⊔ a) (1ℓ ⊔ b) ext
    }

  record Ext2 : Set 3ℓ where
    field
      lowerExts : Ext1
      ext₀₂ : Extensionality 0ℓ 2ℓ
      ext₁₂ : Extensionality 1ℓ 2ℓ
      ext₂₀ : Extensionality 2ℓ 0ℓ
      ext₂₁ : Extensionality 2ℓ 1ℓ
      ext₂₂ : Extensionality 2ℓ 2ℓ
    
    open Ext1 lowerExts public
  
  lower-extensionality₂ : ∀ a b → 
    Extensionality (2ℓ ⊔ a) (2ℓ ⊔ b) → Ext2
  lower-extensionality₂ a b ext =
    record {
      lowerExts = lower-extensionality₁ (2ℓ ⊔ a) (2ℓ ⊔ b) ext;
      ext₀₂ = lower-extensionality (2ℓ ⊔ a) (2ℓ ⊔ b) ext;
      ext₁₂ = lower-extensionality (2ℓ ⊔ a) (2ℓ ⊔ b) ext;
      ext₂₀ = lower-extensionality (2ℓ ⊔ a) (2ℓ ⊔ b) ext;
      ext₂₁ = lower-extensionality (2ℓ ⊔ a) (2ℓ ⊔ b) ext;
      ext₂₂ = lower-extensionality (2ℓ ⊔ a) (2ℓ ⊔ b) ext
    }
  
  