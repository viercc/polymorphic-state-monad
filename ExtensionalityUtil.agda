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

open import Data.Irrelevant public
open import Axiom.Extensionality.Propositional public

-- Extensionality under irrelevance

IrrExtensionality : (a b : Level) → Set _
IrrExtensionality a b = Irrelevant (Extensionality a b)
