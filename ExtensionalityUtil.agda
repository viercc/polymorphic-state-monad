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

open import Axiom.Extensionality.Propositional public

module Ext00 (ext : Extensionality 0ℓ 0ℓ) where
   ext₀₀ : Extensionality 0ℓ 0ℓ
   ext₀₀ = ext

   iext₀₀ : ExtensionalityImplicit 0ℓ 0ℓ
   iext₀₀ = implicit-extensionality ext

module Ext01↓ (ext : Extensionality 0ℓ 1ℓ) where
   ext₀₁ : Extensionality 0ℓ 1ℓ
   ext₀₁ = ext

   iext₀₁ : ExtensionalityImplicit 0ℓ 1ℓ
   iext₀₁ = implicit-extensionality ext

   open Ext00 (lower-extensionality 0ℓ 1ℓ ext) public 

module Ext02↓ (ext : Extensionality 0ℓ 2ℓ) where
   ext₀₂ : Extensionality 0ℓ 2ℓ
   ext₀₂ = ext

   iext₀₂ : ExtensionalityImplicit 0ℓ 2ℓ
   iext₀₂ = implicit-extensionality ext

   open Ext01↓ (lower-extensionality 0ℓ 2ℓ ext) public


module Ext10 (ext : Extensionality 1ℓ 0ℓ) where
   ext₁₀ : Extensionality 1ℓ 0ℓ
   ext₁₀ = ext

   iext₁₀ : ExtensionalityImplicit 1ℓ 0ℓ
   iext₁₀ = implicit-extensionality ext

module Ext11↓ (ext : Extensionality 1ℓ 1ℓ) where
   ext₁₁ : Extensionality 1ℓ 1ℓ
   ext₁₁ = ext

   iext₁₁ : ExtensionalityImplicit 1ℓ 1ℓ
   iext₁₁ = implicit-extensionality ext

   open Ext10 (lower-extensionality 1ℓ 1ℓ ext) public 

module Ext12↓ (ext : Extensionality 1ℓ 2ℓ) where
   ext₁₂ : Extensionality 1ℓ 2ℓ
   ext₁₂ = ext

   iext₁₂ : ExtensionalityImplicit 1ℓ 2ℓ
   iext₁₂ = implicit-extensionality ext

   open Ext11↓ (lower-extensionality 1ℓ 2ℓ ext) public

module Ext20 (ext : Extensionality 2ℓ 0ℓ) where
   ext₂₀ : Extensionality 2ℓ 0ℓ
   ext₂₀ = ext

   iext₂₀ : ExtensionalityImplicit 2ℓ 0ℓ
   iext₂₀ = implicit-extensionality ext

module Ext21↓ (ext : Extensionality 2ℓ 1ℓ) where
   ext₂₁ : Extensionality 2ℓ 1ℓ
   ext₂₁ = ext

   iext₂₁ : ExtensionalityImplicit 2ℓ 1ℓ
   iext₂₁ = implicit-extensionality ext

   open Ext20 (lower-extensionality 2ℓ 1ℓ ext) public 

module Ext22↓ (ext : Extensionality 2ℓ 2ℓ) where
   ext₂₂ : Extensionality 2ℓ 2ℓ
   ext₂₂ = ext

   iext₂₂ : ExtensionalityImplicit 2ℓ 2ℓ
   iext₂₂ = implicit-extensionality ext

   open Ext21↓ (lower-extensionality 2ℓ 2ℓ ext) public

module Ext2↓2↓ (ext : Extensionality 2ℓ 2ℓ) where
   open Ext22↓ ext public
   open Ext12↓ (lower-extensionality 2ℓ 2ℓ ext) public
   open Ext02↓ (lower-extensionality 2ℓ 2ℓ ext) public
