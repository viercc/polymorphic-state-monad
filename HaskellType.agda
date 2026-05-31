{-# OPTIONS --without-K --irrelevant-projections #-}

open import Level

open import Relation.Binary.PropositionalEquality

open import Function
  using (_∘_; id)

open import Data.Product as Prod using (_×_; _,_)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit
open import Data.Empty

open import Data.Maybe as Maybe
  using (Maybe; nothing; just; maybe; maybe′)

module HaskellType where

data Ty (V : Set) : Set where
  varTy : V → Ty V
  emptyTy : Ty V
  unitTy : Ty V
  sumTy  : Ty V → Ty V → Ty V
  prodTy : Ty V → Ty V → Ty V
  funTy  : Ty V → Ty V → Ty V
  forallTy : Ty (Maybe V) → Ty V

mapTy : ∀ {V W : Set} → (V → W) → Ty V → Ty W
mapTy f (varTy v) = varTy (f v)
mapTy f emptyTy = emptyTy
mapTy f unitTy = unitTy
mapTy f (sumTy t u) = sumTy (mapTy f t) (mapTy f u)
mapTy f (prodTy t u) = prodTy (mapTy f t) (mapTy f u)
mapTy f (funTy t u) = funTy (mapTy f t) (mapTy f u)
mapTy f (forallTy body) = forallTy (mapTy (Maybe.map f) body)

interpret : ∀ {V : Set} → Ty V → (V → Set) → Set₁
interpret (varTy v)       var = Lift (suc 0ℓ) (var v)
interpret emptyTy         _   = Lift (suc 0ℓ) ⊥
interpret unitTy          _   = Lift (suc 0ℓ) ⊤
interpret (sumTy t u)     var = interpret t var ⊎ interpret u var
interpret (prodTy t u)    var = interpret t var × interpret u var
interpret (funTy t u)     var = interpret t var → interpret u var
interpret (forallTy body) var =
  (A : Set) → interpret body (maybe′ var A)

interpret-mapTy : ∀ {V W : Set} (f : V → W) (t : Ty V) (env : W → Set)
  → interpret (mapTy f t) env ≡ interpret t (env ∘ f)
interpret-mapTy f t env with t
... | (varTy v) = refl 
... | emptyTy = refl
... | unitTy = refl
... | sumTy u₁ u₂ = cong₂ _⊎_ (interpret-mapTy f u₁ env) (interpret-mapTy f u₂ env)
... | prodTy u₁ u₂ = cong₂ _×_ (interpret-mapTy f u₁ env) (interpret-mapTy f u₂ env)
... | funTy u₁ u₂ = cong₂ (λ A B → A → B) (interpret-mapTy f u₁ env) (interpret-mapTy f u₂ env)
... | forallTy body = {! !} -- requires funext?

{-

TODO:

interpretP : ∀ {V : Set} → Ty V → Profunctor {V}

interpretP-Carrier : ∀ {V} (t : Ty V) (env : V → Set)
  → interpretP t .Carrier env env ≡ interpret t env

-}