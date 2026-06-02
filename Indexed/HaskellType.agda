{-# OPTIONS --without-K --irrelevant-projections #-}

open import Level

open import Relation.Binary.PropositionalEquality

open import Function
  using (_∘_; id; _$_)

open import Data.Product as Prod using (_×_)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit
open import Data.Empty

open import Data.Maybe as Maybe
  using (Maybe; nothing; just; maybe; maybe′)

open import ExtensionalityUtil

module Indexed.HaskellType (irr-ext : IrrExtensionality 1ℓ 2ℓ) where

private
  .ext₁₂ : Extensionality 1ℓ 2ℓ
  ext₁₂ = irrelevant irr-ext

  .ext₁₁ : Extensionality 1ℓ 1ℓ
  ext₁₁ = lower-extensionality 1ℓ 2ℓ ext₁₂

  .ext₀₀ : Extensionality 0ℓ 0ℓ
  ext₀₀ = lower-extensionality 1ℓ 2ℓ ext₁₂

  .ext₀₁ : Extensionality 0ℓ 1ℓ
  ext₀₁ = lower-extensionality 1ℓ 2ℓ ext₁₂

open import Indexed.Profunctor [ ext₁₁ ]
  renaming (_+_ to _+P_; _×_ to _×P_)
open import Indexed.Profunctor.End [ ext₁₁ ]

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

-- TODO: mapTy-id, mapTy-∘

-- * Proof of isomorphisms

-- TODO: Fill TyIsoAxiom

data TyIsoAxiom {V : Set} : Ty V → Ty V → Set where
  sum-empty : (t : Ty V) → TyIsoAxiom (sumTy t emptyTy) t
  sum-comm : (t u : Ty V) → TyIsoAxiom (sumTy t u) (sumTy u t)
  sum-assoc : (t u v : Ty V) → TyIsoAxiom (sumTy (sumTy t u) v) (sumTy t (sumTy u v))
  -- etc.

data TyIso {V : Set} : Ty V → Ty V → Set where
  isoAxiom : ∀ {t u} → TyIsoAxiom t u → TyIso t u
  isoRefl : ∀ {t} → TyIso t t
  isoSym : ∀ {t u} → TyIso t u → TyIso u t
  isoTrans : ∀ {t u v} → TyIso t u → TyIso u v → TyIso t v

weaken : ∀ {V W} (f : W → V) {u v} → TyIso u v → TyIsoAxiom (mapTy f u) (mapTy f v)
weaken = _

-- * Interpreting

interpret : ∀ {V : Set} → Ty V → (V → Set) → Set₁
interpret (varTy v)       var = Lift (suc 0ℓ) (var v)
interpret emptyTy         _   = Lift (suc 0ℓ) ⊥
interpret unitTy          _   = Lift (suc 0ℓ) ⊤
interpret (sumTy t u)     var = interpret t var ⊎ interpret u var
interpret (prodTy t u)    var = interpret t var × interpret u var
interpret (funTy t u)     var = interpret t var → interpret u var
interpret (forallTy body) var =
  (A : Set) → interpret body (maybe′ var A)

.interpret-mapTy : ∀ {V W : Set} (f : V → W) (t : Ty V) (env : W → Set)
  → interpret (mapTy f t) env ≡ interpret t (env ∘ f)
interpret-mapTy f t env with t
... | varTy v = refl
... | emptyTy = refl
... | unitTy = refl
... | sumTy u₁ u₂ = cong₂ _⊎_ (interpret-mapTy f u₁ env) (interpret-mapTy f u₂ env)
... | prodTy u₁ u₂ = cong₂ _×_ (interpret-mapTy f u₁ env) (interpret-mapTy f u₂ env)
... | funTy u₁ u₂ = cong₂ (λ A B → A → B) (interpret-mapTy f u₁ env) (interpret-mapTy f u₂ env)
... | forallTy body =
  cong (λ (T : Set → Set₁) → (A : Set) → T A)
    (ext₁₂ bodySetEq)
    where
      bodySetEq : (A : Set) →
        interpret (mapTy (Maybe.map f) body) (maybe′ env A) ≡
        interpret body (maybe′ (env ∘ f) A)
      bodySetEq A = begin
          interpret (mapTy (Maybe.map f) body) (maybe′ env A)
        ≡⟨ interpret-mapTy (Maybe.map f) body (maybe′ env A) ⟩
          interpret body (maybe′ env A ∘ Maybe.map f)
        ≡⟨ cong (interpret body) (ext₀₁ (λ { (just _) → refl ; nothing → refl })) ⟩
          interpret body (maybe′ (env ∘ f) A)
        ∎
        where open ≡-Reasoning

interpretP : ∀ {V : Set} → Ty V → Profunctor V
interpretP (varTy v) = var v
interpretP emptyTy = constant ⊥
interpretP unitTy = constant ⊤
interpretP (sumTy t u) = interpretP t +P interpretP u
interpretP (prodTy t u) = interpretP t ×P interpretP u
interpretP (funTy t u) = fun (interpretP t) (interpretP u)
interpretP (forallTy body) = EndP (interpretP body)

-- TODO: interpret TyIso to isomorphism between Profunctors