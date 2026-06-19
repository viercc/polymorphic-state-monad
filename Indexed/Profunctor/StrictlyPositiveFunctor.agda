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

open import ExtensionalityUtil

open import Indexed.Profunctor
open import Indexed.Profunctor.Functor
open import Indexed.Profunctor.Sum
open import Indexed.Profunctor.Product

module Indexed.Profunctor.StrictlyPositiveFunctor .(ext : Extensionality 1ℓ 1ℓ) where

open import Indexed.Profunctor.Fun ext
open import Indexed.Profunctor.End ext

open Profunctor

-- Syntax of strictly positive functor
data SPos (I : Set) : Set₂ where
  idSP : SPos I
  constantSP : Profunctor I → SPos I
  sumSP : SPos I → SPos I → SPos I
  prodSP : SPos I → SPos I → SPos I
  kfunSP : Profunctor I → SPos I → SPos I

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
⟦_⟧ : ∀ {I : Set} → SPos I
  → Profunctor I → Profunctor I
⟦ idSP ⟧ P = P
⟦ constantSP A ⟧ P = A
⟦ sumSP F₁ F₂ ⟧ P = ⟦ F₁ ⟧ P + ⟦ F₂ ⟧ P
⟦ prodSP F₁ F₂ ⟧ P = ⟦ F₁ ⟧ P × ⟦ F₂ ⟧ P
⟦ kfunSP A F ⟧ P = fun A (⟦ F ⟧ P)

map⟦_⟧ : ∀ {I} (F : SPos I) {P Q : Profunctor I}
  → P ⇒ Q → (⟦ F ⟧ P ⇒ ⟦ F ⟧ Q)
map⟦ idSP ⟧ α = α
map⟦ constantSP A ⟧ _ = idNat
map⟦ sumSP F₁ F₂ ⟧ α = map+ (map⟦ F₁ ⟧ α) (map⟦ F₂ ⟧ α)
map⟦ prodSP F₁ F₂ ⟧ α = map× (map⟦ F₁ ⟧ α) (map⟦ F₂ ⟧ α)
map⟦ kfunSP A F ⟧ α = mapFun {A = A} (map⟦ F ⟧ α)

map⟦_⟧-cong : ∀ {I} (F : SPos I) {P Q : Profunctor I}
  → {α β : P ⇒ Q}
  → .(α ≈ β)
  → Irrelevant (map⟦ F ⟧ α ≈ map⟦ F ⟧ β)
map⟦ idSP ⟧-cong eq = irr[ eq ]
map⟦ constantSP x ⟧-cong eq = irr[ (λ _ → ≡.refl) ]
map⟦ sumSP F₁ F₂ ⟧-cong eq =
  map⟦ F₁ ⟧-cong eq >>= λ eqF₁ →
  map⟦ F₂ ⟧-cong eq >>= λ eqF₂ → irr[ (λ {
    (Sum.inj₁ x) → ≡.cong Sum.inj₁ (eqF₁ x);
    (Sum.inj₂ y) → ≡.cong Sum.inj₂ (eqF₂ y)
  }) ]
map⟦ prodSP F₁ F₂ ⟧-cong eq = 
  map⟦ F₁ ⟧-cong eq >>= λ eqF₁ →
  map⟦ F₂ ⟧-cong eq >>= λ eqF₂ → irr[ (λ (pair x y) →
    ≡.cong₂ pair (eqF₁ x) (eqF₂ y)
  ) ]
map⟦ kfunSP A F ⟧-cong eq =
  map⟦ F ⟧-cong eq >>= λ eqF# →
  irr[ (λ afp → ext λ a → eqF# (afp a)) ]

map⟦_⟧-id : ∀ {I} (F : SPos I) (P : Profunctor I)
  → Irrelevant( map⟦ F ⟧ (idNat {P = P}) ≈ idNat )
map⟦ idSP ⟧-id P = irr[ (λ _ → ≡.refl) ]
map⟦ constantSP _ ⟧-id P = irr[ (λ _ → ≡.refl) ]
map⟦ sumSP F₁ F₂ ⟧-id P =
  map⟦ F₁ ⟧-id P >>= λ map-id₁# →
  map⟦ F₂ ⟧-id P >>= λ map-id₂# →
  irr[ (λ {
    (Sum.inj₁ fp₁) → ≡.cong Sum.inj₁ (map-id₁# fp₁);
    (Sum.inj₂ fp₂) → ≡.cong Sum.inj₂ (map-id₂# fp₂)
  }) ]
map⟦ prodSP F₁ F₂ ⟧-id P = 
  map⟦ F₁ ⟧-id P >>= λ map-id₁# →
  map⟦ F₂ ⟧-id P >>= λ map-id₂# →
  irr[ (λ (pair fp₁ fp₂) → 
    ≡.cong₂ pair (map-id₁# fp₁)  (map-id₂# fp₂)
  ) ]
map⟦ kfunSP A F ⟧-id P =
  map⟦ F ⟧-id P >>= λ map-id# →
  irr[ (λ afp → ext λ a → map-id# (afp a)) ]

map⟦_⟧-∘ : ∀ {I} (F : SPos I) {P Q R : Profunctor I}
  → (qr : Q ⇒ R) (pq : P ⇒ Q)
  → Irrelevant( map⟦ F ⟧ (qr ∘Nat pq) ≈ map⟦ F ⟧ qr ∘Nat map⟦ F ⟧ pq )
map⟦ idSP ⟧-∘ qr pq = irr[ (λ _ → ≡.refl) ]
map⟦ constantSP _ ⟧-∘ qr pq = irr[ (λ _ → ≡.refl) ]
map⟦ sumSP F₁ F₂ ⟧-∘ qr pq =
  map⟦ F₁ ⟧-∘ qr pq >>= λ map-∘₁# →
  map⟦ F₂ ⟧-∘ qr pq >>= λ map-∘₂# →
  irr[ (λ {
    (Sum.inj₁ fp₁) → ≡.cong Sum.inj₁ (map-∘₁# fp₁);
    (Sum.inj₂ fp₂) → ≡.cong Sum.inj₂ (map-∘₂# fp₂)
  }) ]
map⟦ prodSP F₁ F₂ ⟧-∘ qr pq = 
  map⟦ F₁ ⟧-∘ qr pq >>= λ map-∘₁# →
  map⟦ F₂ ⟧-∘ qr pq >>= λ map-∘₂# →
  irr[ (λ (pair fp₁ fp₂) → 
    ≡.cong₂ pair (map-∘₁# fp₁)  (map-∘₂# fp₂)
  ) ]
map⟦ kfunSP A F ⟧-∘ qr pq =
  map⟦ F ⟧-∘ qr pq >>= λ map-∘# →
  irr[ (λ afp → ext λ a → map-∘# (afp a)) ]

open IsFunctor

instance
  SPosIsFunctor : ∀ {I} {F : SPos I}
    → IsFunctor I I ⟦ F ⟧
  SPosIsFunctor {I} {F} .promap = map⟦ F ⟧
  SPosIsFunctor {I} {F} .promap-cong = map⟦ F ⟧-cong
  SPosIsFunctor {I} {F} .promap-id = map⟦ F ⟧-id
  SPosIsFunctor {I} {F} .promap-∘ = map⟦ F ⟧-∘

-- The yoneda lemma
yoneda : ∀ {I} (F : SPos I) (A : Profunctor I)
  → EndP (fun (fun (k A) v0) (⟦ shiftSPos F ⟧ v0)) ⇔ ⟦ F ⟧ A
yoneda F A = {!   !}
