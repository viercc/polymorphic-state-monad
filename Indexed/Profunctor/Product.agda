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

-- | Product of Profunctors
module Indexed.Profunctor.Product where

private
  -- Prod.map has universe-level-polymorphic type
  -- and they didn't inferred when used directly
  mapProd : ∀ {A B C D : Set₁} → (A → C) → (B → D)
    → A Prod.× B → C Prod.× D
  mapProd f g = Prod.map f g

infixr 3 _×_

_×_ : ∀ {I} → Profunctor I → Profunctor I → Profunctor I
_×_ {I} P Q =
  record {
    Carrier = λ a b → P [ a , b ] Prod.× Q [ a , b ];
    dimap = λ f g → mapProd (dimap P f g) (dimap Q f g);
    dimap-id = λ (pair x₁ x₂) →
        ≡.cong₂ pair (dimap-id P x₁) (dimap-id Q x₂);
    dimap-∘ = λ f₁ g₁ f₂ g₂ (pair x₁ x₂) →
        let eqP = dimap-∘ P f₁ g₁ f₂ g₂ x₁
            eqQ = dimap-∘ Q f₁ g₁ f₂ g₂ x₂
        in ≡.cong₂ Prod._,_ eqP eqQ
  }
  where
    open Profunctor

-- Functoriality
module _ {I : Set} where
  private
    variable
      P₁ P₂ Q₁ Q₂ R₁ R₂ : Profunctor I
  
  map× : (P₁ ⇒ Q₁) → (P₂ ⇒ Q₂) → (P₁ × P₂) ⇒ (Q₁ × Q₂)
  map× α₁ α₂ .φ = mapProd (α₁ .φ) (α₂ .φ)
  map× α₁ α₂ .naturality =
    α₁ .naturality >>= λ nat₁# →
    α₂ .naturality >>= λ nat₂# →
    irr[( λ f g (pair p₁ p₂) →
      ≡.cong₂ pair (nat₁# f g p₁) (nat₂# f g p₂)
    )]
   
  map×-cong : ∀ {α₁ β₁ : P₁ ⇒ Q₁} {α₂ β₂ : P₂ ⇒ Q₂}
    → .(α₁ ≈ β₁) → .(α₂ ≈ β₂)
    → Irrelevant (map× α₁ α₂ ≈ map× β₁ β₂)
  map×-cong eq₁ eq₂ = irr[( λ (pair p₁ p₂) → ≡.cong₂ pair (eq₁ p₁) (eq₂ p₂) )]

  map×-id : (P Q : Profunctor I)
    → Irrelevant (map× (idNat {P = P}) (idNat {P = Q}) ≈ idNat)
  map×-id _ _ = irr[ (λ _ → ≡.refl ) ]

  map×-∘ : ∀
    (qr₁ : Q₁ ⇒ R₁) (qr₂ : Q₂ ⇒ R₂) (pq₁ : P₁ ⇒ Q₁) (pq₂ : P₂ ⇒ Q₂)
    → Irrelevant (map× (qr₁ ∘Nat pq₁) (qr₂ ∘Nat pq₂) ≈ map× qr₁ qr₂ ∘Nat map× pq₁ pq₂)
  map×-∘ _ _ _ _ = irr[ (λ _ → ≡.refl) ]

  open IsFunctor

  instance
    -- Functorial on the second component
    ×-isFunctor : ∀ {A : Profunctor I} → IsFunctor I I (A ×_)
    ×-isFunctor {A} .promap pq = map× {P₁ = A} {Q₁ = A} idNat pq
    ×-isFunctor {A} .promap-cong {α = α} {β = β} =
      map×-cong {P₁ = A} {α₁ = idNat} {β₁ = idNat} {α₂ = α} {β₂ = β} (λ _ → ≡.refl)
    ×-isFunctor {A} .promap-id = map×-id A
    ×-isFunctor {A} .promap-∘ pq qr = map×-∘ (idNat {P = A}) pq (idNat {P = A}) qr

module _ {I : Set} where
  open Profunctor
  open NaturalTransformation
  open NaturalIso

  private
    variable
      P Q R : Profunctor I

  π₁ : P × Q ⇒ P
  π₁ .φ = Prod.proj₁
  π₁ .naturality = irr[( λ _ _ _ → ≡.refl )] 

  π₂ : P × Q ⇒ Q
  π₂ .φ = Prod.proj₂
  π₂ .naturality = irr[( λ _ _ _ → ≡.refl )]

  prod : P ⇒ Q → P ⇒ R → P ⇒ Q × R
  prod P⇒Q P⇒R .φ = Prod.< P⇒Q .φ , P⇒R .φ >
  prod P⇒Q P⇒R .naturality =
    P⇒Q .naturality >>= λ natPQ# →
    P⇒R .naturality >>= λ natPR# →
    irr[ (λ f g p → ≡.cong₂ pair (natPQ# f g p) (natPR# f g p) )]
  
  ×-swap : P × Q ⇒ Q × P
  ×-swap .φ = Prod.swap
  ×-swap .naturality = irr[( λ _ _ _ → ≡.refl )]

  ×-assocʳ : (P × Q) × R ⇒ P × (Q × R)
  ×-assocʳ .φ = Prod.assocʳ
  ×-assocʳ .naturality = irr[( λ _ _ _ → ≡.refl )]

  ×-assocˡ : P × (Q × R) ⇒ (P × Q) × R
  ×-assocˡ .φ = Prod.assocˡ
  ×-assocˡ .naturality = irr[( λ _ _ _ → ≡.refl )]

  ×-identityˡ : unit × P ⇔ P
  ×-identityˡ .to = π₂ {P = unit}
  ×-identityˡ .from = prod bang-unit idNat
  ×-identityˡ .to-from = irr[( λ _ → ≡.refl )]
  ×-identityˡ .from-to = irr[( λ _ → ≡.refl )]

  ×-identityʳ : P × unit ⇔ P
  ×-identityʳ .to = π₁ {Q = unit}
  ×-identityʳ .from = prod idNat bang-unit
  ×-identityʳ .to-from = irr[( λ _ → ≡.refl )]
  ×-identityʳ .from-to = irr[( λ _ → ≡.refl )]

  ×-assoc : (P × Q) × R ⇔ P × (Q × R)
  ×-assoc {P} {Q} {R} .to = ×-assocʳ {P} {Q} {R}
  ×-assoc {P} {Q} {R} .from = ×-assocˡ {P} {Q} {R}
  ×-assoc .to-from = irr[ (λ _ → ≡.refl) ]
  ×-assoc .from-to = irr[ (λ _ → ≡.refl) ]

  ×-swapIso : P × Q ⇔ Q × P
  ×-swapIso {P} {Q} .to = ×-swap {P} {Q}
  ×-swapIso {P} {Q} .from = ×-swap {Q} {P}
  ×-swapIso .to-from = irr[ (λ _ → ≡.refl) ]
  ×-swapIso .from-to = irr[ (λ _ → ≡.refl) ]
