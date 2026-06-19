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

module _ where
  private
    map× : ∀ {A B C D : Set₁} → (A → C) → (B → D)
      → A Prod.× B → C Prod.× D
    map× f g = Prod.map f g

  infixr 3 _×_

  _×_ : ∀ {I} → Profunctor I → Profunctor I → Profunctor I
  _×_ {I} P Q =
    record {
      Carrier = λ a b → P [ a , b ] Prod.× Q [ a , b ];
      dimap = λ f g → map× (dimap P f g) (dimap Q f g);
      dimap-id = 
        dimap-id P >>= λ dimap-id-P →
        dimap-id Q >>= λ dimap-id-Q →
        irr[( λ (pair x₁ x₂) →
          ≡.cong₂ pair (dimap-id-P x₁) (dimap-id-Q x₂)
        )];
      dimap-∘ = 
        dimap-∘ P >>= λ dimap-∘-P →
        dimap-∘ Q >>= λ dimap-∘-Q →
        irr[( λ f₁ g₁ f₂ g₂ (pair x₁ x₂) →
          let eqP = dimap-∘-P f₁ g₁ f₂ g₂ x₁
              eqQ = dimap-∘-Q f₁ g₁ f₂ g₂ x₂
          in ≡.cong₂ Prod._,_ eqP eqQ 
        )]
    }
    where
      open Profunctor
  
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
