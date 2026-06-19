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

-- | Sum of profunctors
module Indexed.Profunctor.Sum where

private
  mapSum : ∀ {A B C D : Set₁} → (A → C) → (B → D)
    → A ⊎ B → C ⊎ D
  mapSum = Sum.map
    -- Sum.map has universe-level-polymorphic type
    -- and they didn't inferred when used directly

  mapSum-id : ∀ {A B} x → mapSum (id {A = A}) (id {A = B}) x ≡ x
  mapSum-id = Sum.[ (λ _ → ≡.refl) , (λ _ → ≡.refl) ]

  mapSum-cong : ∀ {A B C D : Set₁} 
    {f₁ f₂ : A → C} {g₁ g₂ : B → D}
    → f₁ ≗ f₂ → g₁ ≗ g₂ → mapSum f₁ g₁ ≗ mapSum f₂ g₂
  mapSum-cong feq _ (Sum.inj₁ x₁) = ≡.cong Sum.inj₁ (feq x₁)
  mapSum-cong _ geq (Sum.inj₂ x₂) = ≡.cong Sum.inj₂ (geq x₂)

  mapSum-∘ : ∀ {A B C D E F}
    (h₁ : C → E) (j₁ : D → F) (h₂ : A → C) (j₂ : B → D)
    → ∀ x → mapSum (h₁ ∘′ h₂) (j₁ ∘′ j₂) x ≡ mapSum h₁ j₁ (mapSum h₂ j₂ x)
  mapSum-∘ _ _ _ _ = Sum.[ (λ _ → ≡.refl) , (λ _ → ≡.refl) ]

infixr 2 _+_

_+_ : ∀ {I} → Profunctor I → Profunctor I → Profunctor I
_+_ {I} P Q =
  record {
    Carrier = λ a b → P [ a , b ] ⊎ Q [ a , b ];
    dimap = λ f g → mapSum (dimap P f g) (dimap Q f g);
    dimap-id =
      dimap-id P >>= λ dimap-id-P →
      dimap-id Q >>= λ dimap-id-Q →
      irr[( λ x →
        begin
          mapSum (dimap P idᵢ idᵢ) (dimap Q idᵢ idᵢ) x
        ≡⟨ mapSum-cong dimap-id-P dimap-id-Q x ⟩
          mapSum id id x
        ≡⟨ mapSum-id x ⟩
          x
        ∎
      )] ;
    dimap-∘ =
      dimap-∘ P >>= λ dimap-∘-P →
      dimap-∘ Q >>= λ dimap-∘-Q →
      irr[( λ f₁ g₁ f₂ g₂ x →
      let eqP = dimap-∘-P f₁ g₁ f₂ g₂
          eqQ = dimap-∘-Q f₁ g₁ f₂ g₂
      in
        begin
          mapSum (dimap P (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂)) (dimap Q (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂)) x
        ≡⟨ mapSum-cong eqP eqQ x ⟩
          mapSum (dimap P f₁ g₁ ∘′ dimap P f₂ g₂) (dimap Q f₁ g₁ ∘′ dimap Q f₂ g₂) x
        ≡⟨ mapSum-∘ _ _ _ _ x ⟩
          mapSum (dimap P f₁ g₁) (dimap Q f₁ g₁) (mapSum (dimap P f₂ g₂) (dimap Q f₂ g₂) x)
        ∎
    )]
  }
  where
    open Profunctor
    open ≡.≡-Reasoning

-- Functoriality
module _ {I : Set} where
  private
    variable
      P₁ P₂ Q₁ Q₂ R₁ R₂ : Profunctor I
  
  map+ : (P₁ ⇒ Q₁) → (P₂ ⇒ Q₂) → (P₁ + P₂) ⇒ (Q₁ + Q₂)
  map+ α₁ α₂ .φ = mapSum (α₁ .φ) (α₂ .φ)
  map+ α₁ α₂ .naturality =
    α₁ .naturality >>= λ nat₁# →
    α₂ .naturality >>= λ nat₂# →
    irr[( λ f g → λ {
        (Sum.inj₁ p₁) → ≡.cong Sum.inj₁ (nat₁# f g p₁);
        (Sum.inj₂ p₂) → ≡.cong Sum.inj₂ (nat₂# f g p₂)
      }
    )]
   
  map+-cong : ∀ {α₁ β₁ : P₁ ⇒ Q₁} {α₂ β₂ : P₂ ⇒ Q₂}
    → .(α₁ ≈ β₁) → .(α₂ ≈ β₂)
    → Irrelevant (map+ α₁ α₂ ≈ map+ β₁ β₂)
  map+-cong eq₁ eq₂ = irr[ mapSum-cong eq₁ eq₂ ]

  map+-id : (P Q : Profunctor I)
    → Irrelevant (map+ (idNat {P = P}) (idNat {P = Q}) ≈ idNat)
  map+-id _ _ = irr[ mapSum-id ]

  map+-∘ : ∀
    (qr₁ : Q₁ ⇒ R₁) (qr₂ : Q₂ ⇒ R₂) (pq₁ : P₁ ⇒ Q₁) (pq₂ : P₂ ⇒ Q₂)
    → Irrelevant (map+ (qr₁ ∘Nat pq₁) (qr₂ ∘Nat pq₂) ≈ map+ qr₁ qr₂ ∘Nat map+ pq₁ pq₂)
  map+-∘ _ _ _ _ = irr[ mapSum-∘ _ _ _ _ ]

  open IsFunctor

  instance
    -- Functorial on the second component
    +-isFunctor : ∀ {A : Profunctor I} → IsFunctor I I (A +_)
    +-isFunctor {A} .promap pq = map+ {P₁ = A} {Q₁ = A} idNat pq
    +-isFunctor {A} .promap-cong {α = α} {β = β} =
      map+-cong {P₁ = A} {α₁ = idNat} {β₁ = idNat} {α₂ = α} {β₂ = β} (λ _ → ≡.refl)
    +-isFunctor {A} .promap-id = map+-id A
    +-isFunctor {A} .promap-∘ pq qr = map+-∘ (idNat {P = A}) pq (idNat {P = A}) qr

-- Properties of Sum
module _ {I : Set} where
  open NaturalTransformation
  open NaturalIso

  private
    variable
      P Q R : Profunctor I

  inl : P ⇒ P + Q
  inl .φ = Sum.inj₁
  inl .naturality = irr[( λ _ _ _ → ≡.refl )]

  inr : Q ⇒ P + Q
  inr .φ = Sum.inj₂
  inr .naturality = irr[( λ _ _ _ → ≡.refl )]

  either : (P ⇒ R) → (Q ⇒ R) → (P + Q) ⇒ R
  either pr qr .φ = Sum.[ pr .φ , qr .φ ]
  either pr qr .naturality =
    pr .naturality >>= λ pr-nat# →
    qr .naturality >>= λ qr-nat# →
    irr[(
      λ f g → Sum.[ pr-nat# f g , qr-nat# f g ]
    )]
  
  +-swap : P + Q ⇒ Q + P
  +-swap .φ = Sum.swap
  +-swap .naturality = irr[(
      λ f g → Sum.[ (λ _ → ≡.refl) , (λ _ → ≡.refl) ]
    )]

  +-assocʳ : (P + Q) + R ⇒ P + (Q + R)
  +-assocʳ .φ = Sum.assocʳ
  +-assocʳ .naturality = irr[( λ f g →
      λ {
        (Sum.inj₁ (Sum.inj₁ p)) → ≡.refl;
        (Sum.inj₁ (Sum.inj₂ q)) → ≡.refl;
        (Sum.inj₂ r) → ≡.refl 
      }
    )]

  +-assocˡ : P + (Q + R) ⇒ (P + Q) + R
  +-assocˡ .φ = Sum.assocˡ
  +-assocˡ .naturality = irr[( λ f g →
      λ {
        (Sum.inj₁ p) → ≡.refl;
        (Sum.inj₂ (Sum.inj₁ q)) → ≡.refl;
        (Sum.inj₂ (Sum.inj₂ r)) → ≡.refl 
      }
    )]

  +-identityˡ : empty + P ⇔ P
  +-identityˡ .to = either elim-empty idNat
  +-identityˡ .from = inr {P = empty}
  +-identityˡ .to-from = irr[( λ _ → ≡.refl )]
  +-identityˡ .from-to = irr[ Sum.[ (λ ()) , (λ _ → ≡.refl) ] ]

  +-identityʳ : P + empty ⇔ P
  +-identityʳ .to = either idNat elim-empty
  +-identityʳ .from = inl {Q = empty}
  +-identityʳ .to-from = irr[( λ _ → ≡.refl )]
  +-identityʳ .from-to = irr[ Sum.[ (λ _ → ≡.refl), (λ ()) ] ] 

  +-assoc : (P + Q) + R ⇔ P + (Q + R)
  +-assoc {P} {Q} {R} .to = +-assocʳ {P} {Q} {R}
  +-assoc {P} {Q} {R} .from = +-assocˡ {P} {Q} {R}
  +-assoc .to-from = irr[(
      λ {
        (Sum.inj₁ p) → ≡.refl;
        (Sum.inj₂ (Sum.inj₁ q)) → ≡.refl;
        (Sum.inj₂ (Sum.inj₂ r)) → ≡.refl 
      }
    )]
  +-assoc .from-to = irr[(
      λ {
        (Sum.inj₁ (Sum.inj₁ p)) → ≡.refl;
        (Sum.inj₁ (Sum.inj₂ q)) → ≡.refl;
        (Sum.inj₂ r) → ≡.refl 
      }
    )]
  
  +-swapIso : P + Q ⇔ Q + P
  +-swapIso {P} {Q} .to = +-swap {P} {Q}
  +-swapIso {P} {Q} .from = +-swap {Q} {P}
  +-swapIso .to-from = irr[ Sum.[ (λ _ → ≡.refl) , (λ _ → ≡.refl) ] ]
  +-swapIso .from-to = irr[ Sum.[ (λ _ → ≡.refl) , (λ _ → ≡.refl) ] ]
