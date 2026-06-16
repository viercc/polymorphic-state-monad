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

-- | Various Profunctor constructions
module Indexed.Profunctor.Instances where

open import Indexed.Profunctor

-- * Instances

hom : ∀ {I} → Profunctor I
hom = record {
    Carrier = λ a b → Lift 1ℓ (∀ i → a i → b i);
    dimap = λ f g (lift p) → lift (g ∘ᵢ p ∘ᵢ f);
    dimap-id = irr[( λ _ → ≡.refl )];
    dimap-∘ = irr[( λ _ _ _ _ _ → ≡.refl )]
  }

-- constant profunctor
constant : ∀ {I} → (c : Set) → Profunctor I
constant c = record {
    Carrier = λ _ _ → Lift 1ℓ c;
    dimap = λ _ _ p → p;
    dimap-id = irr[( λ _ → ≡.refl )];
    dimap-∘ = irr[( λ _ _ _ _ _ → ≡.refl )]
  }

-- Special constants
empty unit : ∀ {I} → Profunctor I
empty = constant ⊥
unit = constant ⊤

elim-empty : ∀ {I} {P : Profunctor I}
  → empty ⇒ P
elim-empty .φ = λ ()
elim-empty .naturality = irr[( λ _ _ () )]

bang-unit : ∀ {I} {P : Profunctor I}
  → P ⇒ unit
bang-unit .φ = λ _ → lift tt
bang-unit .naturality = irr[( λ _ _ _ → ≡.refl )]

module _ where

  private
    map+ : ∀ {A B C D : Set₁} → (A → C) → (B → D)
      → A ⊎ B → C ⊎ D
    map+ f g = Sum.map f g

    map+-id : ∀ {A B} x → map+ (id {A = A}) (id {A = B}) x ≡ x
    map+-id (Sum.inj₁ x₁) = ≡.refl
    map+-id (Sum.inj₂ x₂) = ≡.refl

    map+-cong : ∀ {A B C D : Set₁} 
      {f₁ f₂ : A → C} {g₁ g₂ : B → D}
      → f₁ ≗ f₂ → g₁ ≗ g₂ → map+ f₁ g₁ ≗ map+ f₂ g₂
    map+-cong feq _ (Sum.inj₁ x₁) = ≡.cong Sum.inj₁ (feq x₁)
    map+-cong _ geq (Sum.inj₂ x₂) = ≡.cong Sum.inj₂ (geq x₂)

    map+-∘ : ∀ {A B C D E F}
      (h₁ : C → E) (j₁ : D → F) (h₂ : A → C) (j₂ : B → D)
      → ∀ x → map+ (h₁ ∘′ h₂) (j₁ ∘′ j₂) x ≡ map+ h₁ j₁ (map+ h₂ j₂ x)
    map+-∘ _ _ _ _ (Sum.inj₁ _) = ≡.refl
    map+-∘ _ _ _ _ (Sum.inj₂ _) = ≡.refl

  infixr 2 _+_

  _+_ : ∀ {I} → Profunctor I → Profunctor I → Profunctor I
  _+_ {I} P Q =
    record {
      Carrier = λ a b → P [ a , b ] ⊎ Q [ a , b ];
      dimap = λ f g → map+ (dimap P f g) (dimap Q f g);
      dimap-id =
        dimap-id P >>= λ dimap-id-P →
        dimap-id Q >>= λ dimap-id-Q →
        irr[( λ x →
          begin
            map+ (dimap P idᵢ idᵢ) (dimap Q idᵢ idᵢ) x
          ≡⟨ map+-cong dimap-id-P dimap-id-Q x ⟩
            map+ id id x
          ≡⟨ map+-id x ⟩
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
            map+ (dimap P (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂)) (dimap Q (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂)) x
          ≡⟨ map+-cong eqP eqQ x ⟩
            map+ (dimap P f₁ g₁ ∘′ dimap P f₂ g₂) (dimap Q f₁ g₁ ∘′ dimap Q f₂ g₂) x
          ≡⟨ map+-∘ _ _ _ _ x ⟩
            map+ (dimap P f₁ g₁) (dimap Q f₁ g₁) (map+ (dimap P f₂ g₂) (dimap Q f₂ g₂) x)
          ∎
      )]
    }
    where
      open Profunctor
      open ≡.≡-Reasoning

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

var : ∀ {I} → I → Profunctor I
var i = record {
    Carrier = λ _ b → Lift 1ℓ (b i);
    dimap = λ _ g p → lift (g i (lower p)) ;
    dimap-id = irr[( λ _ → ≡.refl )];
    dimap-∘ = irr[( λ _ _ _ _ _ → ≡.refl )]
  }

v0 : ∀ {I} → Profunctor (Maybe I)
v0 = var nothing

k : ∀ {I} → Profunctor I → Profunctor (Maybe I)
k = mapIndex just

module InstancesWithExt .(ext : Extensionality 1ℓ 1ℓ) where
  private
    module _ {A B C D : Set₁} where
      dimap-fun : (B → A) → (C → D) → (A → C) → (B → D)
      dimap-fun pre post f = post ∘′ f ∘′ pre

      dimap-fun-cong : ∀ {pre₁ pre₂ : B → A} {post₁ post₂ : C → D}
        → pre₁ ≗ pre₂ → post₁ ≗ post₂
        → ∀ f x → dimap-fun pre₁ post₁ f x ≡ dimap-fun pre₂ post₂ f x
      dimap-fun-cong {pre₁} {pre₂} {post₁} {post₂} preEq postEq f x = begin
          dimap-fun pre₁ post₁ f x
        ≡⟨⟩
          post₁ (f (pre₁ x))
        ≡⟨ postEq (f (pre₁ x)) ⟩
          post₂ (f (pre₁ x))
        ≡⟨ ≡.cong (post₂ ∘′ f) (preEq x) ⟩
          post₂ (f (pre₂ x))
        ≡⟨⟩
          dimap-fun pre₂ post₂ f x
        ∎
        where open ≡.≡-Reasoning

  fun : ∀{I} → Profunctor I → Profunctor I → Profunctor I
  fun {I} P Q = record {
      Carrier = λ a b → P [ b , a ] → Q [ a , b ];
      dimap = λ f g → dimap-fun (dimap P g f) (dimap Q f g);
      dimap-id = 
        dimap-id P >>= λ dimap-id-P →
        dimap-id Q >>= λ dimap-id-Q →
        irr[( λ pq →
          ext (dimap-fun-cong dimap-id-P dimap-id-Q pq)
        )];
      dimap-∘ = 
        dimap-∘ P >>= λ dimap-∘-P →
        dimap-∘ Q >>= λ dimap-∘-Q →
        irr[( λ f₁ g₁ f₂ g₂ pq →
        let eqP = dimap-∘-P g₂ f₂ g₁ f₁
            eqQ = dimap-∘-Q f₁ g₁ f₂ g₂
        in ext (dimap-fun-cong eqP eqQ pq)
        )]
    }
    where
      open Profunctor
      open ≡.≡-Reasoning
      

-- TODO:
-- 
-- 1. Profunctor "behaves like" Set on sum, product, fun.
-- 
--    - [x] _+_ is monoidal (with unit = constant ⊥)
--    - [x] _×_ is monoidal (with unit = constant ⊤)
--    - [_] _×_ distributes over _+_
--    - [_] Adjunction (_× P) ⊣ (fun P)
--      - currying, uncurrying (, evaluation, coevaluation)
--      - fun (P + Q) R ⇔ fun P R × fun Q R

private
  module examples .(ext : Extensionality 1ℓ 1ℓ) where
    open InstancesWithExt ext

    _ : ∀ a b →
      (fun (v0 {⊥} × fun v0 v0) v0) [ a , b ]
        ≡ let
            a₀ = Lift 1ℓ (a nothing)
            b₀ = Lift 1ℓ (b nothing)
          in a₀ Prod.× (b₀ → a₀) → b₀
    _ = λ a b → ≡.refl
