{-# OPTIONS --without-K --irrelevant-projections #-}

open import Level
open import Function
  using (
    _∘_; _∘′_; _$_; id; const; constᵣ;
    case_of_
  )

import Data.Product as Prod
open import Data.Unit

import Axiom.Extensionality.Propositional as Ext

open import Relation.Binary.PropositionalEquality as ≡
   using (_≡_)

open import Data.Irrelevant
open import ExtensionalityUtil

module Profunctor where

record Profunctor (ℓ : Level) : Set (suc ℓ) where
  field
    Carrier : Set → Set → Set ℓ
  
  private
    P : Set → Set → Set ℓ
    P = Carrier
  
  field
    dimap : ∀ {a a′ b b′} → (a′ → a) → (b → b′) → P a b → P a′ b′

    dimap-id : ∀ {a b} →
      dimap {a = a} {b = b} id id ≡ id
    
    dimap-∘ : ∀ {a a′ a″ b b′ b″}
      →  (f₁ : a″ → a′) (g₁ : b′ → b″) (f₂ : a′ → a) (g₂ : b → b′)
      → dimap (f₂ ∘ f₁) (g₁ ∘ g₂) ≡ dimap f₁ g₁ ∘ dimap f₂ g₂

  lmap : ∀ {a a′ b} → (a′ → a) → P a b → P a′ b
  lmap f = dimap f id

  rmap : ∀ {a b b′} → (b → b′) → P a b → P a b′
  rmap g = dimap id g

Carrier-syntax : ∀ {ℓ} → Profunctor ℓ → Set → Set → Set ℓ
Carrier-syntax = Profunctor.Carrier

syntax Carrier-syntax P a b = P [ a , b ]

-- Instances

hom : Profunctor 0ℓ
hom = record {
    Carrier = λ a b → a → b;
    dimap = λ f g p → g ∘′ p ∘′ f;
    dimap-id = ≡.refl;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

k : (c : Set) → Profunctor 0ℓ
k c = record {
    Carrier = λ _ _ → c;
    dimap = λ _ _ p → p;
    dimap-id = ≡.refl;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

_×_ : ∀ {ℓ} → Profunctor ℓ → Profunctor ℓ → Profunctor ℓ
_×_ P Q = record {
    Carrier = PQ;
    dimap = λ f g → map× (dimap P f g) (dimap Q f g);
    dimap-id = ≡.cong₂ map× (dimap-id P) (dimap-id Q);
    dimap-∘ = λ f₁ g₁ f₂ g₂ →
      ≡.cong₂ map× (dimap-∘ P f₁ g₁ f₂ g₂) (dimap-∘ Q f₁ g₁ f₂ g₂)
  }
  where
    open Profunctor

    PQ : Set → Set → Set _
    PQ a b = P [ a , b ] Prod.× Q [ a , b ]

    map× : ∀ {A B C D : Set _} → (A → C) → (B → D)
      → A Prod.× B → C Prod.× D
    map× f g = Prod.map f g

var : Profunctor 0ℓ
var = record {
    Carrier = λ _ b → b;
    dimap = λ _ g → g;
    dimap-id = ≡.refl;
    dimap-∘ = λ _ _ _ _ → ≡.refl  
  } 

fun : ∀ {ℓ} → Profunctor ℓ → Profunctor ℓ → Profunctor ℓ
fun P Q = record {
    Carrier = PQ;
    dimap = λ f g → map→ (dimap P g f) (dimap Q f g);
    dimap-id = ≡.cong₂ map→ (dimap-id P) (dimap-id Q);
    dimap-∘ = λ f₁ g₁ f₂ g₂ →
      ≡.cong₂ map→ (dimap-∘ P g₂ f₂ g₁ f₁ ) (dimap-∘ Q f₁ g₁ f₂ g₂)
  }
  where
    open Profunctor

    PQ : Set → Set → Set _
    PQ a b = P [ b , a ] → Q [ a , b ]

    map→ : ∀ {A B C D : Set _} → (C → A) → (B → D)
      → (A → B) → (C → D)
    map→ f g p = g ∘′ p ∘′ f

record End {ℓ} (P : Profunctor ℓ)
    : Set (suc zero ⊔ ℓ) where
  open Profunctor P using (lmap; rmap)

  field
    proj : ∀ (a : Set) → P [ a , a ]
  
  Extranaturality : Set _
  Extranaturality = ∀ {a⁻ a⁺} → (h : a⁻ → a⁺) → lmap h (proj a⁺) ≡ rmap h (proj a⁻)
  
  field
    extranaturality : Irrelevant Extranaturality

open End

irrEnd : ∀ {P : Profunctor 0ℓ} {α β : End P}
  → proj α ≡ proj β → α ≡ β
irrEnd ≡.refl = ≡.refl

module example where

  module profunctor-construction where
    -- Complex Profunctor can be made by combination of
    -- `var`, `fun`, `×`.
    _ : Profunctor.Carrier (fun (var × fun var var) var)
          ≡
        (λ a b → a Prod.× (b → a) → b)
    _ = ≡.refl
  
  module parametricity-id where
    -- In Haskell, `id` is the only inhabitant of type `∀ a. a → a`.
    -- The following is the proof of the corresponding statement
    -- in terms of `End`.

    open Profunctor {{...}}

    idEnd : End hom
    idEnd = record {
        proj = λ a → id {A = a};
        extranaturality = [ (λ h → ≡.refl) ]
      }

    Uniqueness : Set₁
    Uniqueness = (α : End hom) → Irrelevant (α ≡ idEnd)

    End-hom-singleton : IrrExtensionality 1ℓ 1ℓ → Uniqueness
    End-hom-singleton irr-ext α = map irrEnd $
      extranaturality α >>= λ exnat →
      irr-ext >>= λ ext →
        [(
          let open Ext1 (lower-extensionality₁ 1ℓ 1ℓ ext)
          in
            ext₁₀ λ a → ext₀₀ λ x →
              begin
                proj α a x
              ≡⟨⟩
                (proj α a ∘ const x) tt 
              ≡⟨ ≡.cong-app (exnat (const x)) tt ⟩
                (const x ∘ proj α ⊤) tt 
              ≡⟨⟩
                x
              ∎
        )]
      where open ≡.≡-Reasoning