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

open import Data.Irrelevant
   using (Irrelevant; _>>=_; _<*>_)
   renaming (map to irrmap; [_] to irr[_])
open import ExtensionalityUtil
open import Indexed.Profunctor
open import Indexed.Profunctor.Functor
open import Indexed.Profunctor.Product

-- | "Function" Profunctors
module Indexed.Profunctor.Fun {ℓ} (ext : Extensionality ℓ ℓ) {I} where

open Profunctor
open NaturalTransformation

private
  module _ {A B C D : Set ℓ} where
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

fun : Profunctor ℓ I → Profunctor ℓ I → Profunctor ℓ I
fun P Q = record {
    Carrier = λ a b → P [ b , a ] → Q [ a , b ];
    dimap = λ f g → dimap-fun (dimap P g f) (dimap Q f g);
    dimap-id = λ pq →
        ext (dimap-fun-cong (dimap-id P) (dimap-id Q) pq);
    dimap-∘ = λ f₁ g₁ f₂ g₂ pq →
      let eqP = dimap-∘ P g₂ f₂ g₁ f₁
          eqQ = dimap-∘ Q f₁ g₁ f₂ g₂
      in ext (dimap-fun-cong eqP eqQ pq)
  }
  where
    open Profunctor
    open ≡.≡-Reasoning

module _ {A : Profunctor ℓ I} where
  mapFun : ∀ {P Q : Profunctor ℓ I}
    → (P ⇒ Q) → fun A P ⇒ fun A Q
  mapFun α .φ ap = α .φ ∘′ ap
  mapFun {P} {Q} α .naturality =
    α .naturality >>= λ α-nat# → 
    irr[(λ f g ap → ext λ a →
      begin
        (α .φ ∘′ dimap (fun A P) f g ap) a
      ≡⟨⟩
        (α .φ ∘′ dimap P f g ∘′ ap ∘′ dimap A g f) a
      ≡⟨ α-nat# f g (ap (dimap A g f a)) ⟩
        (dimap Q f g ∘′ α .φ ∘′ ap ∘′ dimap A g f) a
      ≡⟨⟩
        dimap (fun A Q) f g (α .φ ∘′ ap) a
      ∎
    )]
      where open ≡.≡-Reasoning

  mapFun-id : ∀ (P : Profunctor ℓ I)
    → Irrelevant(mapFun (idNat {P = P}) ≈ idNat)
  mapFun-id P = irr[(λ ap → ext (λ a → ≡.refl) )]

  mapFun-∘ : ∀ {P Q R : Profunctor ℓ I}
    → (qr : Q ⇒ R) (pq : P ⇒ Q)
    → Irrelevant (mapFun (qr ∘Nat pq) ≈ (mapFun qr ∘Nat mapFun pq))
  mapFun-∘ qr pq = irr[(λ ap → ext (λ a → ≡.refl))]

  open IsFunctor

  instance
    funIsFunctor : IsFunctor I I (fun A)
    funIsFunctor .promap = mapFun
    funIsFunctor .promap-cong = λ eq → irr[(λ ap → ext (λ a → eq (ap a)))]
    funIsFunctor .promap-id = mapFun-id
    funIsFunctor .promap-∘ = mapFun-∘

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
