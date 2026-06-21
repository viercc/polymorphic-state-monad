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
open import Indexed.Profunctor

-- | Functors between Profunctors
module Indexed.Profunctor.Functor where

record IsFunctor
  {ℓ ℓ'} (I J : Set) (F : Profunctor ℓ I → Profunctor ℓ' J) : Set (suc (ℓ ⊔ ℓ' ⊔ suc 0ℓ)) where

  field
    promap : ∀ {P Q : Profunctor ℓ I}
      → P ⇒ Q → F P ⇒ F Q

    promap-cong : ∀ {P Q : Profunctor ℓ I} {α β : P ⇒ Q}
      → .(α ≈ β) → Irrelevant (promap α ≈ promap β)
    
    promap-id : ∀ (P : Profunctor ℓ I)
      → Irrelevant (promap (idNat {P = P}) ≈ idNat)
    
    promap-∘ : ∀ {P Q R : Profunctor ℓ I}
      → (qr : Q ⇒ R) (pq : P ⇒ Q)
      → Irrelevant (promap (qr ∘Nat pq) ≈ (promap qr ∘Nat promap pq))

open IsFunctor {{...}}

-- mapIndex is a Profunctor Functor
module _ {ℓ : Level} {I J : Set} {t : I → J} where
  instance
    mapIndexIsFunctor : IsFunctor {ℓ = ℓ} {ℓ' = ℓ} I J (mapIndex t)
    mapIndexIsFunctor .promap pq .φ = pq .φ
    mapIndexIsFunctor .promap-cong α≈β = irr[ α≈β ]
    mapIndexIsFunctor .promap pq .naturality =
      pq .naturality >>= λ nat# →
      irr[( λ f g x → nat# (f ∘ t) (g ∘ t) x )]
    mapIndexIsFunctor .promap-id _ = irr[( λ _ → ≡.refl )]
    mapIndexIsFunctor .promap-∘ _ _ = irr[( λ _ → ≡.refl )]

-- Profunctor Functor preserves NaturalIso
module _ {ℓ ℓ' : Level} {I J : Set} where
  open NaturalIso

  promapRightInv : ∀ (F : Profunctor ℓ I → Profunctor ℓ' J)
    {{ isFunctor : IsFunctor I J F }}
    → ∀ {P Q : Profunctor ℓ I}
    → (α : P ⇒ Q) → (β : Q ⇒ P)
    → .(α ∘Nat β ≈ idNat)
    → Irrelevant (promap α ∘Nat promap {{isFunctor}} β ≈ idNat)
  promapRightInv F {{inst}} {Q = Q} α β αβ-id =
    promap-cong {{inst}} αβ-id >>= λ promap-αβ-id# →
    promap-id Q >>= λ promap-id# →
    promap-∘ α β >>= λ promap-∘# →
    irr[( λ fq → begin
        promap α .φ (promap β .φ fq)
      ≡⟨ promap-∘# fq ⟨
        promap (α ∘Nat β) .φ fq
      ≡⟨ promap-αβ-id# fq ⟩
        promap (idNat {P = Q}) .φ fq
      ≡⟨ promap-id# fq ⟩
        fq
      ∎ )]
    where open ≡.≡-Reasoning

  promapIso : ∀ (F : Profunctor ℓ I → Profunctor ℓ' J)
    {{ isFunctor : IsFunctor I J F }}
    → ∀ {P Q : Profunctor ℓ I}
    → (P ⇔ Q) → F P ⇔ F Q
  promapIso F P⇔Q .to = promap (P⇔Q .to)
  promapIso F P⇔Q .from = promap (P⇔Q .from)
  promapIso F {Q = Q} P⇔Q .to-from =
    P⇔Q .to-from >>= promapRightInv F (P⇔Q .to) (P⇔Q .from)
  promapIso F P⇔Q .from-to = 
    P⇔Q .from-to >>= promapRightInv F (P⇔Q .from) (P⇔Q .to)
