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

-- | Profunctors between (I → Set) and itself,
--   their morphisms and isomorphism.
module Indexed.Profunctor.End .(ext : Extensionality 1ℓ 1ℓ) where

open import Indexed.Profunctor
open WithExt ext
open import Indexed.Profunctor.Instances
open InstancesWithExt ext

open import Indexed.Profunctor.Functor

private
  lower-ext₀₀ : Extensionality 1ℓ 1ℓ → Extensionality 0ℓ 0ℓ
  lower-ext₀₀ = lower-extensionality 1ℓ 1ℓ

-- * Preliminary definitions

on-just : ∀ {I : Set} {a b : I → Set} {x : Set}
  → (a ~> b) → maybe′ a x ~> maybe′ b x
on-just f = maybe f id

on-nothing : ∀ {I : Set} {a : I → Set} {x x′ : Set}
  → (x → x′) → maybe′ a x ~> maybe′ a x′
on-nothing h = maybe (λ _ → id) h

private
  on-just-nothing-commute : ∀ {I : Set} {a b : I → Set} {x x′ : Set}
    → (f : a ~> b) (h : x → x′)
    → ∀ mi → (on-just f ∘ᵢ on-nothing h) mi ≡ (on-nothing h ∘ᵢ on-just f) mi
  on-just-nothing-commute f h = λ { nothing  → ≡.refl; (just _) → ≡.refl }

  on-just-id : ∀ {I : Set} (c : I → Set) y → ∀ mi → on-just {x = y} (idᵢ {a = c}) mi ≡ id
  on-just-id _ _ = λ { (just _) → ≡.refl; nothing → ≡.refl }
  
  on-just-∘ : 
      ∀ {I : Set} {a₁ a₂ a₃ : I → Set} {y}
        → (f : a₂ ~> a₃) (g : a₁ ~> a₂)
        → ∀ mi → on-just {x = y} (f ∘ᵢ g) mi ≡ (on-just f ∘ᵢ on-just g) mi
  on-just-∘ _ _ = λ { (just _) → ≡.refl; nothing → ≡.refl }

-- * (one-variable) End of a Profunctor

module _ {I : Set} (P : Profunctor (Maybe I)) where
  open Profunctor P

  record End (a b : I → Set) : Set₁ where
    constructor mkEnd
    
    field
      proj : ∀ (x : Set) → P [ maybe′ a x , maybe′ b x ]
    
    Extranaturality : Set₁
    Extranaturality = ∀ {x⁻ x⁺} → (h : x⁻ → x⁺)
        → lmap (on-nothing h) (proj x⁺) ≡ rmap (on-nothing h) (proj x⁻)
    
    field
      extranaturality : Irrelevant Extranaturality

  open End public

  private
    congEnd : ∀ {a b : I → Set} {p₁ p₂ : End a b}
      → p₁ .proj ≡ p₂ .proj
      → p₁ ≡ p₂
    congEnd ≡.refl = ≡.refl

  -- Extensionality for End.
  -- 
  -- Equality between (p₁ p₂ : End P a b)
  -- can be proven from their contents' pointwise equality.
  -- (uses extensionality for pointwise to function itself,
  --  then uses irrelevance of extranaturality) 
  extEnd : Extensionality 1ℓ 1ℓ
    → ∀ {a b : I → Set} {p₁ p₂ : End a b}
    → (∀ (x : Set) → p₁ .proj x ≡ p₂ .proj x)
    → p₁ ≡ p₂
  extEnd ext projEq = congEnd (ext projEq)

  private
    dimapEnd : ∀ {a a′ b b′ : I → Set} → (a′ ~> a) → (b ~> b′) → End a b → End a′ b′
    dimapEnd f g (mkEnd p _) .proj x = dimap (on-just f) (on-just g) (p x)
    dimapEnd f g (mkEnd p exnat) .extranaturality =
      dimap-∘ >>= λ dimap-∘# →
      exnat >>= λ exnat# →
      irr[( λ {x⁻} {x⁺} h →
        let ext₀₀ = lower-extensionality 1ℓ 1ℓ ext
        in begin
          lmap (on-nothing h) (dimap (on-just f) (on-just g) (p x⁺))
        ≡⟨ dimap-∘# _ _ _ _ (p x⁺) ⟨
          dimap (on-just f ∘ᵢ on-nothing h) (on-just g) (p x⁺)
        ≡⟨ ≡.cong (λ fh → dimap fh (on-just g) (p x⁺)) (ext₀₀ $ on-just-nothing-commute f h) ⟩
          dimap (on-nothing h ∘ᵢ on-just f) (on-just g) (p x⁺)
        ≡⟨ dimap-∘# _ _ _ _ (p x⁺) ⟩
          dimap (on-just f) (on-just g) (lmap (on-nothing h) (p x⁺))
        ≡⟨ ≡.cong (dimap _ _) (exnat# h) ⟩
          dimap (on-just f) (on-just g) (rmap (on-nothing h) (p x⁻))
        ≡⟨ dimap-∘# _ _ _ _ (p x⁻) ⟨
          dimap (on-just f) (on-just g ∘ᵢ on-nothing h) (p x⁻)
        ≡⟨ ≡.cong (λ gh → dimap (on-just f) gh (p x⁻)) (ext₀₀ $ on-just-nothing-commute g h) ⟩
          dimap (on-just f) (on-nothing h ∘ᵢ on-just g) (p x⁻)
        ≡⟨ dimap-∘# _ _ _ _ (p x⁻) ⟩
          rmap (on-nothing h) (dimap (on-just f) (on-just g) (p x⁻))
        ∎
      )]
      where
        open ≡.≡-Reasoning

    dimapEnd-id : Irrelevant (∀ {a b} (p : End a b) → dimapEnd idᵢ idᵢ p ≡ p)
    dimapEnd-id =
      dimap-id >>= λ dimap-id# →
      irr[( λ {a} {b} p → extEnd ext λ x →
        let ext₀₀ = lower-extensionality 1ℓ 1ℓ ext
        in begin
          dimap (on-just idᵢ) (on-just idᵢ) (p .proj x)
        ≡⟨ ≡.cong₂ (λ f g → dimap f g (p .proj x)) (ext₀₀ (on-just-id a x)) (ext₀₀ (on-just-id b x)) ⟩
          dimap idᵢ idᵢ (p .proj x)
        ≡⟨ dimap-id# (p .proj x) ⟩
          p .proj x
        ∎
      )]
      where
        open ≡.≡-Reasoning
    
    dimapEnd-∘ : Irrelevant (
      ∀ {a a′ a″ b b′ b″}
        → (f₁ : a″ ~> a′) (g₁ : b′ ~> b″) (f₂ : a′ ~> a) (g₂ : b ~> b′)
        → (p : End a b)
        → dimapEnd (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂) p ≡ dimapEnd f₁ g₁ (dimapEnd f₂ g₂ p)
      )
    dimapEnd-∘ = 
      dimap-∘ >>= λ dimap-∘# →
      irr[( λ f₁ g₁ f₂ g₂ p → extEnd ext λ x →
        let ext₀₀ = lower-extensionality 1ℓ 1ℓ ext
        in begin
          dimap (on-just (f₂ ∘ᵢ f₁)) (on-just (g₁ ∘ᵢ g₂)) (p .proj x)
        ≡⟨ ≡.cong₂ (λ f g → dimap f g (p .proj x)) (ext₀₀ (on-just-∘ f₂ f₁)) (ext₀₀ (on-just-∘ g₁ g₂)) ⟩
          dimap (on-just f₂ ∘ᵢ on-just f₁) (on-just g₁ ∘ᵢ on-just g₂) (p .proj x)
        ≡⟨ dimap-∘# _ _ _ _ (p .proj x) ⟩
          dimap (on-just f₁) (on-just g₁) (dimap (on-just f₂) (on-just g₂) (p .proj x))
        ∎
      )]
        where
          open ≡.≡-Reasoning
          
  
  EndP : Profunctor I
  EndP .Carrier = End
  EndP .dimap = dimapEnd
  EndP .dimap-id = dimapEnd-id
  EndP .dimap-∘ = dimapEnd-∘

-- TODO:
-- 
-- 1. mapping natural transformation over End:
--   (P ⇒ Q) → (EndP P ⇒ EndP Q)
-- 2. The mapping is functorial
-- 3. The mapping preserves Iso (immediate from 2. but things can be tedious)

module _ {I : Set} where
  open Profunctor

  module _ {P Q : Profunctor (Maybe I)} where
    mapEnd : (P ⇒ Q) -> (EndP P ⇒ EndP Q)
    mapEnd nat .φ eP .proj x = nat .φ (eP .proj x)
    mapEnd nat .φ eP .extranaturality =
      nat .naturality >>= λ naturality# →
      eP .extranaturality >>= λ exnat# →
      irr[(λ {x⁻} {x⁺} h →
        begin
          lmap Q (on-nothing h) (nat .φ (eP .proj x⁺))
        ≡⟨ naturality# _ _ _ ⟨
          nat .φ (lmap P (on-nothing h) (eP .proj x⁺))
        ≡⟨ ≡.cong (nat .φ) (exnat# h) ⟩
          nat .φ (rmap P (on-nothing h) (eP .proj x⁻))
        ≡⟨ naturality# _ _ _ ⟩
          rmap Q (on-nothing h) (nat .φ (eP .proj x⁻))
        ∎
      )]
      where open ≡.≡-Reasoning
        
    mapEnd nat .naturality =
      nat .naturality >>= λ naturality# →
      irr[( λ f g eP → extEnd Q ext λ x →
        naturality# (on-just f) (on-just g) (eP .proj x)
      )]

  mapEnd-cong : ∀ {P Q} {α β : P ⇒ Q}
    → .(α ≈ β)
    → Irrelevant (mapEnd α ≈ mapEnd β)
  mapEnd-cong {Q = Q} eq = irr[( λ eP → extEnd Q ext λ x → eq (eP .proj x) )]

  mapEnd-id : ∀ (P : Profunctor (Maybe I))
    → Irrelevant (mapEnd (idNat {P = P}) ≈ idNat)
  mapEnd-id _ = irr[( λ _ → ≡.refl )]

  mapEnd-∘ : ∀ {P Q R}
    → (natQR : Q ⇒ R) → (natPQ : P ⇒ Q)
    → Irrelevant (mapEnd (natQR ∘Nat natPQ) ≈ mapEnd natQR ∘Nat mapEnd natPQ)
  mapEnd-∘ natQR natPQ = irr[( λ _ → ≡.refl )]

  instance
    EndP-isFunctor : IsFunctor (Maybe I) I EndP
    EndP-isFunctor = record {
        promap = mapEnd;
        promap-cong = λ {P Q} {α β : P ⇒ Q} → mapEnd-cong {α = α} {β = β};
        promap-id = mapEnd-id;
        promap-∘ = mapEnd-∘
      }

  mapEndIso : ∀ {P Q} → (P ⇔ Q) → (EndP P ⇔ EndP Q)
  mapEndIso iso = promapIso EndP iso

-- 4. End commutes with ×
--    EndP (P × Q) ⇔ EndP P × EndP Q
-- 
module _ {I : Set} {P Q : Profunctor (Maybe I)} where
  open Profunctor
  open NaturalIso

  private
    End×⇒Fst : EndP (P × Q) ⇒ EndP P
    End×⇒Fst = mapEnd (π₁ {Q = Q})

    End×⇒Snd : EndP (P × Q) ⇒ EndP Q
    End×⇒Snd = mapEnd (π₂ {P = P})

    End×⇒×End : EndP (P × Q) ⇒ EndP P × EndP Q
    End×⇒×End = prod End×⇒Fst End×⇒Snd

    ×End⇒End× : (EndP P × EndP Q) ⇒ EndP (P × Q)
    ×End⇒End× .φ (pair eP eQ) .proj x = pair (eP .proj x) (eQ .proj x)
    ×End⇒End× .φ (pair eP eQ) .extranaturality =
      eP .extranaturality >>= λ exnatP# →
      eQ .extranaturality >>= λ exnatQ# →
      irr[(
        λ h → ≡.cong₂ pair (exnatP# h) (exnatQ# h)
      )]
    ×End⇒End× .naturality = irr[( λ _ _ _ → ≡.refl )]

  End-×-flip : EndP (P × Q) ⇔ EndP P × EndP Q
  End-×-flip .to = End×⇒×End
  End-×-flip .from = ×End⇒End×
  End-×-flip .to-from = irr[( λ _ → ≡.refl )]
  End-×-flip .from-to = irr[( λ _ → ≡.refl )]

-- 5. End commutes with (fun (k P) _), where k P represents
--    a profunctor which does not use "the outermost variable" 
-- 
--    EndP (fun (k P) Q) ⇔ fun P (EndP Q)
-- 
-- 6. End commutes with End
-- 
--    EndP (EndP P) ⇔ EndP (EndP (mapIndex σ P))
--   
--    where σ : Maybe (Maybe I) → Maybe (Maybe I)
--    is the "swap two nothings" isomorphism

private
  -- Example usage

  module parametricity-id {I : Set} where
    -- Profunctor (a₀ → b₀)
    -- (ignores other type variables)
    fun₀ : Profunctor (Maybe I)
    fun₀ = fun v0 v0

    open Profunctor fun₀

    idEnd : ∀ {a* b*} → End fun₀ a* b*
    idEnd = record {
        proj = λ _ → id;
        extranaturality = irr[( λ _ → ≡.refl )]
      }
    
    private
      -- shorthand
      tt₁ : Lift 1ℓ ⊤
      tt₁ = lift tt
      
      -- Carrier type of fun₀ profunctor, definition unfolded
      -- 
      --   proj α a₀ : fun₀ [ maybe′ a* a₀ , maybe′ b* a₀ ]
      --   proj α a₀ : Lift 1ℓ a₀ → Lift 1ℓ a₀
      _ : ∀ {a b : Maybe I → Set}
        → fun₀ [ a , b ] ≡ (Lift 1ℓ (a nothing) → Lift 1ℓ (b nothing))
      _ = ≡.refl
    
    -- In Haskell, `id` is the only inhabitant of type `∀ a. a → a`.
    -- The following is the corresponding statement in terms of End.
    uniqueness : ∀ {a* b*} → (α : End fun₀ a* b*) → Irrelevant (α ≡ idEnd)
    uniqueness {a*} {b*} α =
      α .extranaturality >>= λ exnat# →
      irr[( 
        extEnd fun₀ ext λ a₀ →
          ext λ x@(lift x₀) →
            begin
              proj α a₀ x
            ≡⟨⟩
              (proj α a₀ ∘′ const x) tt₁
            ≡⟨⟩
              (proj α a₀ ∘ (lift ∘ on-nothing {a = a*} (const x₀) nothing ∘ lower)) tt₁
            ≡⟨ ≡.cong-app (exnat# (const x₀)) tt₁ ⟩
              ((lift ∘ on-nothing {a = b*} (const x₀) nothing ∘ lower) ∘ proj α ⊤) tt₁
            ≡⟨⟩
              (const x ∘ proj α ⊤) tt₁
            ≡⟨⟩
              x
            ∎
      )]
      where
        open ≡.≡-Reasoning
