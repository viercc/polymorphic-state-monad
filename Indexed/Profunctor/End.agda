{-# OPTIONS --without-K --irrelevant-projections #-}

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
module Indexed.Profunctor.End (irr-ext : IrrExtensionality 1ℓ 1ℓ) where

open import Indexed.Profunctor irr-ext

private
  .ext₁₁ : Extensionality 1ℓ 1ℓ
  ext₁₁ = irrelevant irr-ext

  .ext₀₀ : Extensionality 0ℓ 0ℓ
  ext₀₀ = lower-extensionality 1ℓ 1ℓ ext₁₁

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
      .extranaturality : Extranaturality

  open End public

  -- Extensionality for End.
  -- 
  -- Equality between (p₁ p₂ : End P a b)
  -- can be proven from their contents' pointwise equality.
  -- (uses extensionality for pointwise to function itself,
  --  then uses irrelevance of extranaturality) 
  .extEnd : ∀ {a b : I → Set} {p₁ p₂ : End a b}
    → (∀ (x : Set) → p₁ .proj x ≡ p₂ .proj x)
    → p₁ ≡ p₂
  extEnd {p₁ = p₁} {p₂ = p₂} projEq with ext₁₁ projEq
  ... | ≡.refl = ≡.refl

  private
    dimapEnd : ∀ {a a′ b b′ : I → Set} → (a′ ~> a) → (b ~> b′) → End a b → End a′ b′
    dimapEnd f g (mkEnd p _) .proj x = dimap (on-just f) (on-just g) (p x)
    dimapEnd f g (mkEnd p exnatP) .extranaturality {x⁻} {x⁺} h =
      begin
        lmap (on-nothing h) (dimap (on-just f) (on-just g) (p x⁺))
      ≡⟨ ≡.cong-app (dimap-∘ _ _ _ _) (p x⁺) ⟨
        dimap (on-just f ∘ᵢ on-nothing h) (on-just g) (p x⁺)
      ≡⟨ ≡.cong (λ fh → dimap fh (on-just g) (p x⁺)) (ext₀₀ $ on-just-nothing-commute f h) ⟩
        dimap (on-nothing h ∘ᵢ on-just f) (on-just g) (p x⁺)
      ≡⟨ ≡.cong-app (dimap-∘ _ _ _ _) (p x⁺) ⟩
        dimap (on-just f) (on-just g) (lmap (on-nothing h) (p x⁺))
      ≡⟨ ≡.cong (dimap _ _) (exnatP h) ⟩
        dimap (on-just f) (on-just g) (rmap (on-nothing h) (p x⁻))
      ≡⟨ ≡.cong-app (dimap-∘ _ _ _ _) (p x⁻) ⟨
        dimap (on-just f) (on-just g ∘ᵢ on-nothing h) (p x⁻)
      ≡⟨ ≡.cong (λ gh → dimap (on-just f) gh (p x⁻)) (ext₀₀ $ on-just-nothing-commute g h) ⟩
        dimap (on-just f) (on-nothing h ∘ᵢ on-just g) (p x⁻)
      ≡⟨ ≡.cong-app (dimap-∘ _ _ _ _) (p x⁻) ⟩
        rmap (on-nothing h) (dimap (on-just f) (on-just g) (p x⁻))
      ∎
      where
        open ≡.≡-Reasoning

    .dimapEnd-id : ∀ {a b}
      → dimapEnd {a = a} {b = b} idᵢ idᵢ ≡ id
    dimapEnd-id = ext₁₁ λ p → extEnd λ x →
      begin
        dimap (on-just idᵢ) (on-just idᵢ) (p .proj x)
      ≡⟨ ≡.cong₂ (λ f g → dimap f g (p .proj x)) on-just-id on-just-id ⟩
        dimap idᵢ idᵢ (p .proj x)
      ≡⟨ ≡.cong-app dimap-id (p .proj x) ⟩
        p .proj x
      ∎
      where
        open ≡.≡-Reasoning
        
        on-just-id : ∀ {c} {y} → on-just {x = y} (idᵢ {a = c}) ≡ idᵢ
        on-just-id = ext₀₀ λ { (just _) → ≡.refl; nothing → ≡.refl } 
    
    .dimapEnd-∘ : ∀ {a a′ a″ b b′ b″}
      → (f₁ : a″ ~> a′) (g₁ : b′ ~> b″) (f₂ : a′ ~> a) (g₂ : b ~> b′)
      → dimapEnd (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂) ≡ dimapEnd f₁ g₁ ∘′ dimapEnd f₂ g₂
    dimapEnd-∘ f₁ g₁ f₂ g₂ = ext₁₁ λ p → extEnd λ x →
        begin
          dimap (on-just (f₂ ∘ᵢ f₁)) (on-just (g₁ ∘ᵢ g₂)) (p .proj x)
        ≡⟨ ≡.cong₂ (λ f g → dimap f g (p .proj x)) (on-just-∘ _ _) (on-just-∘ _ _) ⟩
          dimap (on-just f₂ ∘ᵢ on-just f₁) (on-just g₁ ∘ᵢ on-just g₂) (p .proj x)
        ≡⟨ ≡.cong-app (dimap-∘ _ _ _ _) (p .proj x) ⟩
          dimap (on-just f₁) (on-just g₁) (dimap (on-just f₂) (on-just g₂) (p .proj x))
        ∎
        where
          open ≡.≡-Reasoning
          
          on-just-∘ : ∀ {a₁ a₂ a₃} {y}
            → (f : a₂ ~> a₃) (g : a₁ ~> a₂)
            → on-just {x = y} (f ∘ᵢ g) ≡ on-just f ∘ᵢ on-just g
          on-just-∘ f g = ext₀₀ λ { (just _) → ≡.refl; nothing → ≡.refl }
  
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
-- 4. End commutes with ×
--    EndP (P × Q) ⇔ EndP P × EndP Q
-- 
-- 5. End commutes with (fun (k P) _), where k P represents
--    a profunctor which does not use "the outermost variable" 
-- 
--    EndP (fun (k P) Q) ⇔ fun P (EndP Q)
-- 
-- 6. End commutes with End
-- 
--    EndP (EndP P) ⇔ EndP (EndP (σ ⋆ P))
--   
--    where σ : Maybe (Maybe I) → Maybe (Maybe I)
--    is the "swap two nothings" isomorphism

module parametricity-id {I : Set} where
  -- Profunctor (a₀ → b₀)
  -- (ignores other type variables)
  fun₀ : Profunctor (Maybe I)
  fun₀ = fun v0 v0

  open Profunctor fun₀

  idEnd : ∀ {a* b*} → End fun₀ a* b*
  idEnd = record {
      proj = λ _ → id;
      extranaturality = λ _ → ≡.refl
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

    .End-hom-contr : ∀ {a* b*} → (α : End fun₀ a* b*) → α ≡ idEnd
    End-hom-contr {a*} {b*} α =
      extEnd fun₀ λ a₀ →
        ext₁₁ λ x@(lift x₀) →
          begin
            proj α a₀ x
          ≡⟨⟩
            (proj α a₀ ∘′ const x) tt₁
          ≡⟨⟩
            (proj α a₀ ∘ (lift ∘ on-nothing {a = a*} (const x₀) nothing ∘ lower)) tt₁
          ≡⟨ ≡.cong-app (extranaturality α (const x₀)) tt₁ ⟩
            ((lift ∘ on-nothing {a = b*} (const x₀) nothing ∘ lower) ∘ proj α ⊤) tt₁
          ≡⟨⟩
            (const x ∘ proj α ⊤) tt₁
          ≡⟨⟩
            x
          ∎
        where open ≡.≡-Reasoning
  
  -- In Haskell, `id` is the only inhabitant of type `∀ a. a → a`.
  -- The following is the corresponding statement in terms of End.
  uniqueness : ∀ {a* b*} → (α : End fun₀ a* b*) → Irrelevant (α ≡ idEnd)
  uniqueness α = [ End-hom-contr α ]
