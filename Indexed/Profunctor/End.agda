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

-- | (One-parameter) End of a Profunctor.
--   
--   Sends Profunctor (Maybe I) to Profunctor I
--   which has been "quotiented away" one parameter.
module Indexed.Profunctor.End (ext : Extensionality 1ℓ 1ℓ) where

open import Indexed.Profunctor
open WithExt ext
open import Indexed.Profunctor.Functor

open import Indexed.Profunctor.Product
import Indexed.Profunctor.Fun as Fun

private
  ext₀₀ : Extensionality 0ℓ 0ℓ
  ext₀₀ = lower-extensionality 1ℓ 1ℓ ext

-- * Preliminary definitions

infix 19 _::_

_::_ : ∀ {I : Set} (a : I → Set) (x : Set) → Maybe I → Set 
_::_ = maybe′

module MaybeIndex {I : Set} where
  on-just : ∀ {a b : I → Set} {x : Set}
    → (a ~> b) → a :: x ~> b :: x
  on-just f = maybe f id

  on-nothing : ∀ {a : I → Set} {x x′ : Set}
    → (x → x′) → a :: x ~> a :: x′
  on-nothing h = maybe (λ _ → id) h

  on-just-nothing-commute : ∀ {a b : I → Set} {x x′ : Set}
    → (f : a ~> b) (h : x → x′)
    → ∀ mi → (on-just f ∘ᵢ on-nothing h) mi ≡ (on-nothing h ∘ᵢ on-just f) mi
  on-just-nothing-commute _ _ = λ { (just _) → ≡.refl; nothing → ≡.refl }

  on-nothing-id : ∀ (a : I → Set) (x : Set)
    → ∀ mi → on-nothing {a = a} {x = x} id mi ≡ id
  on-nothing-id _ _ = λ { (just _) → ≡.refl; nothing → ≡.refl }
  
  on-nothing-∘ : ∀ {a : I → Set} {x₁ x₂ x₃ : Set}
    → (f : x₂ → x₃) (g : x₁ → x₂)
    → ∀ mi → on-nothing {a = a} (f ∘′ g) mi ≡ (on-nothing f ∘ᵢ on-nothing g) mi
  on-nothing-∘ _ _ = λ { (just _) → ≡.refl; nothing → ≡.refl }

  on-just-id : ∀ (c : I → Set) y → ∀ mi → on-just {x = y} (idᵢ {a = c}) mi ≡ id
  on-just-id _ _ = λ { (just _) → ≡.refl; nothing → ≡.refl }
  
  on-just-∘ : 
      ∀ {a₁ a₂ a₃ : I → Set} {y}
        → (f : a₂ ~> a₃) (g : a₁ ~> a₂)
        → ∀ mi → on-just {x = y} (f ∘ᵢ g) mi ≡ (on-just f ∘ᵢ on-just g) mi
  on-just-∘ _ _ = λ { (just _) → ≡.refl; nothing → ≡.refl }

module MaybeIndexProfunctor {I} {ℓ} (P : Profunctor ℓ (Maybe I)) where
  open MaybeIndex
  open Profunctor P

  dimap-on-nothing : ∀ {a b x x' y y'}
    → (x' → x) → (y → y')
    → P [ a :: x , b :: y ] → P [ a :: x' , b :: y' ]
  dimap-on-nothing f g = dimap (on-nothing f) (on-nothing g)

  lmap-on-nothing : ∀ {a b x x' y}
    → (x' → x)
    → P [ a :: x , b :: y ] → P [ a :: x' , b :: y ]
  lmap-on-nothing f = dimap-on-nothing f id

  rmap-on-nothing : ∀ {a b x y y'}
    → (y → y')
    → P [ a :: x , b :: y ] → P [ a :: x , b :: y' ]
  rmap-on-nothing g = dimap-on-nothing id g

  dimap-on-just : ∀ {a a' b b' x y}
    → (a' ~> a) → (b ~> b')
    → P [ a :: x , b :: y ] → P [ a' :: x , b' :: y ]
  dimap-on-just f g = dimap (on-just f) (on-just g)

  dimap-on-nothing-id : ∀ {a b x y}
    → ∀ (p : P [ a :: x , b :: y ]) → dimap-on-nothing id id p ≡ p
  dimap-on-nothing-id p = ≡.trans
    (≡.cong₂ (λ f g → dimap f g p) (ext₀₀ (on-nothing-id _ _)) (ext₀₀ (on-nothing-id _ _)))
    (dimap-id p)

  dimap-on-nothing-∘ : ∀ {a b x₁ x₂ x₃ y₁ y₂ y₃}
    → (f₃₂ : x₃ → x₂) (g₂₃ : y₂ → y₃)
      (f₂₁ : x₂ → x₁) (g₁₂ : y₁ → y₂)
    → dimap-on-nothing {a = a} {b = b} (f₂₁ ∘′ f₃₂) (g₂₃ ∘′ g₁₂) ≗ dimap-on-nothing f₃₂ g₂₃ ∘′ dimap-on-nothing f₂₁ g₁₂
  dimap-on-nothing-∘ f₃₂ g₂₃ f₂₁ g₁₂ p = ≡.trans
    (≡.cong₂ (λ f g → dimap f g p)
      (ext₀₀ (on-nothing-∘ f₂₁ f₃₂))
      (ext₀₀ (on-nothing-∘ g₂₃ g₁₂)))
    (dimap-∘ (on-nothing _) (on-nothing _) (on-nothing _) (on-nothing _) p)

  dimap-on-just-id : ∀ {a b x y}
    → ∀ (p : P [ a :: x , b :: y ]) → dimap-on-just idᵢ idᵢ p ≡ p
  dimap-on-just-id p = ≡.trans
    (≡.cong₂ (λ f g → dimap f g p) (ext₀₀ (on-just-id _ _)) (ext₀₀ (on-just-id _ _)))
    (dimap-id p)

  dimap-on-just-∘ : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ x y}
    → (f₃₂ : a₃ ~> a₂) (g₂₃ : b₂ ~> b₃)
      (f₂₁ : a₂ ~> a₁) (g₁₂ : b₁ ~> b₂)
    → dimap-on-just {x = x} {y = y} (f₂₁ ∘ᵢ f₃₂) (g₂₃ ∘ᵢ g₁₂) ≗ dimap-on-just f₃₂ g₂₃ ∘′ dimap-on-just f₂₁ g₁₂
  dimap-on-just-∘ f₃₂ g₂₃ f₂₁ g₁₂ p = ≡.trans
    (≡.cong₂ (λ f g → dimap f g p)
      (ext₀₀ (on-just-∘ f₂₁ f₃₂))
      (ext₀₀ (on-just-∘ g₂₃ g₁₂)))
    (dimap-∘ (on-just _) (on-just _) (on-just _) (on-just _) p)

  dimap-on-just-nothing-comm : ∀ {a a' b b' x x' y y'}
    → (fj : a' ~> a) (gj : b ~> b') (f : x' → x) (g : y → y')
    → dimap-on-just fj gj ∘′ dimap-on-nothing f g ≗ dimap-on-nothing f g ∘′ dimap-on-just fj gj
  dimap-on-just-nothing-comm fj gj f g p = begin
      dimap-on-just fj gj (dimap-on-nothing f g p)
    ≡⟨ dimap-∘ (on-just fj) (on-just gj) (on-nothing f) (on-nothing g) p ⟨
      dimap (on-nothing f ∘ᵢ on-just fj) (on-just gj ∘ᵢ on-nothing g) p
    ≡⟨ ≡.cong₂ (λ fm gm → dimap fm gm p)
        (ext₀₀ λ { (just _) → ≡.refl; nothing → ≡.refl })
        (ext₀₀ λ { (just _) → ≡.refl; nothing → ≡.refl }) ⟩
      dimap (on-just fj ∘ᵢ on-nothing f) (on-nothing g ∘ᵢ on-just gj) p
    ≡⟨ dimap-∘ (on-nothing f) (on-nothing g) (on-just fj) (on-just gj) p ⟩
      dimap-on-nothing f g (dimap-on-just fj gj p)
    ∎
    where open ≡.≡-Reasoning

open MaybeIndex

-- * One-parameter End of a Profunctor

module _ {I : Set} (P : Profunctor 1ℓ (Maybe I)) where
  open Profunctor P
  open MaybeIndexProfunctor P

  Extranaturality : (a b : I → Set)
    → (∀ (x : Set) → P [ a :: x , b :: x ])
    → Set₁
  Extranaturality a b proj = ∀ {x⁻ x⁺} (h : x⁻ → x⁺)
    → lmap-on-nothing h (proj x⁺) ≡ rmap-on-nothing h (proj x⁻)

  record End (a b : I → Set) : Set₁ where
    constructor mkEnd
    
    field
      proj : ∀ (x : Set) → P [ a :: x , b :: x ]
    
    field
      extranaturality : Irrelevant (Extranaturality a b proj)

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
  extEnd : ∀ {a b : I → Set} {p₁ p₂ : End a b}
    → (∀ (x : Set) → p₁ .proj x ≡ p₂ .proj x)
    → p₁ ≡ p₂
  extEnd projEq = congEnd (ext projEq)

  private
    dimapEnd : ∀ {a a′ b b′ : I → Set} → (a′ ~> a) → (b ~> b′) → End a b → End a′ b′
    dimapEnd f g (mkEnd p _) .proj x = dimap-on-just f g (p x)
    dimapEnd f g (mkEnd p exnat) .extranaturality =
      exnat >>= λ exnat# →
      irr[( λ {x⁻} {x⁺} h →
        begin
          lmap-on-nothing h (dimap-on-just f g (p x⁺))
        ≡⟨ dimap-on-just-nothing-comm _ _ _ _ (p x⁺) ⟨
          dimap-on-just f g (lmap-on-nothing h (p x⁺))
        ≡⟨ ≡.cong (dimap-on-just f g) (exnat# h) ⟩
          dimap-on-just f g (rmap-on-nothing h (p x⁻))
        ≡⟨ dimap-on-just-nothing-comm _ _ _ _ (p x⁻) ⟩
          rmap-on-nothing h (dimap-on-just f g (p x⁻))
        ∎
      )]
      where
        open ≡.≡-Reasoning

    dimapEnd-id : ∀ {a b} (p : End a b) → dimapEnd idᵢ idᵢ p ≡ p
    dimapEnd-id p = extEnd λ x → dimap-on-just-id (p .proj x)
    
    dimapEnd-∘ :
      ∀ {a a′ a″ b b′ b″}
        → (f₁ : a″ ~> a′) (g₁ : b′ ~> b″) (f₂ : a′ ~> a) (g₂ : b ~> b′)
        → (p : End a b)
        → dimapEnd (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂) p ≡ dimapEnd f₁ g₁ (dimapEnd f₂ g₂ p)
    dimapEnd-∘ f₁ g₁ f₂ g₂ p = extEnd λ x →
      dimap-on-just-∘ f₁ g₁ f₂ g₂ (p .proj x)          
  
  EndP : Profunctor 1ℓ I
  EndP .Carrier = End
  EndP .dimap = dimapEnd
  EndP .dimap-id = dimapEnd-id
  EndP .dimap-∘ = dimapEnd-∘

module _ {I : Set} where
  open Profunctor
  open MaybeIndexProfunctor

  -- 1. mapping natural transformation over End:
  --   (P ⇒ Q) → (EndP P ⇒ EndP Q)
  module _ {P Q : Profunctor 1ℓ (Maybe I)} where
    mapEnd : (P ⇒ Q) -> (EndP P ⇒ EndP Q)
    mapEnd nat .φ eP .proj x = nat .φ (eP .proj x)
    mapEnd nat .φ eP .extranaturality =
      nat .naturality >>= λ naturality# →
      eP .extranaturality >>= λ exnat# →
      irr[(λ {x⁻} {x⁺} h →
        begin
          lmap-on-nothing Q h (nat .φ (eP .proj x⁺))
        ≡⟨ naturality# _ _ _ ⟨
          nat .φ (lmap-on-nothing P h (eP .proj x⁺))
        ≡⟨ ≡.cong (nat .φ) (exnat# h) ⟩
          nat .φ (rmap-on-nothing P h (eP .proj x⁻))
        ≡⟨ naturality# _ _ _ ⟩
          rmap-on-nothing Q h (nat .φ (eP .proj x⁻))
        ∎
      )]
      where open ≡.≡-Reasoning
        
    mapEnd nat .naturality =
      nat .naturality >>= λ naturality# →
      irr[( λ f g eP → extEnd Q λ x →
        naturality# (on-just f) (on-just g) (eP .proj x)
      )]

  -- 2. The mapping is functorial

  mapEnd-cong : ∀ {P Q} {α β : P ⇒ Q}
    → .(α ≈ β)
    → Irrelevant (mapEnd α ≈ mapEnd β)
  mapEnd-cong {Q = Q} eq = irr[( λ eP → extEnd Q λ x → eq (eP .proj x) )]

  mapEnd-id : ∀ (P : Profunctor 1ℓ (Maybe I))
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

  -- 3. The mapping preserves Iso

  mapEndIso : ∀ {P Q} → (P ⇔ Q) → (EndP P ⇔ EndP Q)
  mapEndIso iso = promapIso EndP iso

-- 4. End commutes with ×
--    EndP (P × Q) ⇔ EndP P × EndP Q
module _ {I : Set} {P Q : Profunctor 1ℓ (Maybe I)} where
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

-- 5. End can be moved insode (fun (k P) _), where k P represents
--    a profunctor which does not use "the outermost variable" 
-- 
--      EndP (fun (k P) Q) ⇒ fun P (EndP Q)
-- 
--    The converse direction would require a choice-like principle for
--    irrelevant proofs:
--
--      (∀ p → Irrelevant (R p)) → Irrelevant (∀ p → R p)
--
--    This is not available without --irrelevant-projections, and that flag
--    is non-conservative/unsafe.  Therefore we deliberately do not provide
--    FunEnd⇒EndFun.

module _ {I : Set} {P : Profunctor 1ℓ I} {Q : Profunctor 1ℓ (Maybe I)} where
  open Fun {ℓ = 1ℓ} ext
  open Profunctor
  open MaybeIndexProfunctor
  open NaturalIso

  private
    -- lemma
    lmap-on-nothing-fun : ∀ {a* b* : I → Set}
        → {x x' y : Set} (h : x' → x)
        → (pq : P [ b* , a* ] → Q [ maybe′ a* x , maybe′ b* y ])
        → ∀ p → lmap-on-nothing (fun (k P) Q) h pq p ≡ lmap-on-nothing Q h (pq p)
    lmap-on-nothing-fun {x = x} {x' = x'} h pq p =
      begin
        lmap-on-nothing (fun (k P) Q) h pq p
      ≡⟨⟩
        (lmap-on-nothing Q h ∘′ pq ∘′ rmap-on-nothing (k P) {x = x'} h) p
      ≡⟨⟩
        (lmap-on-nothing Q h ∘′ pq ∘′ dimap P idᵢ idᵢ) p
      ≡⟨ ≡.cong (lmap-on-nothing Q h ∘′ pq) (dimap-id P p) ⟩
        lmap-on-nothing Q h (pq p)
      ∎
      where open ≡.≡-Reasoning
    
    rmap-on-nothing-fun : ∀ {a* b* : I → Set}
        → {x y y' : Set} (h : y → y')
        → (pq : P [ b* , a* ] → Q [ maybe′ a* x , maybe′ b* y ])
        → ∀ p → rmap-on-nothing (fun (k P) Q) h pq p ≡ rmap-on-nothing Q h (pq p)
    rmap-on-nothing-fun h pq p =
      -- Reasoning steps are omitted (as they are refl except one step),
      -- because the proof is almost same for lmap
      ≡.cong (rmap-on-nothing Q h ∘′ pq) (dimap-id P p)

  EndFun⇒FunEnd : EndP (fun (k P) Q) ⇒ fun P (EndP Q)
  EndFun⇒FunEnd .φ ePQ p .proj x = ePQ .proj x p
  EndFun⇒FunEnd .φ {a*} {b*} ePQ p .extranaturality =
    ePQ .extranaturality >>= λ exnat# →
    irr[(λ {x⁻ x⁺} h → begin
        lmap-on-nothing Q h (ePQ .proj x⁺ p)
      ≡⟨ lmap-on-nothing-fun h (ePQ .proj x⁺) p ⟨
        lmap-on-nothing (fun (k P) Q) h (ePQ .proj x⁺) p
      ≡⟨ ≡.cong-app (exnat# h) p ⟩
        rmap-on-nothing (fun (k P) Q) h (ePQ .proj x⁻) p
      ≡⟨ rmap-on-nothing-fun h (ePQ .proj x⁻) p ⟩
        rmap-on-nothing Q h (ePQ .proj x⁻ p)
      ∎
    )]
    where open ≡.≡-Reasoning
  EndFun⇒FunEnd .naturality = irr[( λ _ _ _ → ≡.refl )]



-- 6. End commutes with End
-- 
--    EndP (EndP P) ⇔ EndP (EndP (mapIndex σ P))
--    
--    where σ : Maybe (Maybe I) → Maybe (Maybe I)
--    is the "swap two nothings" isomorphism
-- 
-- TODO!

private
  -- Example usage

  module parametricity-id {I : Set} where
    open Profunctor
    open Fun {ℓ = 0ℓ} (lower-extensionality 1ℓ 1ℓ ext)

    x→x : Profunctor 1ℓ (Maybe I)
    x→x = LiftP 1ℓ (fun v0 v0)

    idEnd : ∀ {a* b*} → End x→x a* b*
    idEnd = record {
        proj = λ _ → lift id;
        extranaturality = irr[( λ _ → ≡.refl )]
      }
    
    private
      -- shorthand
      tt₁ : Lift 1ℓ ⊤
      tt₁ = lift tt
      
      _ : ∀ {a b : Maybe I → Set}
        → x→x [ a , b ] ≡ Lift 1ℓ (a nothing → b nothing)
      _ = ≡.refl
    
    -- In Haskell, `id` is the only inhabitant of type `∀ a. a → a`.
    -- The following is the corresponding statement in terms of End.
    uniqueness : ∀ {a* b*} → (α : End x→x a* b*) → Irrelevant (α ≡ idEnd)
    uniqueness {a*} {b*} α =
      α .extranaturality >>= λ exnat# →
      irr[( 
        extEnd x→x λ a₀ → ≡.cong lift $
          ext₀₀ λ x →
            begin
              α[ a₀ ] x
            ≡⟨⟩
              (α[ a₀ ] ∘′ const x) tt
            ≡⟨⟩
              (α[ a₀ ] ∘′ on-nothing {a = a*} (const x) nothing) tt
            ≡⟨⟩
              lower (lmap x→x {b = maybe′ b* a₀} (on-nothing {a = a*} (const x)) (α .proj a₀)) tt
            ≡⟨ ≡.cong-app (≡.cong lower (exnat# (const x))) tt ⟩
              lower (rmap x→x {a = maybe′ a* ⊤} (on-nothing {a = b*} (const x)) (α .proj ⊤)) tt
            ≡⟨⟩
              (on-nothing {a = b*} (const x) nothing ∘′ α[ ⊤ ]) tt
            ≡⟨⟩
              (const x ∘′ α[ ⊤ ]) tt
            ≡⟨⟩
              x
            ∎
      )]
      where
        α[_] : (a₀ : Set) → a₀ → a₀
        α[ a₀ ] = lower (proj α a₀)
        open ≡.≡-Reasoning
