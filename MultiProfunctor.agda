{-# OPTIONS --without-K --irrelevant-projections #-}

open import Level
open import Function
  using (
    _∘_; _∘′_; _$_; id; const; constᵣ;
    case_of_
  )

import Data.Product as Prod
open import Data.Unit
open import Data.Empty

open import Data.Maybe using (Maybe; nothing; just; maybe; maybe′)

open import Data.Irrelevant

import Axiom.Extensionality.Propositional as Ext

open import Relation.Binary.PropositionalEquality as ≡
   using (_≡_)

open import ExtensionalityUtil

module MultiProfunctor where

_~>_ : ∀ {I : Set} → (I → Set) → (I → Set) → Set
_~>_ {I} a b = ∀ (i : I) → a i → b i

infix 7 _~>_

idᵢ : ∀ {I : Set} {a : I → Set} → a ~> a
idᵢ _ = id

infixr 8 _∘ᵢ_

_∘ᵢ_ : ∀ {I : Set} {a b c : I → Set} →
  (f : b ~> c) → (g : a ~> b) → a ~> c 
_∘ᵢ_ f g i = f i ∘′ g i

last : ∀ {I : Set} {a : I → Set} {x x′ : Set}
  → (x → x′) → maybe′ a x ~> maybe′ a x′
last h = maybe (λ _ → id) h

record Profunctor {I : Set} : Set₂ where
  field
    Carrier : (I → Set) → (I → Set) → Set₁
  
  private
    P = Carrier

  field
    dimap : ∀ {a a′ b b′ : I → Set} → (a′ ~> a) → (b ~> b′) → P a b → P a′ b′

    dimap-id : ∀ {a b} →
      dimap {a = a} {b = b} idᵢ idᵢ ≡ id
    
    dimap-∘ : ∀ {a a′ a″ b b′ b″}
      →  (f₁ : a″ ~> a′) (g₁ : b′ ~> b″) (f₂ : a′ ~> a) (g₂ : b ~> b′)
      → dimap (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂) ≡ dimap f₁ g₁ ∘ dimap f₂ g₂

  lmap : ∀ {a a′ b} → (a′ ~> a) → P a b → P a′ b
  lmap f = dimap f idᵢ

  rmap : ∀ {a b b′} → (b ~> b′) → P a b → P a b′
  rmap g = dimap idᵢ g

Carrier-syntax : ∀ {I} → Profunctor {I} → (I → Set) → (I → Set) → Set₁
Carrier-syntax = Profunctor.Carrier

syntax Carrier-syntax P a b = P [ a , b ]

-- Instances

hom : ∀ {I} → Profunctor {I}
hom = record {
    Carrier = λ a b → Lift 1ℓ (∀ i → a i → b i);
    dimap = λ f g (lift p) → lift (g ∘ᵢ p ∘ᵢ f);
    dimap-id = ≡.refl;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

constant : ∀ {I} → (c : Set) → Profunctor {I}
constant c = record {
    Carrier = λ _ _ → Lift 1ℓ c;
    dimap = λ _ _ p → p;
    dimap-id = ≡.refl;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

var : ∀ {I} → Profunctor {Maybe I}
var {I} = record {
    Carrier = λ _ b → Lift 1ℓ (b nothing);
    dimap = λ _ g p → lift (g nothing (lower p)) ;
    dimap-id = ≡.refl ;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

k : ∀ {I} → Profunctor {I} → Profunctor {Maybe I}
k {I} P = record {
    Carrier = λ a b → P [ a ∘ just , b ∘ just ];
    dimap = λ f g p → dimap (f ∘ just) (g ∘ just) p;
    dimap-id = dimap-id;
    dimap-∘ = λ f₁ g₁ f₂ g₂ → dimap-∘ (f₁ ∘ just) (g₁ ∘ just) (f₂ ∘ just) (g₂ ∘ just)
  }
  where open Profunctor P

_×_ : ∀ {I} → Profunctor {I} → Profunctor {I} → Profunctor {I}
_×_ {I} P Q =
  record {
    Carrier = λ a b → P [ a , b ] Prod.× Q [ a , b ];
    dimap = λ f g → map× (dimap P f g) (dimap Q f g);
    dimap-id = ≡.cong₂ map× (dimap-id P) (dimap-id Q);
    dimap-∘ = λ f₁ g₁ f₂ g₂ → 
      ≡.cong₂ map× (dimap-∘ P f₁ g₁ f₂ g₂) (dimap-∘ Q f₁ g₁ f₂ g₂)
  }
  where
    open Profunctor

    map× : ∀ {A B C D : Set₁} → (A → C) → (B → D)
      → A Prod.× B → C Prod.× D
    map× f g = Prod.map f g

fun : ∀{I} → Profunctor {I} → Profunctor {I} → Profunctor {I}
fun {I} P Q = record {
    Carrier = λ a b → P [ b , a ] → Q [ a , b ];
    dimap = λ f g → dimap-fun (dimap P g f) (dimap Q f g);
    dimap-id = ≡.cong₂ dimap-fun (dimap-id P) (dimap-id Q);
    dimap-∘ = λ f₁ g₁ f₂ g₂ →
      ≡.cong₂ dimap-fun (dimap-∘ P g₂ f₂ g₁ f₁) (dimap-∘ Q f₁ g₁ f₂ g₂)
  }
  where
    open Profunctor

    dimap-fun : ∀ {A B C D : Set₁} → (B → A) → (C → D) → (A → C) → (B → D)
    dimap-fun pre post f = post ∘′ f ∘′ pre      

phantom : {P : Profunctor {⊥}}
  → ∀ {a b c d} → P [ a , b ] → P [ c , d ]
phantom {P = P} = Profunctor.dimap P (λ ()) (λ ())

module single-variable where
  open import Profunctor as P₁
    using ()
    renaming (Profunctor to Profunctor₁)
  
  point : Profunctor₁ 1ℓ → Profunctor {⊤}
  point P = record {
      Carrier = λ a b → PP.Carrier (a tt) (b tt);
      dimap = λ f g → PP.dimap (f tt) (g tt);
      dimap-id = PP.dimap-id;
      dimap-∘ = λ f₁ g₁ f₂ g₂ → PP.dimap-∘ (f₁ tt) (g₁ tt) (f₂ tt) (g₂ tt)
    }
    where
      module PP = Profunctor₁ P

  delta : ∀ {I} → Profunctor {I} → Profunctor₁ 1ℓ
  delta P = record {
      Carrier = λ a b → P [ const a , const b ];
      dimap = λ f g → PP.dimap (const f) (const g);
      dimap-id = PP.dimap-id;
      dimap-∘ = λ f₁ g₁ f₂ g₂ → PP.dimap-∘ (const f₁) (const g₁) (const f₂) (const g₂)
    }
    where
      module PP = Profunctor P


module _ {I : Set} (P : Profunctor {Maybe I}) where
  open Profunctor P using (lmap; rmap)

  record End (a b : I → Set) : Set₁ where
    
    field
      proj : ∀ (x : Set) → P [ maybe′ a x , maybe′ b x ]
      
    Extranaturality : Set₁
    Extranaturality = ∀ {x⁻ x⁺} → (h : x⁻ → x⁺)
        → lmap (last h) (proj x⁺) ≡ rmap (last h) (proj x⁻)
    
    field
      extranaturality : Irrelevant Extranaturality

open End

congEnd : ∀ {I : Set} {P : Profunctor {Maybe I}} {a b : I → Set} {p p′ : End P a b}
  → proj p ≡ proj p′
  → p ≡ p′
congEnd ≡.refl = ≡.refl

module example where

  module profunctor-construction where
    _ : Profunctor.Carrier (fun (var {⊥} × fun var var) var)
          ≡
        (λ a b →
          let
            x = Lift 1ℓ (a nothing)
            y = Lift 1ℓ (b nothing)
          in x Prod.× (y → x) → y
        )
    _ = ≡.refl
  
  module parametricity-id where
    open Profunctor (hom {Maybe ⊥})

    -- End' = single-variable End
    End' : Profunctor {Maybe ⊥} → Set₁
    End' P = End P ⊥-elim ⊥-elim

    idEnd : End' hom
    idEnd = record {
        proj = λ a → lift (idᵢ {a = maybe′ ⊥-elim a});
        extranaturality = [ (λ h → ≡.refl) ]
      }
    
    -- In Haskell, `id` is the only inhabitant of type `∀ a. a → a`.
    -- The following is the corresponding statement in terms of End.
    Uniqueness : Set₁
    Uniqueness = (α : End' hom) → Irrelevant (α ≡ idEnd)
    
    pick-nothing : ∀ {I} {a b : Maybe I → Set}
      → hom [ a , b ] → a nothing → b nothing
    pick-nothing p = lower p nothing

    pick-nothing-injective :
        Ext.Extensionality 0ℓ 0ℓ
      → ∀ {a b : Maybe ⊥ → Set}
      → {p q : hom [ a , b ]}
      → pick-nothing p ≡ pick-nothing q
      → p ≡ q
    pick-nothing-injective ext {p = p} {q = q} hyp = ≡.cong lift $ ext $ λ {
        (just bot) → ⊥-elim bot;
        nothing → hyp
      }

    End-hom-singleton : IrrExtensionality 1ℓ 1ℓ → Uniqueness
    End-hom-singleton irr-ext α = map congEnd $
      irr-ext >>= λ ext →
      extranaturality α >>= λ exnat → 
        [(
          let open Ext1 (lower-extensionality₁ 1ℓ 1ℓ ext)
          in
            ext₁₁ λ a → pick-nothing-injective ext₀₀ {a = maybe ⊥-elim a} {b = maybe ⊥-elim a} $ ext₀₀ λ x →
              begin
                lower (proj α a) nothing x
              ≡⟨⟩
                (lower (proj α a) nothing ∘ const x) tt
              ≡⟨⟩
                ((lower (proj α a) ∘ᵢ last (const x)) nothing) tt
              ≡⟨⟩
                lower (lmap (last (const x)) (proj α a)) nothing tt 
              ≡⟨ ≡.cong (λ p → lower p nothing tt) (exnat (const x)) ⟩
                lower (rmap (last (const x)) (proj α ⊤)) nothing tt 
              ≡⟨⟩
                x
              ∎
        )]
      where open ≡.≡-Reasoning