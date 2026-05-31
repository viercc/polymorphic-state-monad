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

open import Data.Irrelevant

import Axiom.Extensionality.Propositional as Ext

open import Relation.Binary.PropositionalEquality as ≡
   using (_≡_)

open import ExtensionalityUtil

module MultiProfunctor (irr-ext : IrrExtensionality 1ℓ 1ℓ) where

.ext₁₁ : Ext.Extensionality 1ℓ 1ℓ
ext₁₁ = irrelevant irr-ext

.ext₀₀ : Ext.Extensionality 0ℓ 0ℓ
ext₀₀ = Ext.lower-extensionality 1ℓ 1ℓ ext₁₁

-- * Preliminary definitions

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

-- * Profunctor type

record Profunctor {I : Set} : Set₂ where
  field
    Carrier : (I → Set) → (I → Set) → Set₁
  
  private
    P = Carrier

  field
    dimap : ∀ {a a′ b b′ : I → Set} → (a′ ~> a) → (b ~> b′) → P a b → P a′ b′

    .dimap-id : ∀ {a b}
      → dimap {a = a} {b = b} idᵢ idᵢ ≡ id
    
    .dimap-∘ : ∀ {a a′ a″ b b′ b″}
      → (f₁ : a″ ~> a′) (g₁ : b′ ~> b″) (f₂ : a′ ~> a) (g₂ : b ~> b′)
      → dimap (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂) ≡ dimap f₁ g₁ ∘′ dimap f₂ g₂

  lmap : ∀ {a a′ b} → (a′ ~> a) → P a b → P a′ b
  lmap f = dimap f idᵢ

  rmap : ∀ {a b b′} → (b ~> b′) → P a b → P a b′
  rmap g = dimap idᵢ g

Carrier-syntax : ∀ {I} → Profunctor {I} → (I → Set) → (I → Set) → Set₁
Carrier-syntax = Profunctor.Carrier

syntax Carrier-syntax P a b = P [ a , b ]

-- * Instances

hom : ∀ {I} → Profunctor {I}
hom = record {
    Carrier = λ a b → Lift 1ℓ (∀ i → a i → b i);
    dimap = λ f g (lift p) → lift (g ∘ᵢ p ∘ᵢ f);
    dimap-id = ≡.refl;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

-- constant profunctor
constant : ∀ {I} → (c : Set) → Profunctor {I}
constant c = record {
    Carrier = λ _ _ → Lift 1ℓ c;
    dimap = λ _ _ p → p;
    dimap-id = ≡.refl;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

-- Remap index set by a function (F : I → J)
_⋆_ : {I J : Set} (F : I → J) (P : Profunctor {I}) → Profunctor {J}
_⋆_ {I} {J} F P = record {
    Carrier = λ a b → P [ a ∘ F , b ∘ F ];
    dimap = λ f g → dimap (f ∘ F) (g ∘ F);
    dimap-id = dimap-id;
    dimap-∘ = λ f₁ g₁ f₂ g₂ → dimap-∘ (f₁ ∘ F) (g₁ ∘ F) (f₂ ∘ F) (g₂ ∘ F)
  }
  where open Profunctor P

module _ where

  private
    map+ : ∀ {A B C D : Set₁} → (A → C) → (B → D)
      → A ⊎ B → C ⊎ D
    map+ f g = Sum.map f g

    map+-id : ∀ {A B} x → map+ (id {A = A}) (id {A = B}) x ≡ x
    map+-id (Sum.inj₁ x₁) = ≡.refl
    map+-id (Sum.inj₂ x₂) = ≡.refl

    map+-∘ : ∀ {A B C D E F}
      (h₁ : C → E) (j₁ : D → F) (h₂ : A → C) (j₂ : B → D)
      → ∀ x → map+ (h₁ ∘′ h₂) (j₁ ∘′ j₂) x ≡ map+ h₁ j₁ (map+ h₂ j₂ x)
    map+-∘ _ _ _ _ (Sum.inj₁ _) = ≡.refl
    map+-∘ _ _ _ _ (Sum.inj₂ _) = ≡.refl

  _+_ : ∀ {I} → Profunctor {I} → Profunctor {I} → Profunctor {I}
  _+_ {I} P Q =
    record {
      Carrier = λ a b → P [ a , b ] ⊎ Q [ a , b ];
      dimap = λ f g → map+ (dimap P f g) (dimap Q f g);
      dimap-id =
          begin
            map+ (dimap P idᵢ idᵢ) (dimap Q idᵢ idᵢ)
          ≡⟨ ≡.cong₂ map+ (dimap-id P) (dimap-id Q) ⟩
            map+ id id
          ≡⟨ ext₁₁ map+-id ⟩
            id
          ∎ ;
      dimap-∘ = λ f₁ g₁ f₂ g₂ →
        let eqP = dimap-∘ P f₁ g₁ f₂ g₂
            eqQ = dimap-∘ Q f₁ g₁ f₂ g₂
        in
          begin
            map+ (dimap P (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂)) (dimap Q (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂))
          ≡⟨ ≡.cong₂ map+ eqP eqQ ⟩
            map+ (dimap P f₁ g₁ ∘′ dimap P f₂ g₂) (dimap Q f₁ g₁ ∘′ dimap Q f₂ g₂)
          ≡⟨ ext₁₁ (map+-∘ _ _ _ _) ⟩
            map+ (dimap P f₁ g₁) (dimap Q f₁ g₁) ∘′ map+ (dimap P f₂ g₂) (dimap Q f₂ g₂)
          ∎
    }
    where
      open Profunctor
      open ≡.≡-Reasoning

module _ where
  private
    map× : ∀ {A B C D : Set₁} → (A → C) → (B → D)
      → A Prod.× B → C Prod.× D
    map× f g = Prod.map f g

  _×_ : ∀ {I} → Profunctor {I} → Profunctor {I} → Profunctor {I}
  _×_ {I} P Q =
    record {
      Carrier = λ a b → P [ a , b ] Prod.× Q [ a , b ];
      dimap = λ f g → map× (dimap P f g) (dimap Q f g);
      dimap-id = begin
          map× (dimap P idᵢ idᵢ) (dimap Q idᵢ idᵢ)
        ≡⟨ ≡.cong₂ map× (dimap-id P) (dimap-id Q) ⟩
          map× id id
        ≡⟨ ext₁₁ (λ _ → ≡.refl) ⟩
          id
        ∎ ;
      dimap-∘ = λ f₁ g₁ f₂ g₂ →
        let eqP = dimap-∘ P f₁ g₁ f₂ g₂
            eqQ = dimap-∘ Q f₁ g₁ f₂ g₂
        in
          begin
            map× (dimap P (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂)) (dimap Q (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂))
          ≡⟨ ≡.cong₂ map× eqP eqQ ⟩
            map× (dimap P f₁ g₁ ∘′ dimap P f₂ g₂) (dimap Q f₁ g₁ ∘′ dimap Q f₂ g₂)
          ≡⟨ ext₁₁ (λ _ → ≡.refl) ⟩
            map× (dimap P f₁ g₁) (dimap Q f₁ g₁) ∘′ map× (dimap P f₂ g₂) (dimap Q f₂ g₂)
          ∎
    }
    where
      open Profunctor
      open ≡.≡-Reasoning

module _ where
  private
    dimap-fun : ∀ {A B C D : Set₁} → (B → A) → (C → D) → (A → C) → (B → D)
    dimap-fun pre post f = post ∘′ f ∘′ pre

  fun : ∀{I} → Profunctor {I} → Profunctor {I} → Profunctor {I}
  fun {I} P Q = record {
      Carrier = λ a b → P [ b , a ] → Q [ a , b ];
      dimap = λ f g → dimap-fun (dimap P g f) (dimap Q f g);
      dimap-id = begin
          dimap-fun (dimap P idᵢ idᵢ) (dimap Q idᵢ idᵢ)
        ≡⟨ ≡.cong₂ dimap-fun (dimap-id P) (dimap-id Q) ⟩
          dimap-fun id id
        ≡⟨ ext₁₁ (λ _ → ≡.refl) ⟩
          id
        ∎;
      dimap-∘ = λ f₁ g₁ f₂ g₂ →
        let eqP = dimap-∘ P g₂ f₂ g₁ f₁
            eqQ = dimap-∘ Q f₁ g₁ f₂ g₂
        in
          begin
            dimap-fun (dimap P (g₁ ∘ᵢ g₂) (f₂ ∘ᵢ f₁)) (dimap Q (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂))
          ≡⟨ ≡.cong₂ dimap-fun eqP eqQ ⟩
            dimap-fun (dimap P g₂ f₂ ∘′ dimap P g₁ f₁) (dimap Q f₁ g₁ ∘′ dimap Q f₂ g₂)
          ≡⟨ ext₁₁ (λ _ → ≡.refl) ⟩
            dimap-fun (dimap P g₁ f₁) (dimap Q f₁ g₁) ∘′ dimap-fun (dimap P g₂ f₂) (dimap Q f₂ g₂)
          ∎
    }
    where
      open Profunctor
      open ≡.≡-Reasoning

var : ∀ {I} → Profunctor {Maybe I}
var {I} = record {
    Carrier = λ _ b → Lift 1ℓ (b nothing);
    dimap = λ _ g p → lift (g nothing (lower p)) ;
    dimap-id = ≡.refl ;
    dimap-∘ = λ _ _ _ _ → ≡.refl
  }

k : ∀ {I} → Profunctor {I} → Profunctor {Maybe I}
k = just ⋆_

-- * Conversion between simple (single-variable) Profunctor

{-
module _ where
  open import Profunctor as P₁
    using ()
    renaming (Profunctor to Profunctor₁)
  
  point : Profunctor₁ 1ℓ → Profunctor {⊤}
  point P = record {
      Carrier = λ a b → PP.Carrier (a tt) (b tt);
      dimap = λ f g → PP.dimap (f tt) (g tt);
      dimap-id = dimap-id;
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
-}

phantom : {P : Profunctor {⊥}}
  → ∀ {a b c d} → P [ a , b ] → P [ c , d ]
phantom {P = P} = Profunctor.dimap P (λ ()) (λ ())

-- * Morphism and isomorphism

record NaturalTransformation {I : Set} (P Q : Profunctor {I}) : Set₁ where
  open Profunctor P renaming (dimap to dimapP)
  open Profunctor Q renaming (dimap to dimapQ)

  field
    φ : ∀ {a b : I → Set}
      → P [ a , b ] → Q [ a , b ]
  
  Naturality : Set₁
  Naturality = ∀ {a a′ b b′ : I → Set}
      → (f : a′ ~> a) (g : b ~> b′) (x : P [ a , b ])
      → φ (dimapP f g x) ≡ dimapQ f g (φ x)
  
  field
    .naturality : Naturality

open NaturalTransformation

infix 7 NaturalTransformation
syntax NaturalTransformation a b = a ⇒ b

idNat : {I : Set} {P : Profunctor {I}} → P ⇒ P
idNat = record {
    φ = id;
    naturality = λ _ _ _ → ≡.refl
  }

_∘Nat_ : {I : Set} {P Q R : Profunctor {I}} → Q ⇒ R → P ⇒ Q → P ⇒ R
_∘Nat_ qr pq = record {
    φ = φ qr ∘ φ pq;
    naturality = λ f g x →
      ≡.trans
        (≡.cong (φ qr) (naturality pq f g x))
        (naturality qr f g (φ pq x))
  } 

record NaturalIso {I : Set} (P Q : Profunctor {I}) : Set₁ where
  field
    to : P ⇒ Q
    from : Q ⇒ P
    .to-from : ∀ {a b} → φ to ∘ φ from ≡ id {_} {Q [ a , b ] }
    .from-to : ∀ {a b} → φ from ∘ φ to ≡ id {_} {P [ a , b ] }

syntax NaturalIso P Q = P ⇔ Q

module _ {I : Set} (P : Profunctor {Maybe I}) where
  open Profunctor P using (lmap; rmap)

  record End (a b : I → Set) : Set₁ where
    
    field
      proj : ∀ (x : Set) → P [ maybe′ a x , maybe′ b x ]
    
    Extranaturality : Set₁
    Extranaturality = ∀ {x⁻ x⁺} → (h : x⁻ → x⁺)
        → lmap (last h) (proj x⁺) ≡ rmap (last h) (proj x⁻)
    
    field
      .extranaturality : Extranaturality

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

    idEnd' : End' hom
    idEnd' = record {
        proj = λ a → lift (idᵢ {a = maybe′ ⊥-elim a});
        extranaturality = λ _ → ≡.refl
      }
    
    private
      pick-nothing : ∀ {I} {a b : Maybe I → Set}
        → hom [ a , b ] → a nothing → b nothing
      pick-nothing p = lower p nothing

      .pick-nothing-injective :
          ∀ {a b : Maybe ⊥ → Set}
        → {p q : hom [ a , b ]}
        → pick-nothing p ≡ pick-nothing q
        → p ≡ q
      pick-nothing-injective {p = p} {q = q} hyp = ≡.cong lift $ ext₀₀ $ λ {
          (just bot) → ⊥-elim bot;
          nothing → hyp
        }

      .End-hom-contr : (α : End' hom) → α ≡ idEnd'
      End-hom-contr α = congEnd $
        ext₁₁ λ a → pick-nothing-injective {a = maybe ⊥-elim a} {b = maybe ⊥-elim a} $ ext₀₀ λ x →
          begin
            lower (proj α a) nothing x
          ≡⟨⟩
            (lower (proj α a) nothing ∘ const x) tt
          ≡⟨⟩
            ((lower (proj α a) ∘ᵢ last (const x)) nothing) tt
          ≡⟨⟩
            lower (lmap (last (const x)) (proj α a)) nothing tt 
          ≡⟨ ≡.cong (λ p → lower p nothing tt) (extranaturality α (const x)) ⟩
            lower (rmap (last (const x)) (proj α ⊤)) nothing tt 
          ≡⟨⟩
            x
          ∎
        where open ≡.≡-Reasoning
    
    -- In Haskell, `id` is the only inhabitant of type `∀ a. a → a`.
    -- The following is the corresponding statement in terms of End.
    uniqueness : (α : End' hom) → Irrelevant (α ≡ idEnd')
    uniqueness α = [ End-hom-contr α ]
    