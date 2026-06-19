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
module Indexed.Profunctor where

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

-- * Profunctor type

record Profunctor (I : Set) : Set₂ where
  constructor mkProfunctor

  field
    Carrier : (I → Set) → (I → Set) → Set₁
  
  private
    P = Carrier

  field
    dimap : ∀ {a a′ b b′ : I → Set} → (a′ ~> a) → (b ~> b′) → P a b → P a′ b′

    dimap-id : Irrelevant (∀ {a b} (x : P a b) → dimap idᵢ idᵢ x ≡ x)
    
    dimap-∘ : Irrelevant (
        ∀ {a a′ a″ b b′ b″}
        → (f₁ : a″ ~> a′) (g₁ : b′ ~> b″) (f₂ : a′ ~> a) (g₂ : b ~> b′)
        → dimap (f₂ ∘ᵢ f₁) (g₁ ∘ᵢ g₂) ≗ dimap f₁ g₁ ∘′ dimap f₂ g₂
      )

  lmap : ∀ {a a′ b} → (a′ ~> a) → P a b → P a′ b
  lmap f = dimap f idᵢ

  rmap : ∀ {a b b′} → (b ~> b′) → P a b → P a b′
  rmap g = dimap idᵢ g

infix 20 Carrier-syntax

Carrier-syntax : ∀ {I} → Profunctor I → (I → Set) → (I → Set) → Set₁
Carrier-syntax = Profunctor.Carrier

syntax Carrier-syntax P a b = P [ a , b ]

phantom : {P : Profunctor ⊥}
  → ∀ {a b c d} → P [ a , b ] → P [ c , d ]
phantom {P = P} = Profunctor.dimap P (λ ()) (λ ())

-- Remap index set by a function (F : I → J)
mapIndex : {I J : Set} (F : I → J) (P : Profunctor I) → Profunctor J
mapIndex {I} {J} F P = record {
    Carrier = λ a b → P [ a ∘ F , b ∘ F ];
    dimap = λ f g → dimap (f ∘ F) (g ∘ F);
    dimap-id = dimap-id >>= λ dimap-id# → irr[ dimap-id# ];
    dimap-∘ = dimap-∘ >>= λ dimap-∘# → irr[(
        λ f₁ g₁ f₂ g₂ → dimap-∘# (f₁ ∘ F) (g₁ ∘ F) (f₂ ∘ F) (g₂ ∘ F)
      )]
  }
  where open Profunctor P

-- * Morphism and isomorphism

record NaturalTransformation {I : Set} (P Q : Profunctor I) : Set₁ where
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
    naturality : Irrelevant Naturality

open NaturalTransformation public

infix 1 NaturalTransformation
syntax NaturalTransformation a b = a ⇒ b

idNat : {I : Set} {P : Profunctor I} → P ⇒ P
idNat = record {
    φ = id;
    naturality = irr[( λ _ _ _ → ≡.refl )]
  }

_∘Nat_ : {I : Set} {P Q R : Profunctor I} → Q ⇒ R → P ⇒ Q → P ⇒ R
_∘Nat_ qr pq .φ = φ qr ∘ φ pq
_∘Nat_ qr pq .naturality =
  naturality pq >>= λ natPQ →
  naturality qr >>= λ natQR → irr[(λ f g x →
    ≡.trans
      (≡.cong (φ qr) (natPQ f g x))
      (natQR f g (φ pq x))
  )]

-- Pointwise equality between natural transformations
infix 1 _≈_
_≈_ : {I : Set} {P Q : Profunctor I} → (P ⇒ Q) → (P ⇒ Q) → Set₁
_≈_ {P = P} α β = ∀ {a b} (p : P [ a , b ]) → α .φ p ≡ β .φ p

record NaturalIso {I : Set} (P Q : Profunctor I) : Set₁ where
  field
    to : P ⇒ Q
    from : Q ⇒ P
    to-from : Irrelevant ((to ∘Nat from) ≈ idNat)
    from-to : Irrelevant ((from ∘Nat to) ≈ idNat)

open NaturalIso

infix 1 NaturalIso
syntax NaturalIso P Q = P ⇔ Q

idIso : ∀ {I} {P : Profunctor I} → P ⇔ P
idIso = record {
    to = idNat; from = idNat;
    to-from = irr[ (λ _ → ≡.refl) ];
    from-to = irr[ (λ _ → ≡.refl) ]
  }

symIso : ∀ {I} {P Q : Profunctor I}
  → P ⇔ Q → Q ⇔ P
symIso P⇔Q = record {
    to = P⇔Q .from;
    from = P⇔Q .to;
    to-from = P⇔Q .from-to;
    from-to = P⇔Q .to-from
  }

transIso : ∀ {I} {P Q R : Profunctor I}
  → P ⇔ Q → Q ⇔ R → P ⇔ R
transIso {_} {P} {Q} {R} P⇔Q Q⇔R = record{
    to = P⇒R; from = R⇒P;
    to-from = to-from-PR;
    from-to = from-to-PR
  } 
  where
    P⇒R : P ⇒ R
    P⇒R = Q⇔R .to ∘Nat P⇔Q .to

    R⇒P : R ⇒ P
    R⇒P = P⇔Q .from ∘Nat Q⇔R .from

    open ≡.≡-Reasoning

    to-from-PR : Irrelevant (∀ {a b} (r : R [ a , b ]) → P⇒R .φ (R⇒P .φ r) ≡ r)
    to-from-PR =
      P⇔Q .to-from >>= λ to-from-PQ# → 
      Q⇔R .to-from >>= λ to-from-QR# →
      irr[( λ {a b} r →
        begin
          P⇒R .φ (R⇒P .φ r)
        ≡⟨⟩
          Q⇔R .to .φ (P⇔Q .to .φ (P⇔Q .from .φ (Q⇔R .from .φ r)))
        ≡⟨ ≡.cong (Q⇔R .to .φ) (to-from-PQ# (Q⇔R .from .φ r)) ⟩
          Q⇔R .to .φ (Q⇔R .from .φ r)
        ≡⟨ to-from-QR# r ⟩
          r
        ∎
       )]

    from-to-PR : Irrelevant (∀ {a b} (p : P [ a , b ]) → R⇒P .φ (P⇒R .φ p) ≡ p)
    from-to-PR = 
      P⇔Q .from-to >>= λ from-to-PQ# → 
      Q⇔R .from-to >>= λ from-to-QR# →
      irr[( λ {a b} p →
        begin
          R⇒P .φ (P⇒R .φ p)
        ≡⟨⟩
          P⇔Q .from .φ (Q⇔R .from .φ (Q⇔R .to .φ (P⇔Q .to .φ p)))
        ≡⟨ ≡.cong (P⇔Q .from .φ) (from-to-QR# (P⇔Q .to .φ p)) ⟩
          P⇔Q .from .φ (P⇔Q .to .φ p)
        ≡⟨ from-to-PQ# p ⟩
          p
        ∎
       )]

-- Given a "≡ on NaturalTransformation" isomorphism proof,
-- construct a NaturalIso.
-- 
-- It is a stronger claim than pointwise equalities ≈ required for
-- NaturalIso.

RightInv LeftInv : ∀ {I : Set} {P Q : Profunctor I} 
  → P ⇒ Q → Q ⇒ P → Set _
RightInv f g = f ∘Nat g ≡ idNat
LeftInv f g = g ∘Nat f ≡ idNat

naturalIsoBy≡ : ∀ {I : Set} {P Q : Profunctor I}
  (f : P ⇒ Q) (g : Q ⇒ P)
  → .(RightInv f g)
  → .(LeftInv f g)
  → P ⇔ Q
naturalIsoBy≡ f g fg≡id gf≡id = 
  record {
    to = f;
    from = g;
    to-from = irr[(
      λ q → ≡.cong (λ nat → nat .φ q) fg≡id
    )];
    from-to = irr[(
      λ p → ≡.cong (λ nat → nat .φ p) gf≡id
    )]
  }

-- * Simple instances

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

-- * Initial and terminal profunctors

empty unit : ∀ {I} → Profunctor I
empty = constant ⊥
unit = constant ⊤

elim-empty : ∀ {I} {P : Profunctor I}
  → empty ⇒ P
elim-empty .φ = λ ()
elim-empty .naturality = irr[( λ _ _ () )]

elim-empty-univ : ∀ {I} {P : Profunctor I}
  → ∀ (elim' : empty ⇒ P) → elim' ≈ elim-empty
elim-empty-univ _ = λ ()

bang-unit : ∀ {I} {P : Profunctor I}
  → P ⇒ unit
bang-unit .φ = λ _ → lift tt
bang-unit .naturality = irr[( λ _ _ _ → ≡.refl )]

bang-unit-univ : ∀ {I} {P : Profunctor I}
  → ∀ (bang' : P ⇒ unit) → bang' ≈ bang-unit
bang-unit-univ _ = λ _ → ≡.refl

-- * Variables

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


-- Theorems depending on function extensionality.
-- The supplied extensionality is marked irrelevant,
-- so that its use is restricted to irrelevant contexts.
module WithExt .(ext : Extensionality 1ℓ 1ℓ) where
  module _ {I : Set} {P Q : Profunctor I} where
    private
      congNat : ∀ {nat1 nat2 : P ⇒ Q}
        → (λ {a b} → nat1 .φ {a} {b}) ≡ nat2 .φ
        → nat1 ≡ nat2
      congNat ≡.refl = ≡.refl

    extNat : ∀ {nat1 nat2 : P ⇒ Q}
      → .(nat1 ≈ nat2)
      → Irrelevant (nat1 ≡ nat2)
    extNat {nat1 = nat1} {nat2 = nat2} eqφ =
        let .iext : ExtensionalityImplicit 1ℓ 1ℓ
            iext = implicit-extensionality ext
        in irr[ congNat (iext (iext (ext eqφ))) ]

  module _ {I : Set} {P Q : Profunctor I} where
    private
      congIso : ∀ {iso1 iso2 : P ⇔ Q}
        → iso1 .to ≡ iso2 .to
        → iso1 .from ≡ iso2 .from
        → iso1 ≡ iso2
      congIso ≡.refl ≡.refl = ≡.refl
    
    extIso : ∀ {iso1 iso2 : P ⇔ Q}
      → .(iso1 .to ≈ iso2 .to)
      → Irrelevant (iso1 ≡ iso2)
    extIso {iso1 = iso1} {iso2 = iso2}
        eqTo = irr[ congIso ] <*> extNat eqTo <*> (eqFrom >>= extNat)
      where
        to1 = iso1 .to .φ
        from1 = iso1 .from .φ
        to2 = iso2 .to .φ
        from2 = iso2 .from .φ

        eqFrom : Irrelevant (iso1 .from ≈ iso2 .from)
        eqFrom =
          iso1 .to-from >>= λ to1-from1-id →
          iso2 .from-to >>= λ from2-to2-id →
            irr[( λ q → begin
                from1 q
              ≡⟨ from2-to2-id (from1 q) ⟨
                from2 (to2 (from1 q))
              ≡⟨ ≡.cong from2 (eqTo (from1 q)) ⟨
                from2 (to1 (from1 q))
              ≡⟨ ≡.cong from2 (to1-from1-id q) ⟩
                from2 q
              ∎
            )]
          where
            open ≡.≡-Reasoning
    
    -- Converse of naturalIsoBy≡.
    -- Recovers "≡ on NaturalTransformation"-style isomorphism proofs.

    iso-rightInv : ∀ (iso : P ⇔ Q)
      → Irrelevant (RightInv (iso .to) (iso .from))
    iso-rightInv iso = iso .to-from >>= extNat
    
    iso-leftInv : ∀ (iso : P ⇔ Q)
      → Irrelevant (LeftInv (iso .to) (iso .from))
    iso-leftInv iso = iso .from-to >>= extNat
