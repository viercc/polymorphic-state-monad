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

module Indexed.Profunctor.StrictlyPositiveFunctor .(ext : Extensionality 1ℓ 1ℓ) where

open import Indexed.Profunctor
open import Indexed.Profunctor.Functor
open import Indexed.Profunctor.Instances
open InstancesWithExt ext
open import Indexed.Profunctor.End ext

open Profunctor

-- Syntax of strictly positive functor
data SPos (I : Set) : Set₂ where
  idSP : SPos I
  constantSP : Profunctor I → SPos I
  sumSP : SPos I → SPos I → SPos I
  prodSP : SPos I → SPos I → SPos I
  kfunSP : Profunctor I → SPos I → SPos I

mapIndexSPos : ∀ {I J : Set} (f : I → J)
  → SPos I → SPos J
mapIndexSPos t idSP = idSP
mapIndexSPos t (constantSP A) = constantSP (mapIndex t A)
mapIndexSPos t (sumSP F₁ F₂) = sumSP (mapIndexSPos t F₁) (mapIndexSPos t F₂)
mapIndexSPos t (prodSP F₁ F₂) = prodSP (mapIndexSPos t F₁) (mapIndexSPos t F₂)
mapIndexSPos t (kfunSP A F) = kfunSP (mapIndex t A) (mapIndexSPos t F)

shiftSPos : ∀ {I : Set} → SPos I → SPos (Maybe I)
shiftSPos = mapIndexSPos just

-- Apply SPos to a type
eval : ∀ {I : Set} → SPos I
  → (a b : I → Set) → Set₁ → Set₁
eval idSP _ _ X = X
eval (constantSP A) a b _ = A [ a , b ]
eval (sumSP F₁ F₂) a b X = eval F₁ a b X ⊎ eval F₂ a b X
eval (prodSP F₁ F₂) a b X = eval F₁ a b X Prod.× eval F₂ a b X
eval (kfunSP A F) a b X = A [ b , a ] → eval F a b X

mapEval : ∀ {I} (F : SPos I)
  → {a a' b b' : I → Set} {X X' : Set₁}
  → (f : a' ~> a) (g : b ~> b') (h : X → X')
  → eval F a b X → eval F a' b' X'
mapEval idSP = λ f g h → h
mapEval (constantSP A) = λ f g h → dimap A f g
mapEval (sumSP F₁ F₂) = λ f g h → Sum.map (mapEval F₁ f g h) (mapEval F₂ f g h)
mapEval (prodSP F₁ F₂) = λ f g h → Prod.map (mapEval F₁ f g h) (mapEval F₂ f g h)
mapEval (kfunSP A F) = λ f g h A→FX → mapEval F f g h ∘′ A→FX ∘′ dimap A g f

mapEval-id : ∀ {I} (F : SPos I) 
  → Irrelevant (
      ∀ {a b : I → Set} {X : Set₁} (x : eval F a b X)
        → mapEval F idᵢ idᵢ id x ≡ x
    )
mapEval-id F = {!   !}

-- Apply SPos to a Profunctor
⟦_⟧ : ∀ {I : Set} → SPos I
  → Profunctor I → Profunctor I
⟦_⟧ {I} F P = record {
    Carrier = FP;
    dimap = λ f g → mapEval F f g (dimap P f g);
    dimap-id = {!   !};
    dimap-∘ = {!   !}
  }
  where
    FP : ∀ (a b : I → Set) → Set₁
    FP = λ a b → eval F a b (P [ a , b ])

instance
  SPosIsFunctor : ∀ {I} {F : SPos I}
    → IsFunctor I I ⟦ F ⟧
  SPosIsFunctor = {!   !}

-- The yoneda lemma
yoneda : ∀ {I} (F : SPos I) (A : Profunctor I)
  → EndP (fun (fun (k A) v0) (⟦ shiftSPos F ⟧ v0)) ⇔ ⟦ F ⟧ A
yoneda F A = {!   !}

-- * Initial algebra of a strictly positive functor

module _ {I : Set} where

  data Rec (F : SPos I) (a b : I → Set) : Set₁ where
    roll : eval F a b (Rec F a b) → Rec F a b
  
  private
    module _ {a a' b b' : I → Set}
      (f : a' ~> a) (g : b ~> b') where

      -- -- This definition fails to termination checking
      -- dimapRec : (F : SPos I) → Rec F a b → Rec F a' b'
      -- dimapRec F (roll x) = roll (mapEval F f g (dimapRec F) x)

      -- But for each concrete F, it seems to be able to write dimapRec

      dimapRecId : Rec idSP a b → Rec idSP a' b'
      dimapRecId (roll x) = roll (dimapRecId x)

      dimapRecEither : ∀ {A : Profunctor I}
        → (let F = sumSP (constantSP A) idSP)
        → Rec F a b → Rec F a' b'
      dimapRecEither {A} (roll (Sum.inj₁ x)) = roll (Sum.inj₁ (dimap A f g x))
      dimapRecEither {A} (roll (Sum.inj₂ x)) = roll (Sum.inj₂ (dimapRecEither x))

      dimapRecFun : ∀ {A : Profunctor I}
        → (let F = kfunSP A idSP)
        → Rec F a b → Rec F a' b'
      dimapRecFun {A} (roll p) = roll (λ a → dimapRecFun (p (dimap A g f a)))

      -- Solution proposed by ChatGPT:

      -- 1. Convert to Container, use W-type (or their clone with parameters (a b : I -> Set))
      -- 
      --    Possible obstacle:
      --    
      --    The dependency between "Shape Profunctor" and "Position Profunctor family"
      --    must satisfy some naturality condition, but I'm not sure how that will
      --    appear formally.
      -- 
      -- 2. Use sized type
      -- 
      --    https://agda.readthedocs.io/en/latest/language/sized-types.html

  RecP : SPos I → Profunctor I
  RecP F .Carrier = Rec F
  RecP F .dimap = _
  RecP F .dimap-∘ = _
  RecP F .dimap-id = _