{-# OPTIONS --without-K --safe #-}

{-

Definition of the State functor, the "usual" State monad on it,
encoding of monads on State with ∀-ed state type.

(work in progress -- the isomorphism-ness of the encoding
is not complete)

-}

open import Function
  using (
    _∘_; id; const; constᵣ;
    case_of_
  )
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
import Data.Product as Product
open import Data.Product.Properties as ProductProp

open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq

module Definitions where

-- Type part of the State monad
State : Set → Set → Set
State s a = s → (s × a)

-- fmap is unique by the Functor law
fmap : { s : Set } { a : Set } { b : Set } → (a → b) → State s a → State s b
fmap f ma s = Product.map₂ f (ma s)

-- pure is unique just by the parametricity
pure : { s : Set } { a : Set } → a → State s a
pure a s = s , a

-- Our beloved join defining the usual State monad
usualJoin : { s : Set } { a : Set } → State s (State s a) -> State s a
usualJoin mma s0 = case mma s0 of λ {
    (s1 , ma) → ma s1
  }

------------------------

-- Type of natural transformations
-- from (State s)^n to (State s), s universally qunatified.
-- 
-- n = 1,2,3 respectively.
M~>M : Set₁
M~>M = ∀ {s a : Set} → State s a → State s a

M²~>M : Set₁
M²~>M = ∀ {s a : Set} → State s (State s a) → State s a

M³~>M : Set₁
M³~>M = ∀ {s a : Set} → State s (State s (State s a)) → State s a

-- The type M~>M is isomorphic to (ℕ × ℕ). 
-- (Can't this proven inside Agda?)
{-
  ∀{s a} → State s a → State s a
    =
  ∀{s a} → (s → s × a) → (s → s × a)
    ≅
  ∀{s a} → (s → s) × (s → a) → (s → s × a)
    ≅
  ∀{s a} → (s → s) → (s → a) → s → s × a
    ≅
  ∀{s a} → (s → s) → s → (s → a) → s × a
    ≅
  ∀{s} → (s → s) → s → (∀{a} → (s → a) → s × a)
    ≅⟨Yoneda lemma⟩
  ∀{s} →  (s → s) → s → s × s
    ≅
  ∀{s} → ((s → s) → s → s) × ((s → s) → s → s)
    ≅
  (∀{s} → (s → s) → (s → s)) × (∀{s} → (s → s) → (s → s))
    ≅⟨ Boehm-Berarducci encoding of ℕ ⟩
  ℕ × ℕ
-}

reifyNat¹ : M~>M → (ℕ × ℕ)
reifyNat¹ nat = nat (λ n → (suc n , n)) zero

foldℕ : {a : Set} → (a → a) → a → ℕ → a
foldℕ {a} f x = go
  where
    go : ℕ → a
    go zero = x
    go (suc n) = f (go n)

runNat¹ : (ℕ × ℕ) → M~>M
runNat¹ (n₁ , n₂) {s = s} {a = a} ma s0 =
  let f : s → s
      f = proj₁ ∘ ma
  in foldℕ f s0 n₁ , proj₂ (ma (foldℕ f s0 n₂))

module iso¹-correct where
  refoldℕ : ∀ (n : ℕ) → foldℕ suc zero n ≡ n
  refoldℕ zero = refl
  refoldℕ (suc n) = cong suc (refoldℕ n)

  reify-run : ∀ (def : ℕ × ℕ) → reifyNat¹ (runNat¹ def) ≡ def
  reify-run (m , n) = ProductProp.×-≡,≡→≡ (refoldℕ m , refoldℕ n)

  {- Can't be proved for Agda because M²~>M lacks parametricity

  run-reify : ∀ (nat : M~>M) {s a} (ma : State s a) (s₀ : s)
    → runNat¹ (reifyNat¹ nat) ma s₀ ≡ nat ma s₀
  run-reify nat ma s₀ = _

  -}

-- Similarly, M²~>M ≅ (T × T × T), with T below.

data T : Set where
  F : T -> T
  G : T -> T -> T
  X : T

reifyNat² : M²~>M → T × T × T
reifyNat² nat = nat tt X
  where
    tt : State T (State T (T × T))
    tt t1 = F t1 , λ t2 → (G t1 t2 , (t1 , t2))

foldT : ∀ {a : Set} → (a → a) → (a → a → a) → a → T → a
foldT f g x X     = x
foldT f g x (F t) = f (foldT f g x t)
foldT f g x (G t1 t2) = g (foldT f g x t1) (foldT f g x t2)

runNat² : (T × T × T) → M²~>M
runNat² (t , l , r) {s = s} {a = a} mma s₀ =
    foldT f g s₀ t , ret (foldT f g s₀ l) (foldT f g s₀ r)
  where
    f : s → s
    f s1 = proj₁ (mma s1)

    g : s → s → s
    g s1 s2 = proj₁ (proj₂ (mma s1) s2)

    ret : s → s → a
    ret s1 s2 = proj₂ (proj₂ (mma s1) s2)

module iso²-correct where
  refoldT : ∀ (t : T) → foldT F G X t ≡ t
  refoldT X = refl
  refoldT (F t) = cong F (refoldT t)
  refoldT (G t₁ t₂) = cong₂ G (refoldT t₁) (refoldT t₂)

  prod3≡ : ∀ {A B C : Set} {p₁@(x₁ , y₁ , z₁) p₂@(x₂ , y₂ , z₂) : A × B × C}
    → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → p₁ ≡ p₂
  prod3≡ refl refl refl = refl

  reify-run : ∀ (def : T × T × T) → reifyNat² (runNat² def) ≡ def
  reify-run (t , l , r) = prod3≡ (refoldT t) (refoldT l) (refoldT r)

  {- Can't be proved for Agda because M²~>M lacks parametricity

  run-reify : ∀ (nat : M²~>M) {s a} (mma : State s (State s a)) (s₀ : s)
    → runNat² (reifyNat² nat) mma s₀ ≡ nat mma s₀
  run-reify nat mma s₀ = _

  -}

---------------------------

-- M³~>M ≅ (S × (S × S × S)), with S below.

data S : Set where
  Leaf : S
  A : S -> S
  B : S -> S -> S
  C : S -> S -> S -> S

reifyNat³ : M³~>M → (S × (S × S × S))
reifyNat³ nat = nat sss Leaf
  where
    sss : State S (State S (State S (S × S × S)))
    sss s1 = A s1 , λ { s2 → B s1 s2 , λ { s3 → C s1 s2 s3 , (s1 , s2 , s3) } }

foldS : ∀ {α : Set} → (α → α) → (α → α → α) → (α → α → α → α) → α → S → α
foldS a b c leaf Leaf = leaf
foldS a b c leaf (A s) = a (foldS a b c leaf s)
foldS a b c leaf (B s s₁) = b (foldS a b c leaf s) (foldS a b c leaf s₁)
foldS a b c leaf (C s s₁ s₂) = c (foldS a b c leaf s) (foldS a b c leaf s₁) (foldS a b c leaf s₂)

runNat³ : (S × (S × S × S)) → M³~>M
runNat³ (s1 , (s2 , s3 , s4)) {s = σ} {a = α} mmma init
  = eval s1 , ret (eval s2) (eval s3) (eval s4)
  where
    a : σ → σ
    a x = proj₁ (mmma x)

    b : σ → σ → σ
    b x y = proj₁ (proj₂ (mmma x) y)
    
    c : σ → σ → σ → σ
    c x y z = proj₁ (proj₂ (proj₂ (mmma x) y) z)

    ret : σ → σ → σ → α
    ret x y z = proj₂ (proj₂ (proj₂ (mmma x) y) z)

    eval : S → σ
    eval = foldS a b c init

module iso³-correct where
  refoldS : ∀ (s : S) → foldS A B C Leaf s ≡ s
  refoldS Leaf = refl
  refoldS (A x) = cong A (refoldS x)
  refoldS (B x y) = cong₂ B (refoldS x) (refoldS y)
  refoldS (C x y z) = cong₂ id (cong₂ C (refoldS x) (refoldS y)) (refoldS z)

  prod4≡ : ∀ {A B C D : Set}
    {p₁@(x₁ , y₁ , z₁ , w₁) p₂@(x₂ , y₂ , z₂ , w₂) : A × B × C × D}
    → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → w₁ ≡ w₂ → p₁ ≡ p₂
  prod4≡ refl refl refl refl = refl

  reify-run : ∀ (def : S × S × S × S) → reifyNat³ (runNat³ def) ≡ def
  reify-run (x , y , z , w) =
    prod4≡ (refoldS x) (refoldS y) (refoldS z) (refoldS w)

  {- Can't be proved for Agda because M²~>M lacks parametricity

  run-reify : ∀ (nat : M³~>M) {s a} (mmma : State s (State s (State s a))) (s₀ : s)
    → runNat³ (reifyNat³ nat) mmma s₀ ≡ nat mmma s₀
  run-reify nat mmma s₀ = _

  -}

module _ where
  private
    variable
      x₁ x₂ y₁ y₂ z₁ z₂ : S
  
  A-injective : ∀{x y : S} → A x ≡ A y → x ≡ y
  A-injective refl = refl

  B-injective₁ : B x₁ y₁ ≡ B x₂ y₂ → x₁ ≡ x₂
  B-injective₁ refl = refl

  B-injective₂ : B x₁ y₁ ≡ B x₂ y₂ → y₁ ≡ y₂
  B-injective₂ refl = refl

  C-injective₁ : C x₁ y₁ z₁ ≡ C x₂ y₂ z₂ → x₁ ≡ x₂
  C-injective₁ refl = refl

  C-injective₂ : C x₁ y₁ z₁ ≡ C x₂ y₂ z₂ → y₁ ≡ y₂
  C-injective₂ refl = refl
  
  C-injective₃ : C x₁ y₁ z₁ ≡ C x₂ y₂ z₂ → z₁ ≡ z₂
  C-injective₃ refl = refl

-------------------------------------------------

-- To state about Monad laws, make an alias of (T × T × T),
-- the data defining join : M²~>M.

record JoinDef : Set where
  constructor mkJoin
  field
    t : T
    l : T
    r : T

Join : Set₁
Join = M²~>M

runDef : JoinDef → Join
runDef (mkJoin t l r) = runNat² (t , (l , r))

module UsualStateMonad where
  join : Join
  join = usualJoin

  def : JoinDef
  def =
    let t , (l , r) = reifyNat² join 
    in mkJoin t l r
  
  private
    _ : def ≡ mkJoin (G X (F X)) X (F X)
    _ = refl

{-

Monad laws can be seen as a equalities between Mⁿ~>M.

  leftUnit  : (join ∘ pure : M~>M) ≗ (id : M~>M)
  rightUnit : (join ∘ fmap pure : M~>M) ≗ (id : M~>M)
  assoc     : (join ∘ join : M³~>M) ≗ (join ∘ fmap join : M³~>M)

By runNat¹ and runNat³ being isomorphisms, instead of proving the above, one only need to prove the following.

  leftUnit'  : reifyNat¹ (join ∘ pure) ≡ reifyNat¹ id
  rightUnit' : reifyNat¹ (join ∘ fmap pure) ≡ reifyNat¹ id
  assoc'     : reifyNat³ (join ∘ join) ≡ reifyNat³ (join ∘ fmap join)

Furthermore, by runDef being isomorphism, every possible (join : Join) satisfying the above equalities
is an image of every solution of the following "system of equations" on (def : JoinDef).

  leftUnit''  : leftUnitLHS def ≡ idNatRep
  rightUnit'' : rightUnitLHS def ≡ idNatRep
  assoc''     : assocLHS def ≡ assocRHS def

where each functions are

-}

idNatRep : ℕ × ℕ
idNatRep = reifyNat¹ id

idNatRepValue : idNatRep ≡ (1 , 0)
idNatRepValue = refl

leftUnitLHS : JoinDef → ℕ × ℕ
leftUnitLHS def = reifyNat¹ (λ ma → runDef def (pure ma))

rightUnitLHS : JoinDef → ℕ × ℕ
rightUnitLHS def = reifyNat¹ (λ ma → runDef def (fmap pure ma))

assocLHS : JoinDef → S × (S × S × S)
assocLHS def = reifyNat³ (λ mmma → runDef def (runDef def mmma))

assocRHS : JoinDef → S × (S × S × S)
assocRHS def = reifyNat³ (λ mmma → runDef def (fmap (runDef def) mmma))

record MonadLaw (def : JoinDef) : Set where
  field
    leftUnitLaw : leftUnitLHS def ≡ idNatRep
    rightUnitLaw : rightUnitLHS def ≡ idNatRep
    assocLaw : assocLHS def ≡ assocRHS def

-- Validity check: UsualStateMonad.def satisfy MonadLaw
_ : MonadLaw UsualStateMonad.def
_ = record {
    leftUnitLaw = refl;
    rightUnitLaw = refl;
    assocLaw = refl
  }
