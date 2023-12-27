{-# OPTIONS --without-K --safe #-}

module PolymorphicState where

open import Function using (_∘_; id; const; constᵣ; case_of_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties
  using (,-injective)
  renaming (
    ,-injectiveˡ to ,-injective₁;
    ,-injectiveʳ to ,-injective₂
  )
import Data.Product as Product

open import Data.Nat
open import Data.List
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
import Data.List.Properties as ListProp
import Data.Nat.Properties as NatProp
open NatProp using (≮⇒≥)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  renaming ([_] to sing)
open Eq.≡-Reasoning

open import ListLemma

----------------------

variable
  α : Set
  β : Set

----------------------

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

runNat¹ : (ℕ × ℕ) → M~>M
runNat¹ (n₁ , n₂) {s = s} {a = a} ma s0 =
  let f : s → s
      f = proj₁ ∘ ma
  in iterate n₁ f s0 , proj₂ (ma (iterate n₂ f s0))

-- -- reifyNat¹ (runNat¹ nn) ≡ nn
-- -- runNat¹ (reifyNat¹ nat) ma s ≡ nat ma s

-- Similarly, M²~>M ≅ (T × T × T), with T below.

data T : Set where
  F : T -> T
  G : T -> T -> T
  X : T

reifyNat² : M²~>M → T × (T × T)
reifyNat² nat = nat tt X
  where
    tt : State T (State T (T × T))
    tt t1 = F t1 , λ t2 → (G t1 t2 , (t1 , t2))

foldT : (α → α) → (α → α → α) → α → T → α
foldT f g x X     = x
foldT f g x (F t) = f (foldT f g x t)
foldT f g x (G t1 t2) = g (foldT f g x t1) (foldT f g x t2)

runNat² : (T × (T × T)) → M²~>M
runNat² (t , (l , r)) {s = σ} {a = α} mma s = foldT f g s t , ret (foldT f g s l) (foldT f g s r)
  where
    f : σ → σ
    f s1 = proj₁ (mma s1)

    g : σ → σ → σ
    g s1 s2 = proj₁ (proj₂ (mma s1) s2)

    ret : σ → σ → α
    ret s1 s2 = proj₂ (proj₂ (mma s1) s2)

-- -- reifyNat² (runNat² def) ≡ def
-- -- runNat² (reifyNat² nat) mma s ≡ nat mma s

caseT : ∀ (t : T) → (Σ[ t₁ ∈ T ] (t ≡ F t₁)) ⊎ (Σ[ t₁ ∈ T ] (Σ[ t₂ ∈ T ] (t ≡ G t₁ t₂))) ⊎ (t ≡ X)
caseT (F t₁) = inj₁ (t₁ , refl)
caseT (G t₁ t₂) = inj₂ (inj₁ (t₁ , t₂ , refl))
caseT X = inj₂ (inj₂ refl)

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

foldS :  (α → α) → (α → α → α) → (α → α → α → α) → α → S → α
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

module _ where
  A-injective : ∀{x y : S} → A x ≡ A y → x ≡ y
  A-injective refl = refl

  B-injective : ∀{x₁ x₂ y₁ y₂ : S} → B x₁ y₁ ≡ B x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂
  B-injective refl = refl , refl

  C-injective : ∀{x₁ x₂ y₁ y₂ z₁ z₂ : S} → C x₁ y₁ z₁ ≡ C x₂ y₂ z₂ → x₁ ≡ x₂ × y₁ ≡ y₂ × z₁ ≡ z₂
  C-injective refl = refl , refl , refl

-------------------------------------------------

-- To state about Monad laws, make an alias of (T × T × T),
-- the data defining join : M²~>M.

record JoinDef : Set where
  field
    t : T
    l : T
    r : T

Join : Set₁
Join = M²~>M

runDef : JoinDef → Join
runDef def = runNat² (JoinDef.t def , (JoinDef.l def , JoinDef.r def))

module UsualStateMonad where
  join : Join
  join = usualJoin

  def : JoinDef
  def = case reifyNat² join of λ {
      (t , (l , r)) → record { t = t ; l = l ; r = r }
    }
  
  private
    _ : def ≡ record { t = G X (F X) ; l = X ; r = F X }
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

---------------------------------------

countFs : T -> ℕ
countFs = foldT suc constᵣ zero

countGs : T -> ℕ
countGs = foldT id (λ { _ r → suc r }) zero

---- Left and Right unit laws ----

-- By manually evaluating leftUnitLHS and idNatRep:
record LeftUnitProp' (def : JoinDef) : Set where
  open JoinDef def
  field
    eq1 : countGs t ≡ 1
    eq2 : countGs r ≡ 0

makeLeftUnitProp' : (def : JoinDef) → leftUnitLHS def ≡ idNatRep → LeftUnitProp' def
makeLeftUnitProp' def eqs = case ,-injective eqs of λ {
    (eq1 , eq2) → record { eq1 = eq1 ; eq2 = eq2 }
  }

-- By manually evaluating rightUnitLHS and idNatRep:
record RightUnitProp' (def : JoinDef) : Set where
  open JoinDef def
  field
    eq3 : countFs t ≡ 1
    eq4 : countFs l ≡ 0

makeRightUnitProp' : (def : JoinDef) → rightUnitLHS def ≡ idNatRep → RightUnitProp' def
makeRightUnitProp' def eqs = case ,-injective eqs of λ {
    (eq3 , eq4) → record { eq3 = eq3 ; eq4 = eq4 }
  }

---- Associativity ----

-- By manually evaluating assocLHS and assocRHS:
record AssocProp' (def : JoinDef) : Set where
  open JoinDef def

  f : S → S
  f s1 = foldT A B s1 t

  g : S → S → S
  g s1 s2 = C (foldT A B s1 l) (foldT A B s1 r) s2

  g' : S → S → S
  g' s1 s2 = foldT (B s1) (C s1) s2 t

  fl : S
  fl = foldT f g Leaf l

  fr : S
  fr = foldT f g Leaf r

  fl' : S
  fl' = foldT A g' Leaf l

  fr' : S
  fr' = foldT A g' Leaf r

  field
    eq5 : foldT f g Leaf t ≡ foldT A g' Leaf t
    eq6 : foldT A B fl l ≡ fl'
    eq7 : foldT A B fl r ≡ foldT (B fl') (C fl') fr' l
    eq8 : fr ≡ foldT (B fl') (C fl') fr' r

makeAssocProp' : (def : JoinDef) → assocLHS def ≡ assocRHS def → AssocProp' def
makeAssocProp' def eqs = record {
    eq5 = ,-injective₁ eqs ;
    eq6 = ,-injective₁ (,-injective₂ eqs) ;
    eq7 = ,-injective₁ (,-injective₂ (,-injective₂ eqs)) ;
    eq8 = ,-injective₂ (,-injective₂ (,-injective₂ eqs))
  }

------------------------------------

pat-F0-G0 : (t : T) → countFs t ≡ 0 → countGs t ≡ 0 → t ≡ X
pat-F0-G0 X _ _ = refl

pat-F0-G1 : (t : T) → countFs t ≡ 0 → countGs t ≡ 1 → Σ[ u ∈ T ] (t ≡ G u X)
pat-F0-G1 (G u X) _ _ = u , refl

pat-F1-G0 : (t : T) → countFs t ≡ 1 → countGs t ≡ 0 → t ≡ F X
pat-F1-G0 (F X) _ _ = refl

pat-F1-G1 : (t : T)
  → countFs t ≡ 1
  → countGs t ≡ 1
  → Σ[ u ∈ T ] (t ≡ G u (F X) ⊎ t ≡ F (G u X))
pat-F1-G1 (G u (F X)) _ _ = u , inj₁ refl 
pat-F1-G1 (F (G u X)) _ _ = u , inj₂ refl

---------------

data STag : Set where
  At : STag
  Bt : STag
  Ct : STag

pathʳ : S -> List STag
pathʳ = foldS (λ s → At ∷ s) (λ _ s → Bt ∷ s) (λ _ _ s → Ct ∷ s) []

rightAppender1 : (S → S) → Set
rightAppender1 f = ∀ (x : S) → pathʳ (f x) ≡ pathʳ (f Leaf) ++ pathʳ x

rightAppender2 : (S → S → S) → Set
rightAppender2 g = ∀ (x y : S) → pathʳ (g x y) ≡ pathʳ (g Leaf Leaf) ++ pathʳ y

pathʳ-foldT : 
  ∀(f : S → S) (g : S → S → S) (x : S) (t : T)
  → rightAppender1 f → rightAppender2 g
  → pathʳ (foldT f g x t) ≡ pathʳ (foldT f g Leaf t) ++ pathʳ x
pathʳ-foldT f g x (F t) appf appg = begin
    pathʳ (foldT f g x (F t))
  ≡⟨ refl ⟩
    pathʳ (f (foldT f g x t))
  ≡⟨ appf (foldT f g x t) ⟩
    pathʳ (f Leaf) ++ pathʳ (foldT f g x t)
  ≡⟨ cong₂ _++_ refl (pathʳ-foldT f g x t appf appg) ⟩
    pathʳ (f Leaf) ++ (pathʳ (foldT f g Leaf t) ++ pathʳ x)
  ≡⟨ sym (ListProp.++-assoc (pathʳ (f Leaf)) (pathʳ (foldT f g Leaf t)) _) ⟩
    (pathʳ (f Leaf) ++ pathʳ (foldT f g Leaf t)) ++ pathʳ x
  ≡⟨ cong₂ _++_ (sym (appf (foldT f g Leaf t))) refl ⟩
    pathʳ (foldT f g Leaf (F t)) ++ pathʳ x
  ∎
pathʳ-foldT f g x (G u t) appf appg = begin
    pathʳ (foldT f g x (G u t))
  ≡⟨ refl ⟩
    pathʳ (g (foldT f g x u) (foldT f g x t))
  ≡⟨ appg _ (foldT f g x t) ⟩
    pathʳ (g Leaf Leaf) ++ pathʳ (foldT f g x t)
  ≡⟨ cong₂ _++_ refl (pathʳ-foldT f g x t appf appg) ⟩
    pathʳ (g Leaf Leaf) ++ (pathʳ (foldT f g Leaf t) ++ pathʳ x)
  ≡⟨ sym (ListProp.++-assoc (pathʳ (g Leaf Leaf)) (pathʳ (foldT f g Leaf t)) _) ⟩
    (pathʳ (g Leaf Leaf) ++ pathʳ (foldT f g Leaf t)) ++ pathʳ x
  ≡⟨ cong₂ _++_ (sym (appg _ (foldT f g Leaf t))) refl ⟩
    pathʳ (foldT f g Leaf (G u t)) ++ pathʳ x
  ∎
pathʳ-foldT f g x X appf appg = refl

pathʳ-foldT-Fs :
  ∀(f : S → S) (g : S → S → S) (x : S) (t : T)
  → countGs t ≡ 0
  → rightAppender1 f
  → pathʳ (foldT f g x t) ≡ pathʳ (f Leaf) ^^ countFs t ++ pathʳ x
pathʳ-foldT-Fs f g x (F t) noGs app = begin
    pathʳ (foldT f g x (F t))
  ≡⟨⟩
    pathʳ (f (foldT f g x t))
  ≡⟨ app (foldT f g x t) ⟩
    pathʳ (f Leaf) ++ pathʳ (foldT f g x t)
  ≡⟨ cong₂ _++_ refl (pathʳ-foldT-Fs f g x t noGs app) ⟩
    pathʳ (f Leaf) ++ (pathʳ (f Leaf) ^^ countFs t) ++ pathʳ x
  ≡˘⟨ ListProp.++-assoc (pathʳ (f Leaf)) (repeatN (countFs t) (pathʳ (f Leaf))) _ ⟩
    (pathʳ (f Leaf) ++ pathʳ (f Leaf) ^^ countFs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (f Leaf) ^^ suc (countFs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (f Leaf) ^^ countFs (F t) ++ pathʳ x
  ∎ 
pathʳ-foldT-Fs f g x X noGs app = refl

pathʳ-foldT-Gs :
  ∀(f : S → S) (g : S → S → S) (x : S) (t : T)
  → countFs t ≡ 0
  → rightAppender2 g
  → pathʳ (foldT f g x t) ≡ pathʳ (g Leaf Leaf) ^^ countGs t ++ pathʳ x
pathʳ-foldT-Gs f g x (G t' t) noFs app = begin
    pathʳ (foldT f g x (G t' t))
  ≡⟨⟩
    pathʳ (g (foldT f g x t') (foldT f g x t))
  ≡⟨ app (foldT f g x t') (foldT f g x t) ⟩
    pathʳ (g Leaf Leaf) ++ pathʳ (foldT f g x t)
  ≡⟨ cong₂ _++_ refl (pathʳ-foldT-Gs f g x t noFs app) ⟩
    pathʳ (g Leaf Leaf) ++ (pathʳ (g Leaf Leaf) ^^ countGs t ++ pathʳ x)
  ≡˘⟨ ListProp.++-assoc (pathʳ (g Leaf Leaf)) (pathʳ (g Leaf Leaf) ^^ countGs t) _ ⟩
    (pathʳ (g Leaf Leaf) ++ pathʳ (g Leaf Leaf) ^^ countGs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (g Leaf Leaf) ^^ suc (countGs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (g Leaf Leaf) ^^ countGs (G t' t) ++ pathʳ x
  ∎
pathʳ-foldT-Gs f g x X noFs appender = refl

------------------------------------

record MonadProp (def : JoinDef) : Set where
  field
    leftUnitP : LeftUnitProp' def
    rightUnitP : RightUnitProp' def
    assocP : AssocProp' def

  open LeftUnitProp' leftUnitP public
  open RightUnitProp' rightUnitP public
  open AssocProp' assocP public

-- (eq1) and (eq3) implies
--   t = G u (F X) | F (G u X)    (for some u)
gf-or-fg : (def : JoinDef) → (props : MonadProp def) →
  Σ[ u ∈ T ] (JoinDef.t def ≡ G u (F X) ⊎ JoinDef.t def ≡ F (G u X))
gf-or-fg def props = pat-F1-G1 (JoinDef.t def) (MonadProp.eq3 props) (MonadProp.eq1 props)

-- (eq2) and (eq8) implies
--   r = X | F X
module R-01 (def : JoinDef) (props : MonadProp def) where
  open JoinDef def
  open MonadProp props
  
  -- r = F^n X
  n : ℕ
  n = countFs r

  pathʳ-eq8 : pathʳ (foldT A B Leaf t) ^^ n ≡ [ Bt ] ^^ n ++ [ At ] ^^ n
  pathʳ-eq8 = subst₂ _≡_ pathʳ-eq8-lhs pathʳ-eq8-rhs (cong pathʳ eq8)
    where
      appenderA : rightAppender1 A
      appenderA x = refl

      appenderB : ∀ (s : S) → rightAppender1 (B s)
      appenderB _ x = refl

      appenderF : ∀ (t : T) → rightAppender1 (λ { x → foldT A B x t })
      appenderF (F t) x = cong (_∷_ At) (appenderF t x)
      appenderF (G _ t) x = cong (_∷_ Bt) (appenderF t x)
      appenderF X x = refl

      pathʳ-t : List STag
      pathʳ-t = pathʳ (foldT A B Leaf t)

      pathʳ-fr' : pathʳ fr' ≡ [ At ] ^^ n
      pathʳ-fr' =
        begin
          pathʳ fr'
        ≡⟨⟩
          pathʳ (foldT A g' Leaf r)
        ≡⟨ pathʳ-foldT-Fs A _ Leaf r eq2 appenderA ⟩
          repeatN n [ At ] ++ []
        ≡⟨ ListProp.++-identityʳ _ ⟩
          repeatN n [ At ]
        ∎

      pathʳ-eq8-lhs : pathʳ (foldT f g Leaf r) ≡ pathʳ-t ^^ n 
      pathʳ-eq8-lhs =
        begin
          pathʳ (foldT f g Leaf r)
        ≡⟨ pathʳ-foldT-Fs f g Leaf r eq2 (appenderF t) ⟩
          repeatN n pathʳ-t ++ pathʳ Leaf
        ≡⟨ ListProp.++-identityʳ _ ⟩
          repeatN n pathʳ-t
        ∎
      
      pathʳ-eq8-rhs : pathʳ (foldT (B fl') (C fl') fr' r) ≡ [ Bt ] ^^ n ++ [ At ] ^^ n
      pathʳ-eq8-rhs =
        begin
          pathʳ (foldT (B fl') (C fl') fr' r)
        ≡⟨ pathʳ-foldT-Fs (B fl') (C fl') fr' r eq2 (appenderB fl') ⟩
          [ Bt ] ^^ n ++ pathʳ fr'
        ≡⟨ cong (_++_ ([ Bt ] ^^ n)) pathʳ-fr' ⟩
          [ Bt ] ^^ n ++ [ At ] ^^ n
        ∎
  
  r-01 : r ≡ X ⊎ r ≡ F X
  r-01 = Data.Sum.map (λ r0 → pat-F0-G0 r r0 eq2) (λ r1 → pat-F1-G0 r r1 eq2) n-01
    where
      n-01 : n ≡ 0 ⊎ n ≡ 1
      n-01 = n≯1→0or1 (no-repeats n _ { a = Bt } { b = At } (λ ()) pathʳ-eq8)

-- (eq4) and (eq6) implies
--   l = X | G k X    (for some k)
module L-01 (def : JoinDef) (props : MonadProp def) where
  open JoinDef def
  open MonadProp props

  -- l = (G _)^m X
  m : ℕ
  m = countGs l

  pathʳ-eq6 : [ Bt ] ^^ m ++ [ Ct ] ^^ m ≡ pathʳ (foldT (B Leaf) (C Leaf) Leaf t) ^^ m
  pathʳ-eq6 = subst₂ _≡_ pathʳ-eq6-lhs pathʳ-eq6-rhs (cong pathʳ eq6)
    where
      appender2B : rightAppender2 B
      appender2B x y = refl

      appender2G : rightAppender2 g
      appender2G x y = refl

      appender2g' : ∀ (t : T) → rightAppender2 (λ x y → foldT (B x) (C x) y t)
      appender2g' (F t₁) x y = cong (_∷_ Bt) (appender2g' t₁ x y)
      appender2g' (G t₁ t₂) x y = cong (_∷_ Ct) (appender2g' t₂ x y)
      appender2g' X x y = refl

      pathʳ-fl : pathʳ fl ≡ [ Ct ] ^^ m
      pathʳ-fl = begin
          pathʳ (foldT f g Leaf l)
        ≡⟨ pathʳ-foldT-Gs f g Leaf l eq4 appender2G ⟩
          [ Ct ] ^^ m ++ []
        ≡⟨ ListProp.++-identityʳ ([ Ct ] ^^ m) ⟩
          [ Ct ] ^^ m
        ∎
      
      pathʳ-eq6-lhs : pathʳ (foldT A B fl l) ≡  [ Bt ] ^^ m ++ [ Ct ] ^^ m
      pathʳ-eq6-lhs = begin
          pathʳ (foldT A B fl l)
        ≡⟨ pathʳ-foldT-Gs A B fl l eq4 appender2B ⟩
          [ Bt ] ^^ m ++ pathʳ fl
        ≡⟨ cong₂ _++_ refl pathʳ-fl ⟩
          [ Bt ] ^^ m ++ [ Ct ] ^^ m
        ∎

      pathʳ-eq6-rhs : pathʳ fl' ≡ pathʳ (foldT (B Leaf) (C Leaf) Leaf t) ^^ m
      pathʳ-eq6-rhs = begin
          pathʳ fl'
        ≡⟨⟩
          pathʳ (foldT A g' Leaf l)
        ≡⟨ pathʳ-foldT-Gs A g' Leaf l eq4 (appender2g' t) ⟩
          pathʳ (foldT (B Leaf) (C Leaf) Leaf t) ^^ m ++ []
        ≡⟨ ListProp.++-identityʳ _ ⟩
          pathʳ (foldT (B Leaf) (C Leaf) Leaf t) ^^ m
        ∎
 
  l-01 : (l ≡ X) ⊎ (Σ[ k ∈ T ] (l ≡ G k X))
  l-01 = Data.Sum.map (pat-F0-G0 l eq4) (pat-F0-G1 l eq4) m-01
    where
      m-01 : m ≡ 0 ⊎ m ≡ 1
      m-01 = n≯1→0or1 (no-repeats m _ { a = Bt } { b = Ct } (λ ()) (sym pathʳ-eq6))

-- Combining them, the possible JoinDef is one of:

data JoinDefCase : JoinDef → Set where
  def-GF-X-X : (u : T) → JoinDefCase (record { t = G u (F X) ; l = X ; r = X })
  def-GF-X-FX : (u : T) → JoinDefCase (record { t = G u (F X) ; l = X ; r = F X })
  def-GF-GX-r : (u k r : T) → JoinDefCase (record { t = G u (F X) ; l = G k X ; r = r })
  def-FG-X-X : (u : T) → JoinDefCase (record { t = F (G u X) ; l = X ; r = X })
  def-FG-GX-X : (u k : T) → JoinDefCase (record { t = F (G u X) ; l = G k X ; r = X })
  def-FG-l-FX : (u l : T) → JoinDefCase (record { t = F (G u X) ; l = l ; r = F X })

classify : (def : JoinDef) → (props : MonadProp def) → JoinDefCase def
classify def props = result
  where
    gffg : Σ[ u ∈ T ] (JoinDef.t def ≡ G u (F X) ⊎ JoinDef.t def ≡ F (G u X))
    gffg = gf-or-fg def props
    open L-01 def props using (l-01)
    open R-01 def props using (r-01)

    result : JoinDefCase def
    result with gffg        | l-01           | r-01
    result  | u , inj₁ refl | inj₁ refl       | inj₁ refl = def-GF-X-X u
    result  | u , inj₁ refl | inj₁ refl       | inj₂ refl = def-GF-X-FX u
    result  | u , inj₁ refl | inj₂ (k , refl) | _         = def-GF-GX-r u k (JoinDef.r def)
    result  | u , inj₂ refl | inj₁ refl       | inj₁ refl = def-FG-X-X u
    result  | u , inj₂ refl | inj₂ (k , refl) | inj₁ refl = def-FG-GX-X u k
    result  | u , inj₂ refl | _               | inj₂ refl = def-FG-l-FX u (JoinDef.l def)

-- Let's resolve each case!

-- | Simply impossible to satisfy eq6
case-GF-GX-r : ∀ (u k r : T) (props : MonadProp (record { t = G u (F X) ; l = G k X ; r = r })) → ⊥
case-GF-GX-r u k r props = case MonadProp.eq6 props of λ ()

-- | Simply impossible to satisfy eq8
case-FG-l-FX : ∀(u l : T) → MonadProp (record { t = F (G u X) ; l = l ; r = F X }) → ⊥
case-FG-l-FX u l props = case MonadProp.eq8 props of λ ()

-- | Impossible to satisfy eq5, by pattern matching u
case-GF-X-X : ∀(u : T) → (props : MonadProp (record { t = G u (F X) ; l = X ; r = X })) → ⊥
case-GF-X-X u     props with MonadProp.eq5 props
case-GF-X-X (F _)   props  | ()
case-GF-X-X (G _ _) props  | ()
case-GF-X-X X       props  | ()

{-
    fu : S
    fu = foldT f g Leaf u

    fu' : S
    fu' = foldT A g' Leaf u

    eq5' : C fu fu (B (foldT A B Leaf u) (A Leaf))
        ≡ C fu' (foldT (B fu') (C fu') (A Leaf) u) (B fu' (A Leaf))
    eq5' = eq5

    eq5-1 : fu ≡ fu'
    eq5-1 = proj₁ (C-injective eq5')

    eq5-2 : fu ≡ foldT (B fu') (C fu') (A Leaf) u
    eq5-2 = proj₁ (proj₂ (C-injective eq5'))

    eq5-3 : foldT A B Leaf u ≡ fu'
    eq5-3 = proj₁ (B-injective (proj₂ (proj₂ (C-injective eq5'))))

    inequal-fold : (x : T) → foldT A B Leaf x ≢ foldT (B fu') (C fu') (A Leaf) x
    inequal-fold (F _) ()
    inequal-fold (G _ _) ()
    inequal-fold X ()
-}

-- | Only u ≡ X satisfy eq5
case-GF-X-FX : ∀(u : T) → (props : MonadProp (record { t = G u (F X) ; l = X ; r = F X })) → u ≡ X
case-GF-X-FX u props with MonadProp.eq5 props
case-GF-X-FX (F _)   props | ()
case-GF-X-FX (G _ _) props | ()
case-GF-X-FX X       props | _ = refl

-- | Same!
case-FG-X-X : ∀ (u : T) → (props : MonadProp (record { t = F (G u X) ; l = X ; r = X })) → ⊥
case-FG-X-X u       props with MonadProp.eq5 props
case-FG-X-X (F _)   _     | ()
case-FG-X-X (G _ _) _     | ()
case-FG-X-X X       _     | ()

case-FG-GX-X : ∀(u k : T) → MonadProp (record { t = F (G u X) ; l = G k X ; r = X }) → ⊥
case-FG-GX-X u k props = contradiction
  where
    def : JoinDef
    def = record { t = F (G u X) ; l = G k X ; r = X }

    open MonadProp props

    depth : S → ℕ
    depth = foldS suc (λ x _ → suc x) (λ x _ _ → suc x) zero

    depth-foldT-AB : ∀ (s : S) (t : T) →
      depth (foldT A B s t) ≡ depth (foldT A B Leaf t) + depth s
    depth-foldT-AB s (F t) = cong suc (depth-foldT-AB s t)
    depth-foldT-AB s (G t t₁) = cong suc (depth-foldT-AB s t)
    depth-foldT-AB s X = refl

    fk : S
    fk = foldT f g Leaf k

    fk' : S
    fk' = foldT A g' Leaf k
    
    _ : fl' ≡ B fk' (C fk' (foldT (B fk') (C fk') Leaf u) Leaf)
    _ = refl

    eq7' : C (B (foldT A B fk k) fk) fk Leaf ≡
            C fl' (foldT (B fl') (C fl') Leaf k) Leaf
    eq7' = eq7

    eq7-1 : B (foldT A B fk k) fk ≡ fl'
    eq7-1 = proj₁ (C-injective eq7')

    eq7-2 : fk ≡ foldT (B fl') (C fl') Leaf k
    eq7-2 = proj₁ (proj₂ (C-injective eq7'))

    eq7-1-depth : 1 + depth (foldT A B Leaf k) + depth fk ≡ 1 + depth fk'
    eq7-1-depth =
      begin
        1 + depth (foldT A B Leaf k) + depth fk
      ≡˘⟨ cong suc (depth-foldT-AB fk k)⟩
        1 + depth (foldT A B fk k)
      ≡⟨ cong depth eq7-1 ⟩
        1 + depth fk'
      ∎
    
    depth-fk≤fk' : depth fk ≤ depth fk'
    depth-fk≤fk' =
      subst (depth fk ≤_)
            (NatProp.suc-injective eq7-1-depth)
            (NatProp.m≤n+m (depth fk) (depth (foldT A B Leaf k)))
    
    eq7-2-depth : depth fk ≡ depth (foldT (B fl') (C fl') Leaf k)
    eq7-2-depth = cong depth eq7-2
    
    2+n>n : ∀ (n : ℕ) → suc (suc n) > n
    2+n>n _ = NatProp.m≤n⇒m≤1+n NatProp.≤-refl
    -- suc (suc n) > n = suc n ≥ n = n ≤ suc n

    m≡2+n⇒m>n : ∀(m n : ℕ) → m ≡ 2 + n → m > n
    m≡2+n⇒m>n m n refl = 2+n>n n

    contradiction : ⊥
    contradiction with caseT k       | eq7-2-depth
    contradiction  | inj₁ (_ , refl) | depth-fk≡2+fk' =
      NatProp.≤⇒≯ depth-fk≤fk' (m≡2+n⇒m>n (depth fk) (depth fk') depth-fk≡2+fk')
    contradiction  | inj₂ (inj₁ (_ , _ , refl)) | depth-fk≡2+fk' =
      NatProp.≤⇒≯ depth-fk≤fk' (m≡2+n⇒m>n (depth fk) (depth fk') depth-fk≡2+fk')
    contradiction  | inj₂ (inj₂ refl) | _ = case eq7-1 of λ ()

uniqueness : (def : JoinDef) (props : MonadProp def) → def ≡ UsualStateMonad.def
uniqueness def props = result
  where
    result : def ≡ UsualStateMonad.def
    result with classify def props
    result | def-GF-X-X u = ⊥-elim (case-GF-X-X u props)
    result | def-GF-X-FX u = cong (λ u → record { t = G u (F X) ; l = X ; r = F X }) (case-GF-X-FX u props)
    result | def-GF-GX-r u k r = ⊥-elim (case-GF-GX-r u k r props)
    result | def-FG-X-X u = ⊥-elim (case-FG-X-X u props)
    result | def-FG-GX-X u k = ⊥-elim (case-FG-GX-X u k props)
    result | def-FG-l-FX u l = ⊥-elim (case-FG-l-FX u l props)

-- Sanity check: UsualStateMonad.def satisfy MonadProp
_ : MonadProp (UsualStateMonad.def)
_ = record {
  leftUnitP = record {
    eq1 = refl ;
    eq2 = refl
  } ;
  rightUnitP = record {
    eq3 = refl ;
    eq4 = refl
  } ;
  assocP = record {
    eq5 = refl ;
    eq6 = refl ;
    eq7 = refl ;
    eq8 = refl
  }
  }
