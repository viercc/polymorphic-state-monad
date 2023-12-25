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
open import Data.Empty using (⊥-elim)
import Data.List.Properties as ListProp
import Data.Nat.Properties as NatProp
open NatProp using (≮⇒≥)

import Relation.Binary.PropositionalEquality as Eq
open Eq hiding ([_])
open Eq.≡-Reasoning

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

iterate : ℕ → (α → α) → α → α
iterate zero _ x = x
iterate (suc n) f x = f (iterate n f x)

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

  -- Originally l' and r'

  fl' : S
  fl' = foldT A g' Leaf l

  fr' : S
  fr' = foldT A g' Leaf r

  field
    eq5 : foldT f g Leaf t ≡ foldT A g' Leaf t
    eq6 : foldT A B (foldT f g Leaf l) l ≡ fl'
    eq7 : foldT A B (foldT f g Leaf l) r ≡ foldT (B fl') (C fl') fr' l
    eq8 : foldT f g Leaf r ≡ foldT (B fl') (C fl') fr' r

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

-- Nat properties

n≤1-is-01 : ∀{n : ℕ} → n ≤ 1 → n ≡ 0 ⊎ n ≡ 1
n≤1-is-01 {n = zero} p = inj₁ refl
n≤1-is-01 {n = suc n} (s≤s z≤n) = inj₂ refl

≯⇒≤ : ∀{ n m : ℕ } → (n ≯ m) → n ≤ m
≯⇒≤ = ≮⇒≥

-- List properties

repeatN : ℕ → List α → List α
repeatN n x = iterate n (_++_ x) []

syntax repeatN n x = x ^^ n

length-repeatN : (x : List α) → (n : ℕ) → length (x ^^ n) ≡ n * length x
length-repeatN x zero = refl
length-repeatN x (suc n) = begin
    length (x ^^ suc n)
  ≡⟨⟩
    length (x ++ x ^^ n)
  ≡⟨ ListProp.length-++ x ⟩
    length x + length (x ^^ n)
  ≡⟨ cong (_+_ (length x)) (length-repeatN x n) ⟩
    length x + n * length x
  ≡⟨⟩
    suc n * length x
  ∎

repeat-+ : (x : List α) → (n m : ℕ) → x ^^ n ++ x ^^ m ≡ x ^^ (n + m)
repeat-+ x zero m = refl
repeat-+ x (suc n) m = begin
    (x ^^ suc n) ++ x ^^ m
  ≡⟨⟩
    (x ++ x ^^ n) ++ x ^^ m
  ≡⟨ ListProp.++-assoc x (x ^^ n) (x ^^ m) ⟩
    x ++ (x ^^ n ++ x ^^ m)
  ≡⟨ cong₂ _++_ refl (repeat-+ x n m) ⟩
    x ++ x ^^ (n + m)
  ≡⟨⟩
    x ^^ (suc n + m)
  ∎

repeat-* : (x : List α) → (n m : ℕ) → (x ^^ n) ^^ m ≡ x ^^ (m * n)
repeat-* x n zero = refl
repeat-* x n (suc m) = begin
    (x ^^ n) ^^ (suc m)
  ≡⟨⟩
    x ^^ n ++ (x ^^ n) ^^ m
  ≡⟨ cong₂ _++_ refl (repeat-* x n m) ⟩
    x ^^ n ++ x ^^ (m * n)
  ≡⟨ repeat-+ x n (m * n) ⟩
    x ^^ (n + m * n)
  ≡⟨ refl ⟩
    x ^^ (suc m * n)
  ∎

repeat-*-comm : (x : List α) → (n m : ℕ) → (x ^^ n) ^^ m ≡ (x ^^ m) ^^ n
repeat-*-comm x n m = begin
    (x ^^ n) ^^ m
  ≡⟨ repeat-* x n m ⟩
    x ^^ (m * n)
  ≡⟨ cong₂ repeatN (NatProp.*-comm m n) refl ⟩
    x ^^ (n * m)
  ≡˘⟨ repeat-* x m n ⟩
    (x ^^ m) ^^ n
  ∎

drop-repeat : ( a : α ) → (n : ℕ) → (xs : List α) → drop n ([ a ] ^^ n ++ xs) ≡ xs
drop-repeat a zero xs = refl
drop-repeat a (suc n) xs = begin
    drop (suc n) ([ a ] ^^ suc n ++ xs)
  ≡⟨ refl ⟩
    drop (suc n) (a ∷ [ a ] ^^ n ++ xs)
  ≡⟨ drop-repeat a n xs ⟩
    xs
  ∎

repeat-prefix : (n : ℕ) → (xs ys zs : List α) → (a : α) →
  (xs ++ ys ≡ [ a ] ^^ n ++ zs) → length xs ≤ n → xs ≡ [ a ] ^^ length xs
repeat-prefix n [] ys zs a eq len≤n = refl
repeat-prefix (suc n) (x ∷ xs) ys zs a eq (s≤s leq₁) =
  case ListProp.∷-injective eq of λ {
    (eq-x , eq-xs) → cong₂ _∷_ eq-x (repeat-prefix n xs ys zs a eq-xs leq₁)
  }

no-repeats-aux : (n : ℕ) → { a b : α } →
  a ≢ b →
  ([ a ]  ^^ suc n) ^^ 2 ≢ [ a ] ^^ suc n ++ [ b ] ^^ suc n
no-repeats-aux n {a = a} {b = b} a≢b eq = a≢b (ListProp.∷-injectiveˡ an≡bn)
  where
    sn : ℕ
    sn = suc n

    an≡bn : [ a ] ^^ sn ≡ [ b ] ^^ sn
    an≡bn = begin
        [ a ] ^^ sn
      ≡˘⟨ ListProp.++-identityʳ _ ⟩
        [ a ] ^^ sn ++ []
      ≡˘⟨ drop-repeat a sn _ ⟩
        drop sn ([ a ] ^^ sn ++ ([ a ] ^^ sn ++ []))
      ≡⟨⟩
        drop sn (([ a ] ^^ sn) ^^ 2)
      ≡⟨ cong (drop sn) eq ⟩
        drop sn ([ a ] ^^ sn ++ [ b ] ^^ sn)
      ≡⟨ drop-repeat a sn _ ⟩
        [ b ] ^^ sn
      ∎

no-repeats :
  (n : ℕ) → (xs : List α) → { a b : α } →
  (a ≢ b) →
  (xs ^^ n ≡ [ a ] ^^ n ++ [ b ] ^^ n) →
  (n ≯ 1)
no-repeats (suc (suc n₂)) xs {a = a} {b = b} a≢b eqn (s≤s (s≤s le₂)) =
  no-repeats-aux (suc n₂) a≢b (begin
      ([ a ] ^^ n) ^^ 2
    ≡⟨ repeat-*-comm [ a ] n 2 ⟩
      ([ a ] ^^ 2) ^^ n
    ≡⟨⟩
      (a ∷ a ∷ []) ^^ n
    ≡˘⟨ cong (repeatN n) xs≡aa ⟩
      xs ^^ n
    ≡⟨ eqn ⟩
      [ a ] ^^ n ++ [ b ] ^^ n
    ∎)
   where
     n : ℕ
     n = suc (suc n₂)
     
     m : ℕ
     m = length xs

     n*m≡n*2 : n * m ≡ n * 2
     n*m≡n*2 = begin
        n * m
      ≡˘⟨ length-repeatN xs n ⟩
        length (xs ^^ n)
      ≡⟨ cong length eqn ⟩
        length ([ a ] ^^ n ++ [ b ] ^^ n)
      ≡⟨ ListProp.length-++ ([ a ] ^^ n) ⟩
        length ([ a ] ^^ n) + length ([ b ] ^^ n)
      ≡⟨ cong₂ _+_ (length-repeatN [ a ] n) (length-repeatN [ b ] n) ⟩
        n * length [ a ] + n * length [ b ]
      ≡⟨⟩
        n * 1 + n * 1
      ≡˘⟨ NatProp.*-distribˡ-+ n 1 1 ⟩
        n * 2
      ∎
     
     m≡2 : m ≡ 2
     m≡2 = NatProp.*-cancelˡ-≡ m 2 n n*m≡n*2

     xs≡aa : xs ≡ a ∷ a ∷ []
     xs≡aa = begin
        xs
      ≡⟨ repeat-prefix n xs _ _ a eqn (respˡ _≤_ (sym m≡2) (s≤s (s≤s le₂))) ⟩
        [ a ] ^^ m
      ≡⟨ cong₂ repeatN m≡2 refl ⟩
        [ a ] ^^ 2
      ≡⟨⟩
        a ∷ a ∷ []
      ∎

--------

data STag : Set where
  At : STag
  Bt : STag
  Ct : STag

pathʳ : S -> List STag
pathʳ = foldS (λ s → At ∷ s) (λ _ s → Bt ∷ s) (λ _ _ s → Ct ∷ s) []

rightAppender1 : (S → S) → Set
rightAppender1 f = ∀ (x : S) → pathʳ (f x) ≡ pathʳ (f Leaf) ++ pathʳ x

pathʳ-iterByFs :
  ∀(t : T) (f : S → S) {g : _} (x : S)
  → countGs t ≡ 0
  → rightAppender1 f
  → pathʳ (foldT f g x t) ≡ pathʳ (f Leaf) ^^ countFs t ++ pathʳ x
pathʳ-iterByFs (F t) f {g = g} x noGs appender = begin
    pathʳ (foldT f g x (F t))
  ≡⟨⟩
    pathʳ (f (foldT f g x t))
  ≡⟨ appender (foldT f g x t) ⟩
    pathʳ (f Leaf) ++ pathʳ (foldT f g x t)
  ≡⟨ cong₂ _++_ refl (pathʳ-iterByFs t f x noGs appender) ⟩
    pathʳ (f Leaf) ++ (pathʳ (f Leaf) ^^ countFs t) ++ pathʳ x
  ≡˘⟨ ListProp.++-assoc (pathʳ (f Leaf)) (repeatN (countFs t) (pathʳ (f Leaf))) _ ⟩
    (pathʳ (f Leaf) ++ pathʳ (f Leaf) ^^ countFs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (f Leaf) ^^ suc (countFs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (f Leaf) ^^ countFs (F t) ++ pathʳ x
  ∎ 
pathʳ-iterByFs X f {g = g} x noGs appenderProp = refl

rightAppender2 : (S → S → S) → Set
rightAppender2 g = ∀ (x y : S) → pathʳ (g x y) ≡ pathʳ (g Leaf Leaf) ++ pathʳ y

pathʳ-iterByGs :
  ∀(t : T) { f } (g : S → S → S) (x : S)
  → countFs t ≡ 0
  → rightAppender2 g
  → pathʳ (foldT f g x t) ≡ pathʳ (g Leaf Leaf) ^^ countGs t ++ pathʳ x
pathʳ-iterByGs (G t' t) {f = f} g x noFs appender = begin
    pathʳ (foldT f g x (G t' t))
  ≡⟨⟩
    pathʳ (g (foldT f g x t') (foldT f g x t))
  ≡⟨ appender (foldT f g x t') (foldT f g x t) ⟩
    pathʳ (g Leaf Leaf) ++ pathʳ (foldT f g x t)
  ≡⟨ cong₂ _++_ refl (pathʳ-iterByGs t g x noFs appender) ⟩
    pathʳ (g Leaf Leaf) ++ (pathʳ (g Leaf Leaf) ^^ countGs t ++ pathʳ x)
  ≡˘⟨ ListProp.++-assoc (pathʳ (g Leaf Leaf)) (pathʳ (g Leaf Leaf) ^^ countGs t) _ ⟩
    (pathʳ (g Leaf Leaf) ++ pathʳ (g Leaf Leaf) ^^ countGs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (g Leaf Leaf) ^^ suc (countGs t) ++ pathʳ x
  ≡⟨⟩
    pathʳ (g Leaf Leaf) ^^ countGs (G t' t) ++ pathʳ x
  ∎
pathʳ-iterByGs X {f = f} g x noFs appender = refl

------------------------------------

record MonadProp (def : JoinDef) : Set where
  field
    leftUnitP : LeftUnitProp' def
    rightUnitP : RightUnitProp' def
    assocP : AssocProp' def

  open LeftUnitProp' leftUnitP public
  open RightUnitProp' rightUnitP public
  open AssocProp' assocP public

module StateMonadUniquenessImpl (def : JoinDef) (props : MonadProp def) where
  open JoinDef def
  open MonadProp props
  
  gf-or-fg-sum : _
  gf-or-fg-sum = pat-F1-G1 t eq3 eq1

  u : T
  u = proj₁ gf-or-fg-sum
  
  gf-or-fg : t ≡ G u (F X) ⊎ t ≡ F (G u X)
  gf-or-fg = proj₂ gf-or-fg-sum
  
  r-depth : ℕ
  r-depth = countFs r

  l-depth : ℕ
  l-depth = countGs l

  pathʳ-eq8 : pathʳ (foldT A B Leaf t) ^^ r-depth ≡ [ Bt ] ^^ r-depth ++ [ At ] ^^ r-depth
  pathʳ-eq8 = subst₂ _≡_ pathʳ-eq8-lhs pathʳ-eq8-rhs (cong pathʳ eq8)
    where
      appenderA : rightAppender1 A
      appenderA x = refl

      appenderB : ∀ (s : S) → rightAppender1 (B s)
      appenderB _ x = refl

      appenderF : ∀ (t : T) → rightAppender1 (λ { x → foldT A B x t })
      appenderF (F t) x =
        begin
          pathʳ (foldT A B x (F t))
        ≡⟨⟩
          At ∷ pathʳ (foldT A B x t)
        ≡⟨ cong (_∷_ At) (appenderF t x) ⟩
          At ∷ (pathʳ (foldT A B Leaf t) ++ pathʳ x)
        ≡⟨⟩
          pathʳ (foldT A B Leaf (F t)) ++ pathʳ x
        ∎
      appenderF (G t' t) x = begin
          pathʳ (foldT A B x (G t' t))
        ≡⟨⟩
          Bt ∷ pathʳ (foldT A B x t)
        ≡⟨ cong (_∷_ Bt) (appenderF t x) ⟩
          Bt ∷ (pathʳ (foldT A B Leaf t) ++ pathʳ x)
        ≡⟨⟩
          pathʳ (foldT A B Leaf (G t' t)) ++ pathʳ x
        ∎
      appenderF X x = refl

      pathʳ-eq8-lhs : pathʳ (foldT f g Leaf r) ≡ pathʳ (foldT A B Leaf t) ^^ r-depth 
      pathʳ-eq8-lhs =
        begin
          pathʳ (foldT f g Leaf r)
        ≡⟨ pathʳ-iterByFs r f Leaf eq2 (appenderF t) ⟩
          repeatN r-depth (pathʳ (foldT A B Leaf t)) ++ pathʳ Leaf
        ≡⟨ ListProp.++-identityʳ _ ⟩
          repeatN r-depth (pathʳ (foldT A B Leaf t))
        ∎

      pathʳ-fr' : pathʳ fr' ≡ [ At ] ^^ r-depth
      pathʳ-fr' =
        begin
          pathʳ fr'
        ≡⟨⟩
          pathʳ (foldT A g' Leaf r)
        ≡⟨ pathʳ-iterByFs r A Leaf eq2 appenderA ⟩
          repeatN r-depth [ At ] ++ []
        ≡⟨ ListProp.++-identityʳ _ ⟩
          repeatN r-depth [ At ]
        ∎

      pathʳ-eq8-rhs : pathʳ (foldT (B fl') (C fl') fr' r) ≡ [ Bt ] ^^ r-depth ++ [ At ] ^^ r-depth
      pathʳ-eq8-rhs =
        begin
          pathʳ (foldT (B fl') (C fl') fr' r)
        ≡⟨ pathʳ-iterByFs r (B fl') fr' eq2 (appenderB fl') ⟩
          [ Bt ] ^^ r-depth ++ pathʳ fr'
        ≡⟨ cong (_++_ ([ Bt ] ^^ r-depth)) pathʳ-fr' ⟩
          [ Bt ] ^^ r-depth ++ [ At ] ^^ r-depth
        ∎

  pathʳ-eq6 : [ Bt ] ^^ l-depth ++ [ Ct ] ^^ l-depth ≡ pathʳ (foldT (B Leaf) (C Leaf) Leaf t) ^^ l-depth
  pathʳ-eq6 = subst₂ _≡_ pathʳ-eq6-lhs pathʳ-eq6-rhs (cong pathʳ eq6)
    where
      appender2B : rightAppender2 B
      appender2B x y = refl

      appender2G : rightAppender2 g
      appender2G x y = refl

      pathʳ-eq6-lhs : pathʳ (foldT A B (foldT f g Leaf l) l) ≡  [ Bt ] ^^ l-depth ++ [ Ct ] ^^ l-depth
      pathʳ-eq6-lhs = begin
          pathʳ (foldT A B (foldT f g Leaf l) l)
        ≡⟨ pathʳ-iterByGs l B (foldT f g Leaf l) eq4 appender2B ⟩
          [ Bt ] ^^ l-depth ++ pathʳ (foldT f g Leaf l)
        ≡⟨ cong₂ _++_ refl (pathʳ-iterByGs l g Leaf eq4 appender2G) ⟩
          [ Bt ] ^^ l-depth ++ ([ Ct ] ^^ l-depth ++ [])
        ≡⟨ cong₂ _++_ refl (ListProp.++-identityʳ ([ Ct ] ^^ l-depth)) ⟩
          [ Bt ] ^^ l-depth ++ [ Ct ] ^^ l-depth
        ∎

      pathʳ-eq6-rhs : pathʳ fl' ≡ pathʳ (foldT (B Leaf) (C Leaf) Leaf t) ^^ l-depth
      pathʳ-eq6-rhs = _
 
  r-depth-01 : r-depth ≡ 0 ⊎ r-depth ≡ 1
  r-depth-01 = n≤1-is-01 (≯⇒≤ (no-repeats r-depth _ { a = Bt } { b = At } (λ ()) pathʳ-eq8))

  l-depth-01 : l-depth ≡ 0 ⊎ l-depth ≡ 1
  l-depth-01 = n≤1-is-01 (≯⇒≤ (no-repeats l-depth _ { a = Bt } { b = Ct } (λ ()) (sym pathʳ-eq6)))

  gfcase-uniqueness : t ≡ G u (F X) → (def ≡ UsualStateMonad.def)
  gfcase-uniqueness = _

  fgcase-impossible : ¬ (t ≡ F (G u X))
  fgcase-impossible = _

  uniqueness : def ≡ UsualStateMonad.def
  uniqueness = Data.Sum.[  gfcase-uniqueness , ⊥-elim ∘ fgcase-impossible ] gf-or-fg
 