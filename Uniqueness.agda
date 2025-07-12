{-# OPTIONS --without-K --safe #-}

{-

Proof that the State monad with ∀-ed state type
is unique.

-}

open import Function
  using (
    _∘_; id; const; constᵣ;
    case_of_
  )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties as ProductProp
  using ()
  renaming (
    ,-injectiveˡ to ,-injective₁;
    ,-injectiveʳ to ,-injective₂
  )
import Data.Product as Product

open import Data.Nat
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Nat.Properties as NatProp

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

module Uniqueness where

open import Definitions

private
  countFs : T -> ℕ
  countFs = foldT suc constᵣ zero

  countGs : T -> ℕ
  countGs = foldT id (λ { _ r → suc r }) zero

  -- MonadLaw can be rewritten as these eq1-eq8
  module ExpandMonadLaw {def : JoinDef} (law : MonadLaw def) where
    open JoinDef def
    open MonadLaw law

    -- From leftUnitLaw:
    eq1 : countGs t ≡ 1
    eq1 = ,-injective₁ leftUnitLaw

    eq2 : countGs r ≡ 0
    eq2 = ,-injective₂ leftUnitLaw

    -- From rightUnitLaw:
    eq3 : countFs t ≡ 1
    eq3 = ,-injective₁ rightUnitLaw

    eq4 : countFs l ≡ 0
    eq4 = ,-injective₂ rightUnitLaw

    -- From assocLaw:
    runAB : T → S → S
    runAB x s = foldT A B s x

    ΔC : S → S → S
    ΔC s₁ = C (runAB l s₁) (runAB r s₁)

    runBC : T → S → S → S
    runBC x s₁ s₂ = foldT (B s₁) (C s₁) s₂ x

    run : T → S
    run = foldT (runAB t) ΔC Leaf

    run' : T → S
    run' = foldT A (runBC t) Leaf

    fl : S
    fl = run l

    fr : S
    fr = run r

    fl' : S
    fl' = run' l

    fr' : S
    fr' = run' r

    eq5 : run t ≡ run' t
    eq5 = ,-injective₁ assocLaw

    eq6 : runAB l fl ≡ fl'
    eq6 = ,-injective₁ (,-injective₂ assocLaw)
    
    eq7 : runAB r fl ≡ runBC l fl' fr'
    eq7 = ,-injective₁ (,-injective₂ (,-injective₂ assocLaw))

    eq8 : fr ≡ runBC r fl' fr'
    eq8 = ,-injective₂ (,-injective₂ (,-injective₂ assocLaw))

  pat-F1-G1 : (t : T)
    → countFs t ≡ 1
    → countGs t ≡ 1
    → (∃ λ u → t ≡ G u (F X)) ⊎ (∃ λ u → t ≡ F (G u X))
  pat-F1-G1 (G u (F X)) _ _ = inj₁ (u , refl) 
  pat-F1-G1 (F (G u X)) _ _ = inj₂ (u , refl)

  clone : ∀ {ℓ} {A : Set ℓ} (x : A) → ∃ (x ≡_)
  clone x = x , refl

  module Law-consequences (def : JoinDef) (law : MonadLaw def) where
    open JoinDef def
    open ExpandMonadLaw law

    -- (eq1) and (eq3) implies
    --   t = G u (F X) | F (G u X)    (for some u)
    gf-or-fg : 
      (∃ λ u → t ≡ G u (F X)) ⊎ (∃ λ u → t ≡ F (G u X))
    gf-or-fg = pat-F1-G1 t eq3 eq1

    GF-case : (u : T) → t ≡ G u (F X) → def ≡ mkJoin (G X (F X)) X (F X)
    GF-case u refl = result where
      l≡X : l ≡ X
      l≡X with clone l
      ...  | X , eq = eq
      ...  | F _ , refl = case eq4 of λ ()
      ...  | G _ _ , refl = case eq6 of λ ()
      {- because:
        l = (G _)^n X from eq4 = (countFs l ≡ 0)
        n = 0 from eq6:

        lhs(eq6)
          = runAB ((G _)^n X) fl
          = (B _)^n fl
          = (B _)^n (run ((G _)^n X))
          = (B _)^n ((ΔC _)^n Leaf)
          = (B _)^n ((C _ _)^n Leaf)
        rhs(eq6)
          = fl'
          = run' l
          = foldT A (runBC t) Leaf ((G _)^n X)
          = (runBC t)^n Leaf
          = (λ s → foldT (B _) (C _) s t)^n Leaf
          = (λ s → C _ _ (B _ s))^n Leaf
      -}

      r-01 : (r ≡ X) ⊎ (r ≡ F X)
      r-01 with l≡X
      ... | refl with clone r
      ...         | X , eq = inj₁ eq
      ...         | F X , eq = inj₂ eq
      ...         | F (F _) , refl = case eq8 of λ ()
      ...         | F (G _ _) , refl = case eq2 of λ ()
      ...         | G _ _ , refl = case eq2 of λ ()
      {- because:
        r = F^n X from eq2 = (countGs r ≡ 0)
        n ≤ 1 from eq8:

        lhs(eq8)
        = fr
        = run r
        = foldT (runAB t) ΔC Leaf (F^n X)
        = (runAB t)^n Leaf
        = (λ s ­→ B _ (A s))^n Leaf
        rhs(eq8)
        = runBC (F^n X) fl' fr'
        = (B _)^n fr'
        = (B _)^n (foldT A (runBC t) Leaf (F^n X))
        = (B _)^n (A^n Leaf)
      -}

      -- u ≡ X from eq5:
      {-
      
      lhs(eq5)
      = run t
      = run (G u (F X))
      = ΔC (run u) (runAB t Leaf)
        (let fu₁ = run u)
      = ΔC fu₁ (runAB t Leaf)
      = C (runAB l fu₁) (runAB r fu₁) (runAB t Leaf)
      = C fu₁ (A^n fu₁) (runAB t Leaf)
        (where n ∈ {0, 1} such that r = F^n X)
      rhs(eq5)
      = run' t
      = run' (G u (F X))
      = runBC t (run' u) (A Leaf)
        (let fu₂ = run' u)
      = foldT (B fu₂) (C fu₂) (A Leaf) t
      = foldT (B fu₂) (C fu₂) (A Leaf) (G u (F X))
      = C fu₂ (runBC u fu₂ (A Leaf)) (B fu₂ (A Leaf))
      = C fu₂ (foldT (B fu₂) (C fu₂) (A Leaf) u) (B fu₂ (A Leaf))
      
      therefore:
        fu₁ ≡ fu₂ --- (*)
        A^n fu₁ ≡ foldT (B fu₂) (C fu₂) (A Leaf) u --- (**)
      
      Case analysis on n:
      - Case n ≡ 1

        (**) ⇒ (A fu₁ ≡ foldT (B fu₂) (C fu₂) (A Leaf) u),
        which is satisfied only when u = X.

      - Case n ≡ 0

        (**) ⇒ fu₁ ≡ foldT (B fu₂) (C fu₂) (A Leaf) u

        Any u contradicts (*): fu₁ = fu₂
          
        - Case u = X

          fu₁ = Leaf
          fu₂ = A Leaf

        - Case u = F _

          fu₁
          = foldT (B fu₂) (C fu₂) (A Leaf) (F _)
          = B fu₂ _
          
        - Case u = G _ _

          fu₁
          = foldT (B fu₂) (C fu₂) (A Leaf) (F _)
          = C fu₂ _ _
      
      Each contradictory cases can be "automatically" eliminated
      by having Agda check that (eq5) reduces to an
      impossible equation (distinct constructor or
      "occurs check" failure)

      -}

      result : def ≡ mkJoin (G X (F X)) X (F X)
      result with l≡X | r-01
      result  | refl  | inj₁ refl
                with clone u
      ...         | X , refl = case eq5 of λ ()
      ...         | F _ , refl = case eq5 of λ ()
      ...         | G _ _ , refl = case eq5 of λ ()
      result  | refl  | inj₂ refl
                with clone u
      ...         | X , refl = refl
      ...         | F _ , refl = case eq5 of λ ()
      ...         | G _ _ , refl = case eq5 of λ ()

    FG-case : (u : T) → t ≡ F (G u X)
      → ∃ λ k → def ≡ mkJoin (F (G u X)) (G k X) X
    FG-case u refl = result where
      -- Using arguments parallel to GF-case:
      r≡X : r ≡ X
      r≡X with clone r
      ...  | X , eq = eq
      ...  | F _ , refl = case eq8 of λ ()
      ...  | G _ _ , refl = case eq2 of λ ()

      l-01 : (l ≡ X) ⊎ (∃ λ l′ → l ≡ G l′ X)
      l-01 with r≡X
      ... | refl with clone l
      ...         | X , eq = inj₁ eq
      ...         | F _ , refl = case eq4 of λ ()
      ...         | G l′ X , eq = inj₂ (l′ , eq)
      ...         | G _ (G _ _) , refl = case eq6 of λ ()
      ...         | G _ (F _) , refl = case eq4 of λ ()

      -- l also can't be X with similar argument to GF-case,
      -- but the other case is hard -- so it's handled later
      result : ∃ λ k → def ≡ mkJoin (F (G u X)) (G k X) X
      result with r≡X | l-01
      result  | refl  | inj₁ refl
            with clone u
      ...         | X , refl = case eq5 of λ ()
      ...         | F _ , refl = case eq5 of λ ()
      ...         | G _ _ , refl = case eq5 of λ ()
      result | refl  | inj₂ (l′ , refl) = l′ , refl

    -- Utilities
    module left-depth where
      -- Left depth of tree S
      depth : S → ℕ
      depth = foldS suc (λ x _ → suc x) (λ x _ _ → suc x) zero

      -- Left depth of tree T
      depthT : T → ℕ
      depthT = foldT suc (λ x _ → suc x) zero

      depth-runAB : ∀ (t : T) (s : S) →
        depth (runAB t s) ≡ depthT t + depth s
      depth-runAB (F t) s = cong suc (depth-runAB t s)
      depth-runAB (G t _) s = cong suc (depth-runAB t s)
      depth-runAB X s = refl

    FG-GX-X-case : ∀(u k : T) → def ≡ mkJoin (F (G u X)) (G k X) X → ⊥
    FG-GX-X-case u k refl = contradiction
      where
        open left-depth
        fk : S
        fk = run k

        fk' : S
        fk' = run' k
        
        -- eq7
        _ : C (B (runAB k fk) fk) fk Leaf
            ≡
            C fl' (runBC k fl' fr') Leaf
        _ = eq7

        {-
        fl' = run' l
        = run' (G k X)
        = runBC t (run' k) (run' X)
        = runBC t fk' Leaf
        = foldT (B fk') (C fk') Leaf t
        = foldT (B fk') (C fk') Leaf (F (G u X))
        = B fk' (C fk' (runBC u fk' Leaf) Leaf)
        -}
        _ : fl' ≡ B fk' (C fk' (runBC u fk' Leaf) Leaf)
        _ = refl

        eq7-1 : B (runAB k fk) fk ≡ fl'
        eq7-1 = C-injective₁ eq7

        eq7-1-1 : runAB k fk ≡ fk'
        eq7-1-1 = B-injective₁ eq7-1
        
        eq7-1-2 : fk ≡ C fk' (runBC u fk' Leaf) Leaf
        eq7-1-2 = B-injective₂ eq7-1

        infinite-depth : depth fk ≡ 1 + depthT k + depth fk
        infinite-depth =
          begin
            depth fk
          ≡⟨ cong depth eq7-1-2 ⟩
            1 + depth fk'
          ≡⟨ cong suc (cong depth eq7-1-1) ⟨
            1 + depth (runAB k fk)
          ≡⟨ cong suc (depth-runAB k fk) ⟩
            1 + depthT k + depth fk
          ∎
        
        m<1+n+m : ∀ (m n : ℕ) → m < 1 + n + m
        m<1+n+m m n = s≤s (NatProp.m≤n+m m n)
        -- Note:
        --   - (x < y) is defined as (1 + x ≤ 1 + y)
        --   - s≤s : ∀ x y → x ≤ y → suc x ≤ suc y 

        contradiction : ⊥
        contradiction = NatProp.<-irrefl infinite-depth (m<1+n+m (depth fk) (depthT k))

    uniqueness : def ≡ UsualStateMonad.def
    uniqueness = case gf-or-fg of λ {
        (inj₁ (u , eq)) → GF-case u eq;
        (inj₂ (u , eq-t)) → case FG-case u eq-t of λ {
          (l′ , eq-tlr) → ⊥-elim (FG-GX-X-case u l′ eq-tlr)
        }
      }

open Law-consequences using (uniqueness)
