{-# OPTIONS --without-K --safe #-}
module ListLemma where

open import Function using (_∘_; id; const; constᵣ; case_of_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties
  using (,-injective)

open import Data.Nat
open import Data.List
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
import Data.List.Properties as ListProp
import Data.Nat.Properties as NatProp

import Relation.Binary.PropositionalEquality as Eq
open Eq
  renaming ([_] to sing)
open Eq.≡-Reasoning

private
  variable
    α : Set
    β : Set

-- Nat properties

iterate : ℕ → (α → α) → α → α
iterate zero _ x = x
iterate (suc n) f x = f (iterate n f x)

n≯1→0or1 : ∀{n : ℕ} → n ≯ 1 → n ≡ 0 ⊎ n ≡ 1
n≯1→0or1 {n = zero} _ = inj₁ refl
n≯1→0or1 {n = suc zero} _ = inj₂ refl
n≯1→0or1 {n = suc (suc n)} n≯1 = ⊥-elim (n≯1 (s≤s NatProp.0<1+n))

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
 