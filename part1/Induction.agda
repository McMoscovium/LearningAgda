module LearningAgda.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ)→(m + n)+ p ≡ m +(n + p) 
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) =
  begin
    m + (suc n) ≡⟨ +-suc m n ⟩
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q) ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl


+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p 
  rewrite
    +-comm′ m (n + p) |
    +-assoc′ n p m |
    +-comm′ m p
  = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p 
  rewrite *-distrib-+ m n p |
    +-assoc′ p (m * p) (n * p)
  = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite
    *-distrib-+ n (m * n) p |
    *-assoc m n p
  = refl

*-identity : ∀ (n : ℕ) → 1 * n ≡ n
*-identity n = +-identity′ n

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n
  rewrite
    *-suc m n |
    +-swap n m (m * n)
  = refl

*-zero : ∀ (n : ℕ) → n * 0 ≡ 0
*-zero zero = refl
*-zero (suc n) = *-zero n

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n
  rewrite
    *-zero n
  = refl
*-comm (suc m) n
  rewrite
    *-suc n m |
    *-comm n m
  = refl

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p
  rewrite
    *-comm m (n * p) |
    *-assoc n p m |
    *-comm p m
  = refl

∸-zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-zero zero = refl
∸-zero (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p
  rewrite
    ∸-zero n |
    ∸-zero p |
    ∸-zero (n + p)
  = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

^-distribˡ+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ+-* m zero p
  rewrite
    +-identity′ (m ^ p)
  = refl
^-distribˡ+-* m (suc n) p
  rewrite
    ^-distribˡ+-* m n p |
    *-assoc m (m ^ n) (m ^ p)
  = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite
    ^-distribʳ-* m n p |
    *-assoc m n (m ^ p * n ^ p) |
    *-swap n (m ^ p) (n ^ p) |
    *-assoc m (m ^ p) (n * n ^ p)
  = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero
  rewrite *-zero n
  = refl
^-*-assoc m n (suc p)
  rewrite
    *-suc n p |
    ^-*-assoc m n p |
    ^-distribˡ+-* m n (n * p)
  = refl
