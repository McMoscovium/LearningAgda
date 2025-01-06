{-# OPTIONS --exact-split #-}

module LearningAgda.part1.Naturals where


data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


seven : ℕ
seven = suc(suc(suc(suc(suc(suc(suc zero))))))




{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ (suc m )= n * (n ^ m)




_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
  begin
    5 ∸ 3 
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎
