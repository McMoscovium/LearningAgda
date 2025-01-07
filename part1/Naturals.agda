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
suc m + n = suc (m + n)

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


infixl 6 _+_ _∸_
infixl 7 _*_

infixr 20 _^_

n : ℕ
n = _+_ 2 3
p : n ≡ 5
p = refl


{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ O
inc (x O) = x I
inc (x I) = inc (x) O

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

