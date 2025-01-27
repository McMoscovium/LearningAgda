module LearningAgda.part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  -------
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ----------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 step-≡-| step-≡-⟩
  infix 3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  step-≡-| : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-| x x≡y = x≡y

  step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y = trans x≡y y≡z

  syntax step-≡-| x x≡y = x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

_≡⟨_⟩′_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩′ y≡z = trans x≡y y≡z

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z = 
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero 
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev rewrite +-comm n m = ev

--rewriteを使った証明の例
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n
  rewrite
  +-identity n
  = refl
+-comm′ (suc m) n
  rewrite
  +-suc n m |
  +-comm′ m n
  = refl

--withを使った証明の例
even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with m + n | +-comm m n
... | .(n + m) | refl = ev

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    ------
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
  Q : A → Set
  Q z = P z → P x
  Qx : Q x
  Qx = refl-≐ P
  Qy : Q y
  Qy = x≐y Q Qx

-- "≐" はLeipniz equalityと呼ばれる。
-- 以下で、Martin Loef equality ≡ とLeipniz equalityの同値性を示す。

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
  → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
  Q : A → Set
  Q z = x ≡ z
  Qx : Q x
  Qx = refl
  Qy : Q y
  Qy = x≐y Q Qx


-- 型の型Setにレベルを導入し、universal polymorphismを用いて任意のレベルのSetにおけるequalityを定義してみる

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
-- _⊔_で、大きい方のレベルをもつSetₗを返す

-- 任意のレベルのSetにおけるequalityを定義してみる
data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

-- universal polymorphismを用いた対称律
sym′ : ∀ {ℓ : Level} {A : Set} {x y : A}
  → x ≡′ y
  → y ≡′ x
sym′ refl′ = refl′ 

-- universal polymorphismを用いたLeipniz equality
_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

-- universal polymorphismを用いて関数の合成が定義できる。
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)