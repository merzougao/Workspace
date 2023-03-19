module Foundations.Type_Theory where
open import Agda.Primitive

-- Universes --
---------------
𝓤₀ : Set (lsuc lzero)
𝓤₀ = Set lzero

𝓤₁ : Set (lsuc (lsuc lzero))
𝓤₁ = Set (lsuc lzero)

-- Misc --
-------------
level-of : ∀ {n} {X : Set n} → X → Level
level-of {n} {X} x = n

type-of : ∀ {n} {X : Set n} → X → Set n
type-of {n} {X} x = X

_∘_ :   ∀ {n m k} {X : Set n} {Y : Set m} {Z : Set k}
        → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g ( f x)

id : ∀ {n} {X : Set n} → X → X
id x = x

dom :   ∀ {n m} {X : Set n} {Y : Set m}
        → (X → Y) → Set n
dom {n} {m} {X} {Y} f = X

rng :   ∀ {n m} {X : Set n} {Y : Set m}
        → (X → Y) → Set m
rng {n} {m} {X} {Y} f = Y


-- Dependent functions type --
------------------------------

∏ : ∀ {n m} → (A : Set n) → (B : A → Set m) → Set (n ⊔ m)
∏ A B = (a : A) → B a
syntax ∏ A (λ a → b) = ∏ a ∶ A , b


-- Product types --
-------------------

data _×_ {n m : Level} (X : Set n) (Y : Set m) : Set (n ⊔ m) where
    _,_ : X → Y → X × Y

infixr 20 _×_

-- Induction Principle --
×-ind : ∀ {n m k} {A : Set n} {B : Set m} {P : A × B → Set k}
        → ((a : A) → (b : B) → P (a , b))
        → ((z : A × B) →  P z)
×-ind f (a , b) = f a b

-- Recursion Principle --
×-rec : ∀ {n m k} {A : Set n} {B : Set m} {P : Set k}
    → (A → B → P)
    → ((z : A × B) → P)
×-rec {P = P} = ×-ind {P = (λ z → P)}

data 𝟙 : 𝓤₀ where
    ✭ : 𝟙
𝟙-ind : ∀ {n} {P : 𝟙 → Set n}
        → (P ✭)
        → ((z : 𝟙) → P z)
𝟙-ind s ✭ = s

𝟙-rec : ∀ {n} {P : Set n}
        → P
        → ((z : 𝟙) → P)
𝟙-rec {n} {P} = 𝟙-ind{n} {λ z → P}

-- Projections --
×p₁ : ∀ {n m} {A : Set n} {B : Set m} → A × B → A
×p₂ : ∀ {n m} {A : Set n} {B : Set m} → A × B → B
×p₁ z = ×-rec (λ a b → a) z
×p₂ z = ×-rec (λ a b → b) z

-- Dependent Pair Types --
--------------------------

data Σ {n m : Level } {X : Set n} (Y : X → Set m) : Set (n ⊔ m) where
    _,_ : (x : X) → Y x → Σ Y

-Σ : ∀ {n m} →  (X : Set n) (Y : X → Set m) → Set (n ⊔ m)
-Σ X Y = Σ Y

syntax -Σ X (λ x → Y) = Σ x ∶ X , Y 

-- Induction Principle --
Σ-ind : ∀ {n m k} {A : Set n} {B : A → Set m} {P : Σ B → Set k}
        → ((a : A) → (b : B a) → P (a , b))
        → (z : Σ B) → P z
Σ-ind f (a , b) = f a b

-- Recursion Principle --
Σ-rec : ∀ {n m k} {A : Set n} {B : A → Set m} {P : Set k}
        → ((a : A) → (b : B a) → P)
        → (z : Σ B) → P
Σ-rec {P = P} = Σ-ind {P = (λ z → P)}

-- Coproducts types --
----------------------

data _+_ {n m : Level} (A : Set n) (B : Set m) : Set (n ⊔ m) where
    inl : A → A + B
    inr : B → A + B

+-ind : ∀ {n m k} {A : Set n} {B : Set m} {P : A + B → Set k}
        → ((a : A) → P (inl a))
        → ((b : B) → P (inr b))
        → (z : A + B) → P z
+-ind f g (inl a) = f a
+-ind f g (inr b) = g b

+-rec : ∀ {n m k} {A : Set n} {B : Set m} {P : Set k}
        → ((a : A) → P)
        → ((b : B) → P)
        → (z : A + B) → P
+-rec {P = P} = +-ind {P = λ z → P} 

data 𝟘 : 𝓤₀ where

𝟘-ind : ∀ {n} {P : 𝟘 → Set n}
        → (z : 𝟘) → P z
𝟘-ind ()

𝟘-rec : ∀ {n} {P : Set n}
        → (z : 𝟘) → P
𝟘-rec {P = P} = 𝟘-ind {P = λ z → P}

-- Boolean --
-------------

data 𝟚 : 𝓤₀ where
    t₂ : 𝟚
    f₂ : 𝟚

-- Induction Principle--
𝟚-ind : ∀ {n} {P : 𝟚 → Set n}
        → (P t₂)
        → (P f₂)
        → (z : 𝟚) → P z
𝟚-ind p₁ p₂ t₂ = p₁
𝟚-ind p₁ p₂ f₂ = p₂

𝟚-rec : ∀ {n} {P : Set n}
        → P
        → P 
        → (z : 𝟚) → P
𝟚-rec {P = P} = 𝟚-ind {P = λ z → P}

-- Natural Numbers --
---------------------

data ℕ : 𝓤₀ where
    0ₙ      : ℕ
    succ    : ℕ → ℕ

ℕ-ind : ∀ {n} {P : ℕ → Set n}
        → P 0ₙ
        → ((n : ℕ) →  P n → P (succ n))
        → (n : ℕ) → P n
ℕ-ind p₀ pₙ 0ₙ = p₀ 
ℕ-ind p₀ pₙ (succ n) = pₙ n (ℕ-ind p₀ pₙ n)

ℕ-rec : ∀ {n} {P : Set n}
        → P 
        → ((n : ℕ) →  P → P )
        → (n : ℕ) → P
ℕ-rec {P = P} = ℕ-ind {P = λ z → P} 


-- Identity types --
--------------------

data _≡_ {n : Level } {A : Set n} : A → A → Set n where
    refl : (a : A) → a ≡ a

≡-ind : ∀ {n m} {A : Set n} {P : (a b : A) → (a ≡ b) → Set m}
        → ((a : A) → P a a (refl a))
        → ((a b : A) → (p : a ≡ b) → P a b p)
≡-ind f a a (refl a) = f a

-- Helpers --
src : ∀ {n} {A : Set n} {a b : A} →  a ≡ b → A
src {a = a} p = a

dst : ∀ {n} {A : Set n} {a b : A} →  a ≡ b → A
dst {b = b} p = b

-- Negation and disequality --
------------------------------

¬ : ∀ {n} (A : Set n) → Set n
¬ A = A → 𝟘

_≢_ : ∀ {n} {A : Set n} → (a b : A) → Set n 
a ≢ b = ¬ (a ≡ b)
