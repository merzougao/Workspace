{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT where
open import Agda.Primitive

-- Universes --
---------------
𝓤₀ : Set (lsuc lzero)
𝓤₀ = Set lzero

𝓤₁ : Set (lsuc (lsuc lzero))
𝓤₁ = Set (lsuc lzero)

-- Basic Types --
-----------------

data 𝟘 : 𝓤₀ where

data 𝟙 : 𝓤₀ where
    ✭ : 𝟙

𝟙-induction : ∀ {n} {A : 𝟙 → Set n}
            → A ✭
            → ((x : 𝟙) → A x)
𝟙-induction a ✭ = a 

-- Negation --
--------------
¬ : ∀ {n} → Set n → Set n
¬ A = A → 𝟘


-- Natural Numbers --
---------------------
data ℕ : 𝓤₀ where
  zero : ℕ
  succ : ℕ → ℕ
 
{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : ∀ {n} {A : ℕ → Set n} 
            → A zero 
            → ((n : ℕ) → A n → A (succ n))
            → ((n : ℕ) →  A n)
ℕ-induction a₀ f  zero      = a₀ 
ℕ-induction a₀ f  (succ n)  = f n (ℕ-induction a₀ f n) 

-- Coproducts ------
--------------------
data _+_ {n m : Level} (X : Set n) (Y : Set m) : Set (n ⊔ m) where
    inl : X → X + Y
    inr : Y → X + Y

+-induction : ∀ {n m} {X : Set n} {Y : Set m} {A : X + Y → Set (n ⊔ m)}
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → ((z : X + Y) → A z)
+-induction f g (inl x) = f x
+-induction f g (inr y) = g y

-- Dependent sum ---
--------------------
data Σ {n m : Level } {X : Set n} (Y : X → Set m) : Set (n ⊔ m) where
    _,_ : (x : X) → Y x → Σ Y

proj₁ : ∀ {n m} {X : Set n} {Y : X → Set m} → Σ Y → X
proj₁ (x , y) = x

proj₂ : ∀ {n m} {X : Set n} {Y : X → Set m} → (z : Σ Y) → Y (proj₁ z)
proj₂ (x , y) = y

Σ-induction : ∀ {n m r} {X : Set n} {Y : X → Set m} {A : Σ Y → Set r} 
            → ((x : X) → (y : Y x) → A (x , y))
            → ((z : Σ Y) → A z)
Σ-induction f (x , y) = f x y

_×_ : ∀ {n m} → Set n → Set m → Set (n ⊔ m)
X × Y = Σ (λ (x : X) → Y)

-- Dependent functions --
-------------------------
Π  : ∀ {n m} {X : Set n} (Y : X → Set m) → Set (n ⊔ m)
Π {n} {m} {X} Y = (x : X) → Y x

dom : ∀ {n m} {X : Set n} {Y : Set m} → (X → Y) → Set n
dom {n} {m} {X} {Y} f = X

rng : ∀ {n m} {X : Set n} {Y : Set m} → (X → Y) → Set m
rng {n} {m} {X} {Y} f = Y

-- Identity Types --
--------------------

data Id {n : Level} (X : Set n) : X → X → Set n where
    refl : (x : X) → Id X x x

_≡_ : ∀ {n} {X : Set n} → X → X → Set n
x ≡ y = Id _ x y 

≡-induction : ∀ {n m} {X : Set n} {A : (x y : X) → (x ≡ y) → Set m} 
            → ((x : X) → A x x (refl x))
            → ((x y : X) → (p : x ≡ y) → A x y p)
≡-induction f x x (refl x) = f x

-- left and Right hand side of a path p : x ≡ y --
lhs : ∀ {n} {X : Set n} { x y : X} →  x ≡ y → X
lhs {n} {X} {x} {y} p = x

rhs : ∀ {n} {X : Set n} { x y : X} →  x ≡ y → X
rhs {n} {X} {x} {y} p = y

-- Homotopy theory --
---------------------

transport : ∀ {n m} {X : Set n} {A : X → Set m} {x y : X} 
            → x ≡ y 
            → (A x → A y)
transport {n} {m} {X} {A} p = ≡-induction (λ x → ( λ (y : A x) → y)) (lhs p) (rhs p) p
--transport (refl x) = λ y → y

concat  : ∀ {n} {X : Set n} 
        → (x y : X) 
        → x ≡ y 
        → ((z : X) →  (y ≡ z) → (x ≡ z))
        
concat = ≡-induction λ x → λ z → λ p → p
--concat x x (refl x) = λ z → λ p → p

-- Inversion of paths --
_⁻¹ : ∀ {n} {X : Set n} {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = ≡-induction (λ x → (refl x)) (lhs p) (rhs p) p

-- Functions are functors --
ap : ∀ {n m} {X : Set n} {Y : Set m}  → (f : X → Y) {x y : X} →  x ≡ y → (f x ≡ f y)
ap f p = ≡-induction (λ x → (refl ( f x))) (lhs p) (rhs p) p

-- Homotopy between functions --
_~_ : ∀ {n m} {X : Set n} {A : X → Set m}
    → ((x : X) → A x) 
    → ((x : X) → A x)
    → Set (n ⊔ m)
f ~ g = ∀ x → f x ≡ g x

-- Operation on double negation --
¬¬ : ∀ {n} → (X : Set n) → Set n
¬¬ X = ¬ (¬ X)

dni : ∀ {n} → {X : Set n} → X → ¬¬ X
dni {n} {X} x = λ (f : ¬ X) → f x 

_≢_ : ∀ {n} {X : Set n} → (x y : X) → Set n
x ≢ y = ¬ (x ≡ y)


