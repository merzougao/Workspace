{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT where
open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣  : Universe

-- Type of an element --
type-of : {X : 𝓤 ̇} →  X → 𝓤 ̇
type-of {𝓤} {X} x = X

-- Basic Types --
-----------------

data 𝟘 : 𝓤₀ ̇ where

data 𝟙 : 𝓤₀ ̇ where
    ✭ : 𝟙

𝟙-induction : {A : 𝟙 → 𝓤 ̇}
            → A ✭
            → ((x : 𝟙) → A x)
𝟙-induction a ✭ = a 

-- Negation --
--------------
¬ : 𝓤 ̇ → 𝓤 ̇
¬ A = A → 𝟘


-- Natural Numbers --
---------------------
data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ
 
{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : {A : ℕ → 𝓤 ̇} 
            → A zero 
            → ((n : ℕ) → A n → A (succ n))
            → ((n : ℕ) →  A n)
ℕ-induction a₀ f  zero      = a₀ 
ℕ-induction a₀ f  (succ n)  = f n (ℕ-induction a₀ f n) 

-- Coproducts ------
--------------------
data _+_ (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
    inl : X → X + Y
    inr : Y → X + Y

+-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : X + Y → 𝓦 ̇}
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → ((z : X + Y) → A z)
+-induction f g (inl x) = f x
+-induction f g (inr y) = g y

-- Dependent sum ---
--------------------
data Σ {X : 𝓤 ̇} (Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
    _,_ : (x : X) → Y x → Σ Y

proj₁ :{X : 𝓤 ̇} {Y : X → 𝓥 ̇} → Σ Y → X
proj₁ (x , y) = x

proj₂ :{X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (z : Σ Y) → Y (proj₁ z)
proj₂ (x , y) = y

Σ-induction : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦  ̇} 
            → ((x : X) → (y : Y x) → A (x , y))
            → ((z : Σ Y) → A z)
Σ-induction f (x , y) = f x y

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ (λ (x : X) → Y)

-- Dependent functions --
-------------------------
Π  : {X : 𝓤 ̇} (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇ 
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

dom : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
dom {𝓤} {𝓥} {X} {Y} f = X

rng : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
rng {𝓤} {𝓥} {X} {Y} f = Y

-- Identity Types --
--------------------

data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇ where
    refl : (x : X) → Id X x x

_≡_ : {X : 𝓤  ̇} → X → X → 𝓤  ̇
x ≡ y = Id _ x y 

≡-induction : {X : 𝓤 ̇} {A : (x y : X) → (x ≡ y) → 𝓥 ̇} 
            → ((x : X) → A x x (refl x))
            → ((x y : X) → (p : x ≡ y) → A x y p)
≡-induction f x x (refl x) = f x

-- left and Right hand side of a path p : x ≡ y --
lhs : {X : 𝓤 ̇} { x y : X} →  x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇} { x y : X} →  x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y

-- Homotopy theory --
---------------------

transport : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x y : X} 
            → x ≡ y 
            → (A x → A y)
transport A p = ≡-induction (λ x → ( λ (y : A x) → y)) (lhs p) (rhs p) p
--transport (refl x) = λ y → y

concat  : {X : 𝓤 ̇} 
        → (x y : X) 
        → x ≡ y 
        → ((z : X) →  (y ≡ z) → (x ≡ z))
        
concat = ≡-induction λ x → λ z → λ p → p
--concat x x (refl x) = λ z → λ p → p

-- Inversion of paths --
_⁻¹ : {X : 𝓤 ̇} {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = ≡-induction (λ x → (refl x)) (lhs p) (rhs p) p

-- Functions are functors --
ap : {X : 𝓤 ̇} {Y : 𝓥 ̇}  → (f : X → Y) {x y : X} →  x ≡ y → (f x ≡ f y)
ap f p = ≡-induction (λ x → (refl ( f x))) (lhs p) (rhs p) p


