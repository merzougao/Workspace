{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT where
open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣  : Universe

data 𝟘 : 𝓤₀ ̇ where

data 𝟙 : 𝓤₀ ̇ where
    ✭ : 𝟙

𝟙-induction : {A : 𝟙 → 𝓤 ̇}
            → A ✭
            → ((x : 𝟙) → A x)
𝟙-induction a ✭ = a 

¬ : 𝓤 ̇ → 𝓤 ̇
¬ A = A → 𝟘

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

data _+_ (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
    inl : X → X + Y
    inr : Y → X + Y

+-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : X + Y → 𝓦 ̇}
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → ((z : X + Y) → A z)
+-induction f g (inl x) = f x
+-induction f g (inr y) = g y

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

Π  : {X : 𝓤 ̇} (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇ 
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

