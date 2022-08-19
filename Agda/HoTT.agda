{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT where
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
        → (X → Y) → (Y → Z) → (X → Z)
f ∘ g = λ x → g ( f x)

Id_fun : ∀ {n} {X : Set n} → X → X
Id_fun x = x

dom :   ∀ {n m} {X : Set n} {Y : Set m}
        → (X → Y) → Set n
dom {n} {m} {X} {Y} f = X

rng :   ∀ {n m} {X : Set n} {Y : Set m}
        → (X → Y) → Set m
rng {n} {m} {X} {Y} f = Y

-- Basic Types --
-----------------

data 𝟘 : 𝓤₀ where

𝟘-induction : ∀ {n} {A : 𝟘 → Set n}
            → ((x : 𝟘) → A x)
𝟘-induction ()

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

-Σ : ∀ {n m} →  (X : Set n) (Y : X → Set m) → Set (n ⊔ m)
-Σ X Y = Σ Y

syntax -Σ X (λ x → Y) = Σ x ∶ X , Y 

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

_≢_ : ∀ {n} {X : Set n} → (x y : X) → Set n
x ≢ y = ¬ (x ≡ y)

-- left and Right hand side of a path p : x ≡ y --
lhs : ∀ {n} {X : Set n} { x y : X} →  x ≡ y → X
lhs {n} {X} {x} {y} p = x

rhs : ∀ {n} {X : Set n} { x y : X} →  x ≡ y → X
rhs {n} {X} {x} {y} p = y

-- Homotopy theory --
---------------------


-- Inversion of paths --
≡-inv : (n : Level) → (X : Set n) → (x y : X) → x ≡ y → y ≡ x
≡-inv = λ n X x y p → ≡-induction (λ s → (refl s)) x y p

-- Convenience function --
_⁻¹ : ∀ {n} {X : Set n} {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = ≡-inv (level-of p) (type-of (lhs p)) (lhs p) (rhs p) p


-- Concatenation of paths --
≡-concat  : (n : Level) → (X : Set n) 
        → (x y : X) 
        → x ≡ y 
        → ((z : X) →  (y ≡ z) → (x ≡ z))
        
≡-concat = λ n X x y p → ≡-induction {n} {n} {X} {A X} (λ r → λ s → λ t → t) x y p
    where
        A : ∀ {n} → (X : Set n) → (x y : X) → (p : x ≡ y) →  Set n
        A X x y p = (z : X) → (y ≡ z) → (x ≡ z)

-- Convenience function --
_∙_ : ∀ {n} {X : Set n} {x y z : X}
    → (p : x ≡ y)
    → (q : y ≡ z)
    → x ≡ z
p ∙ q = ≡-concat  (level-of p) 
                (type-of (lhs p))
                (lhs p)
                (rhs p)
                p
                (rhs q)
                q

-- Functions are functors --
ap : ∀ {n m} {X : Set n} {Y : Set m}  → (f : X → Y) {x y : X} →  x ≡ y → (f x ≡ f y)
ap f p = ≡-induction (λ x → (refl ( f x))) (lhs p) (rhs p) p

-- Transport of paths --
≡-transport : (n m : Level) 
            → (X : Set n) 
            → (A : X → Set m) 
            → (x y : X) → x ≡ y 
            → (A x → A y)
≡-transport = λ n m X A x y p → ≡-induction (λ x → ( λ (y : A x) → y)) x y p


-- Homotopy between functions --
_~_ : ∀ {n m} {X : Set n} {A : X → Set m}
    → ((x : X) → A x) 
    → ((x : X) → A x)
    → Set (n ⊔ m)
f ~ g = ∀ x → f x ≡ g x


-- Contractibility --
is_contr : ∀ {n} → Set n → Set n
is_contr X = Σ x ∶ X , ((y : X) → x ≡ y)


-- Mere Propositions --
is_prop : ∀ {n} → Set n → Set n
is_prop X = (x y : X) → x ≡ y


-- Sets --
is_set : ∀ {n} → Set n → Set n
is_set X = (x y : X) → (p q : x ≡ y) → p ≡ q

-- Equivalences --
------------------

is_equiv :  ∀ {n m} {X : Set n} {Y : Set m} 
            → (X → Y) → Set (n ⊔ m)
is_equiv f = Σ g ∶ ((rng f) → (dom f)) , (((f ∘ g) ~ Id_fun) × ((g ∘ f) ~ Id_fun))
