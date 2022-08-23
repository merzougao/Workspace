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
        → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g ( f x)

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

-- Products --
--------------
data _×_ {n m : Level} (X : Set n) (Y : Set m) : Set (n ⊔ m) where
    _,_ : (x : X) → (y : Y) → X × Y

×-induction : ∀ {n m k} {X : Set n} {Y : Set m} {A : X × Y → Set k}
            → ((x : X) → (y : Y) → A (x , y))
            → ((z : X × Y) → A z)
×-induction f (a , b) = f a b

×pr₁ : ∀ {n m} {X : Set n} {Y : Set m} → X × Y → X
×pr₁ = λ z → ×-induction (λ x y → x) z

×pr₂ : ∀ {n m} {X : Set n} {Y : Set m} → X × Y → Y
×pr₂ = λ z → ×-induction (λ x y → y) z

-- Dependent sum ---
--------------------
data Σ {n m : Level } {X : Set n} (Y : X → Set m) : Set (n ⊔ m) where
    _,_ : (x : X) → Y x → Σ Y

-Σ : ∀ {n m} →  (X : Set n) (Y : X → Set m) → Set (n ⊔ m)
-Σ X Y = Σ Y

syntax -Σ X (λ x → Y) = Σ x ∶ X , Y 

pr₁ : ∀ {n m} {X : Set n} {Y : X → Set m} → Σ Y → X
pr₁ (x , y) = x

pr₂ : ∀ {n m} {X : Set n} {Y : X → Set m} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

Σ-induction : ∀ {n m r} {X : Set n} {Y : X → Set m} {A : Σ Y → Set r} 
            → ((x : X) → (y : Y x) → A (x , y))
            → ((z : Σ Y) → A z)
Σ-induction f (x , y) = f x y

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

apf : ∀ {n m} {X : Set n} {Y : Set m} {f g : X → Y} → (f ≡ g) → ((x y : X) → (x ≡ y) → (f x ≡ g y)) 
apf {n} {m} {X} {Y} {f} {g} p = ≡-induction (λ (f : X → Y) → (λ x y q → (ap {n} {m} f {x} {y} q))) f g p

-- Transport of paths --
≡-transport : (n m : Level) 
            → (X : Set n) 
            → (A : X → Set m) 
            → (x y : X) → x ≡ y 
            → (A x → A y)
≡-transport = λ n m X A x y p → ≡-induction (λ x → ( λ (y : A x) → y)) x y p


-- Homotopy between functions --
ℍ : (n m : Level) 
    → (X : Set n)
    → (A : X → Set m)
    → ((x : X) → A x) 
    → ((x : X) → A x)
    → Set (n ⊔ m)
ℍ n m X A f g = ∀ x → f x ≡ g x

-- Convenience function --
_∼_ : ∀ {n m} {X : Set n} {A : X → Set m}
    → ((x : X) → A x) 
    → ((x : X) → A x)
    → Set (n ⊔ m)
f ∼ g = ∀ x → f x ≡ g x

ℍ_Id_fun : ∀ {n} {X : Set n} → Id_fun ∼ Id_fun
ℍ_Id_fun {n} {X} = λ (x : X) → refl x



-- Equivalences --
------------------

is_equiv :  ∀ {n m} {X : Set n} {Y : Set m} 
            → (X → Y) → Set (n ⊔ m)
is_equiv f = Σ g ∶ (rng(f) → dom(f)) , (((f ∘ g) ∼ Id_fun) × ((g ∘ f) ∼ Id_fun))

Id_is_equiv : ∀ {n} {X : Set n} → is_equiv (Id_fun {n} {X})
Id_is_equiv = (Id_fun , (ℍ_Id_fun , ℍ_Id_fun))

_≃_ : ∀ {n m} → (X : Set n) → (Y : Set m) → Set (n ⊔ m)
X ≃ Y = Σ f ∶ (X → Y) , is_equiv(f)

self_eq : ∀ {n} → {X : Set n} → X ≃ X
self_eq = (Id_fun , Id_is_equiv)

idtoeqv : (n : Level) → (X : Set n) →  (Y : Set n) → X ≡ Y → X ≃ Y
idtoeqv n X Y p = ≡-induction {lsuc n} {n} {Set n} {λ R S q → R ≃ S} (λ X → self_eq) X Y p 

-- Contractible fibers --

fib : ∀ {n m} {X : Set n} {Y : Set m} 
    → (f : X → Y) → (y : Y) → Set (n ⊔ m)
fib {n} {m} {X} {Y} f y = Σ x ∶ X , (f(x) ≡ y)


-- Universal properties --
--------------------------

×-univ  : ∀ {n} {X A B : Set n} 
        → (X → A × B) → (X → A) × (X → B)
×-univ {n} {X} {A} {B} f = ((λ x → ×pr₁ (f x)) , (λ x → ×pr₂ (f x)))

-- Weak Axiom of choice --
weak_choice : ∀ {n m k} {X : Set n} {A : X → Set m} {P : (x : X) → A x → Set k} 
            → ((x : X) → (Σ a ∶ (A x) , (P x a))) 
            → (Σ g ∶ ((x : X) → A x) , ((x : X) → P x (g x)))
weak_choice = λ f → ((λ x → pr₁ (f x)) , λ x → pr₂ (f x))

-- Pullbacks --
pullback  : ∀ {n m k} {A : Set n} {B : Set m} {C : Set k}
        → (A → C) → (B → C) →  Set (n ⊔ m ⊔ k)
pullback {n} {m} {k} {A} {B} {C} f g = Σ a ∶ A , (Σ b ∶ B , ((f a) ≡ (g b)))

-- Sets and Logic --
--------------------

-- Sets --
is_set : ∀ {n} → Set n → Set n
is_set X = (x y : X) → (p q : x ≡ y) → p ≡ q

-- Mere Propositions --
is_prop : ∀ {n} → Set n → Set n
is_prop X = (x y : X) → x ≡ y

-- Contractibility --
is_contr : ∀ {n} → Set n → Set n
is_contr X = Σ x ∶ X , ((y : X) → x ≡ y)

-- Truncation --
decidable : ∀ {n} → (A : Set n) → Set n
decidable A = A + ¬ A

-- Alternate equivalence definition
is_equiv_fiber : ∀ {n m} {X : Set n} {Y : Set m} 
            → (X → Y) → Set (n ⊔ m)
is_equiv_fiber {n} {m} {X} {Y} f = (y : Y) → is_contr(fib f y)


-- Uniqueness principles --
---------------------------

-- Product types --
×uniq   : ∀ {n}
        → {A B : Set n}
        → (x : A × B)
        → x ≡ (×pr₁ x , ×pr₂ x)
×uniq = ×-induction λ a b → refl (a , b) 
