module Foundations.Homotopy_Type_Theory where

open import Agda.Primitive
open import Foundations.Type_Theory

-- Types are higher groupoids --
--------------------------------

variable
    n : Level
    A B : Set n
    a b c d : A

≡-reflexivity : a ≡ b → b ≡ a
≡-reflexivity p = ≡-ind (λ z → (refl z)) (src p) (dst p) p


_⁻¹ : a ≡ b → b ≡ a 
p ⁻¹ = ≡-reflexivity p

infix 30 _⁻¹

≡-transitivity : a ≡ b → (c : A) → b ≡ c → a ≡ c
≡-transitivity {A = A} p = ≡-ind {P = P} (λ z → (λ c q → q)) (src p) (dst p) p
    where P = λ a b p → (c : A) → b ≡ c → a ≡ c

_•_ : a ≡ b → b ≡ c → a ≡ c
p • q = ≡-transitivity p (dst q) q

infix 25 _•_


variable 
    p : a ≡ a

Lemma2-1-4-i : p • (refl a) ≡ p
Lemma2-1-4-i {p = p} = ≡-ind {P = λ b c p → (p • (refl c) ≡ p)} (λ c →  (refl (refl c))) (src p) (src p) p

Lemma2-1-4-ii : (p ⁻¹ • p) ≡ (refl a)
Lemma2-1-4-ii {p = p} = ≡-ind {P = λ a b p → (p ⁻¹ • p) ≡ (refl b)} (λ c → (refl (refl c))) (src p) (dst p) p

Lemma2-1-4-iii : (p ⁻¹) ⁻¹ ≡ p
Lemma2-1-4-iii {p = p} = ≡-ind {P = λ a b p → (p ⁻¹) ⁻¹ ≡ p} (λ c → (refl (refl c))) (src p) (dst p) p



Lemma2-1-4-iv : (p : a ≡ b) 
                → (c d : A) → (q : b ≡ c) → (r : c ≡ d) 
                → p • (q • r) ≡ (p • q) • r
Lemma2-1-4-iv {A = A} {a} {b} p = ≡-ind {P = P} (λ z c d q r → (refl (q • r))) a b p where
    P = λ a b p → (c d : A) → (q : b ≡ c) → (r : c ≡ d) → p • (q • r) ≡ (p • q) • r

-- Eckmann-Hilton --
--------------------

-- Loop spaces --
-- Ω : (m : ℕ) → (A : Set n ) → (a : A) → Set n
-- Ω = ℕ-ind (λ A a → a ≡ a) (λ m s → s ≡ s)

-- Eckmann-Hilton : (α β : (Ω 2 A a)) → α • β  = β • α
-- TO FINISH --

-- Functions are functors --
----------------------------

variable
    f : A → B
    x y : A

ap : x ≡ y → (f x) ≡ (f y)
ap {f = f} p = ≡-ind {P = λ x y p → f x ≡ f y} (λ z → refl (f z)) (src p) (dst p) p

