module Foundations.Homotopy_Type_Theory where

open import Agda.Primitive
open import Foundations.Type_Theory

variable
    n : Level
    A : Set n
    a b c : A

≡-reflexivity : ∀ {n} {A : Set n} {a b : A} → a ≡ b → b ≡ a
≡-reflexivity p = ≡-ind (λ z → (refl z)) (src p) (dst p) p

≡-transitivity : ∀ {n} {A : Set n} {a b : A} 
                    → a ≡ b 
                    → (c : A) → b ≡ c → a ≡ c
≡-transitivity {A = A} p = ≡-ind {P = P} (λ z → (λ c q → q)) (src p) (dst p) p
    where P = λ a b p → (c : A) → b ≡ c → a ≡ c

_•_ : a ≡ b → b ≡ c → a ≡ c
p • q = ≡-transitivity p (dst q) q

Lemma2-1-4 : (p : a ≡ a) → ((p • (refl a)) ≡ p)
Lemma2-1-4  p = ≡-ind {P = λ b c p → ((p • (refl c)) ≡ p)} (λ c →  (refl (refl c))) (src p) (src p) p
