module Foundations.Homotopy_Type_Theory where

open import Agda.Primitive
open import Foundations.Type_Theory

≡-reflexivity : ∀ {n} {A : Set n} {a b : A} → a ≡ b → b ≡ a
≡-reflexivity p = ≡-ind (λ z → (refl z)) (src p) (dst p) p

≡-transitivity : ∀ {n} {A : Set n} {a b : A} 
                    → a ≡ b 
                    → (c : A) → b ≡ c → a ≡ c
≡-transitivity {A = A} p = ≡-ind {P = P} (λ z → (λ c q → q)) (src p) (dst p) p
    where P = λ a b p → (c : A) → b ≡ c → a ≡ c
