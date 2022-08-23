module Avigad_problems where

open import Agda.Primitive
open import HoTT

-- Propositional validities --
------------------------------

prop₁ : {A B : Set} → A × B → B × A
prop₁ = λ z → (×pr₂ z , ×pr₁ z)

prop₂ : {A B : Set} → A + B → B + A
prop₂ = λ z → +-induction (λ x → inr x) (λ x → inl x) z
