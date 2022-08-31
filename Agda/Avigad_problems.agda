module Avigad_problems where

open import Agda.Primitive
open import HoTT

-- Definitions --
-----------------

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) × (B → A)

-- Propositional validities --
------------------------------

prop₁ : {A B : Set} → A × B → B × A
prop₁ = λ z → (×pr₂ z , ×pr₁ z)

prop₂ : {A B : Set} → A + B → B + A
prop₂ = +-induction (λ x → inr x) (λ x → inl x)

prop₃ : {A B C : Set} → (A × B) × C → A × (B × C)
prop₃ = ×-induction (λ ab c → ×-induction (λ a b → (a , (b , c)) ) ab)

prop₄ : {A B C : Set} → (A + B) + C → A + (B + C)
prop₄ = +-induction (+-induction (λ a → inl a) (λ b → inr (inl b))) 
                    (λ c → inr ( inr c)) 
                          

prop₅ : {A B C : Set} → A + (B × C) → (A + B) × (A + C)
prop₅ = +-induction (λ a → (inl a , inl a))
                    (×-induction (λ b c → (inr b , inr c)))
                              

prop₆ : {A B C : Set} → A × (B + C) → (A × B) + (A × C)
prop₆ =  ×-induction  (λ a → +-induction (λ b → inl (a , b)) (λ c → inr (a , c))) 

prop₇ : {A B C : Set} → (A → B → C) ↔ ((A × B) → C)
prop₇ = ((λ f → ×-induction (λ a b → f a b)) , (λ g a b → g (a , b)))

prop₈ : {A B C : Set} → (A → B) → ((B → C) → (A → C))
prop₈ = λ f g a → g (f a)

prop₉ : {A B C : Set} → ((A + B) → C) ↔ ((A → C) × (B → C))
prop₉ = ( (λ f → ((λ a → f (inl a)) , (λ b → f (inr b))))  
        , (×-induction (λ f g → +-induction (λ a → f a) (λ b → g b))))

prop₁₀ : {A B : Set} → ¬ (A × ¬ A)
prop₁₀ = ×-induction (λ a ¬a → ¬a a)

prop₁₁ : {A B : Set} → (¬ (A → B)) → (¬ B)
prop₁₁ = λ z b → z (λ a → b)
