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

-- Contrapositive
prop₁₂ : {A B : Set} → (A → B) → (¬ B → ¬ A)
prop₁₂ = λ f g a → g (f a) 

-- Double negation introduction
prop₁₃ : {A : Set} → A → ¬¬ A
prop₁₃ = λ a ¬a → ¬a a 

prop₁₄ : {A B : Set} → (A + B) → ¬ ((¬ B) × (¬ A))
prop₁₄ = +-induction  (λ a → ×-induction (λ ¬b ¬a → ¬a a))  
                      (λ b → ×-induction (λ ¬b ¬a → ¬b b))  


prop₁₅ : {A B : Set} → ((¬ A) + (¬ B)) → ¬ (A × B)
prop₁₅ = +-induction  (λ ¬a → ×-induction (λ a b → ¬a a))
                      (λ ¬b → ×-induction (λ a b → ¬b b))

prop₁₆ : {A B : Set} → (¬ (A + B)) ↔ ((¬ A) × (¬ B))
prop₁₆ =  ( (λ f → ((λ a → f (inl a)) , (λ b → f (inr b))))
          ,
          (×-induction (λ ¬a ¬b → +-induction (λ a → ¬a a) (λ b → ¬b b)  )))

prop₁₇ : {A : Set} → ¬ A → (¬ (¬¬ A))
prop₁₇ = λ f g → g f 

prop₁₈ : {A B : Set} → (A → ¬ B) ↔ ((¬¬ A) → (¬ B))
prop₁₈ = (  (λ f g b → g ((prop₁₂ f) (prop₁₃ b)))
          , (λ f a b → (f (prop₁₃ a)) b)
          )


prop₁₉ : {A B : Set} → (¬¬ (A + B)) ↔ (¬ ((¬ A) × (¬ B)))
prop₁₉ = (  (λ ¬¬a+b ¬a×¬b → ¬¬a+b (+-induction (λ a → (×pr₁ ¬a×¬b) a) (λ b → (×pr₂ ¬a×¬b) b)))  
          , (λ f g → f ( (λ a → g (inl a)), (λ b → g (inr b)))))


--prop₂₀ : {A B : Set} → ¬¬ (A → B) → ((¬¬ A) → (¬¬ B))
--prop₂₁ : {A B : Set} → ¬¬ (A × B) → ((¬¬ A) × (¬¬ B))
--prop₂₂ : {A : Set} → ⊥ ↔ (A × (¬ A))
--prop₂₃ : {A B : Set} → ¬ A → (A → B)
--prop₂₄ : {A B : Set} → A + B → ((¬ A) → B)
--prop₂₅ : {A B : Set} → ¬ (A → B) → (¬¬ A)
--prop₂₆ : {A B : Set} → ¬¬ (A → B) ↔ ¬ ((¬¬ A) → (¬¬B))
--prop₂₇ : {A : Set} → A + ⊥ ↔ A
--prop₂₈ : {A : Set} → A × ⊥ ↔ ⊥
