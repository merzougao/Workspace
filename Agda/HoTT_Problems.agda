open import HoTT
open import Agda.Primitive

-- Problem 1 --
-- This is defined in HoTT.agda as the operator "∘"

-- Problem 1.2 --
recA×B : ∀ {n} 
        → (A B C : Set n) 
        → (A → B → C) 
        → A × B → C

recA×B = λ A B C g r → g(×pr₁(r))(×pr₂(r))

recΣ    : ∀ {n m}
        → (A C : Set n)
        → (B : A → Set m)
        → ((x : A) → B x → C)
        → (Σ x ∶ A , B x) → C
recΣ = λ A C B g r → g (pr₁ r) (pr₂ r)

-- Problem 1.3 --

indA×B : ∀ {n m} 
        → (A B : Set n) 
        → (C : A × B →  Set m) 
        → ((a : A) → (b : B) → C (a , b)) 
        → ((z : A × B) → C z)
indA×B {n} {m} = λ A B C g z → ≡-transport  n m 
                                    (A × B) 
                                    (λ r → C r) 
                                    (×pr₁ z , ×pr₂ z) 
                                    z
                                    ((×uniq z) ⁻¹) 
                                    (g (×pr₁ z) (×pr₂ z))


-- Problem 1.4 --

ℕ-iter : ∀ {n} {C : Set n} → C → (C → C) → ℕ → C
ℕ-iter c₀ cₛ 0 = c₀
ℕ-iter c₀ cₛ (succ n) = cₛ (ℕ-iter c₀ cₛ n)

recℕ    : ∀ {n} {C : Set n} 
        → C
        → (ℕ → C → C)
        → (ℕ → C)
recℕ c₀ cₛ 0 = c₀
recℕ c₀ cₛ (succ n) = cₛ n (recℕ c₀ cₛ n)

cₛ'     : ∀ {n} {C : Set n}
        → (ℕ → C → C)
        → ℕ × C → ℕ × C
cₛ' cₛ = λ z → (succ (×pr₁ z) , cₛ (×pr₁ z)  (×pr₂ z))

recℕ'   : ∀ {n} {C : Set n} 
        → C
        → (ℕ → C → C)
        → (ℕ → C)
recℕ' {i} {C} c₀ cₛ n = ×pr₂ (ℕ-iter  {i} 
                                {ℕ × C} 
                                (0 , c₀) 
                                (cₛ' {i} {C} cₛ)
                                n
                                ) 
                                
lemma1  : ∀ {i} {C : Set i}
        → (c₀ : C)
        → (cₛ : ℕ → C → C)
        → (n : ℕ)
        → (×pr₁ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n) ≡ n)
lemma1 {i} {C} c₀ cₛ 0 = refl 0
lemma1 {i} {C} c₀ cₛ (succ n) = ap {lzero} {lzero} {ℕ} {ℕ} 
                                succ 
                                {×pr₁ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n)}
                                {n}
                                (lemma1 {i} {C} c₀ cₛ n)



lemma2  : ∀ {i} {C : Set i}
        → (c₀ : C)
        → (cₛ : ℕ → C → C)
        → (n : ℕ)
        → cₛ (×pr₁ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n)) ≡ (cₛ n)
lemma2 {i} {C} c₀ cₛ n = ap {lzero} {i} {ℕ} {(C → C)}
                            cₛ
                            {(×pr₁ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n))}
                            {n}
                            (lemma1 {i} {C} c₀ cₛ n)

lemma3  : ∀ {i} {C : Set i}
        → (c₀ : C)
        → (cₛ : ℕ → C → C)
        → (n : ℕ)
        → (×pr₂ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n)) ≡ (recℕ c₀ cₛ n)
lemma3 {i} {C} c₀ cₛ 0 = refl c₀
lemma3 {i} {C} c₀ cₛ (succ n) = apf {i} {i} {C} {C}
                                    {(cₛ (×pr₁ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n)))}
                                    {(cₛ n)}
                                    (lemma2 {i} {C} c₀ cₛ n)
                                    (×pr₂ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n))
                                    (recℕ c₀ cₛ n)
                                    (lemma3 {i} {C} c₀ cₛ n)
                                
proof_recℕ≡recℕ'    : ∀ {i} {C : Set i}
                    → (c₀ : C)
                    → (cₛ : ℕ → C → C)
                    → (n : ℕ)
                    → (recℕ' c₀ cₛ n) ≡ (recℕ c₀ cₛ n)
proof_recℕ≡recℕ' {i} {C} c₀ cₛ 0 = refl c₀
proof_recℕ≡recℕ' {i} {C} c₀ cₛ (succ n) = apf {i} {i} {C} {C}
                                    {(cₛ (×pr₁ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n)))}
                                    {(cₛ n)}
                                    (lemma2 {i} {C} c₀ cₛ n)
                                    (×pr₂ (ℕ-iter {i} {ℕ × C} (0 , c₀) (cₛ' {i} {C} cₛ) n))
                                    (recℕ c₀ cₛ n)
                                    (lemma3 {i} {C} c₀ cₛ n)
