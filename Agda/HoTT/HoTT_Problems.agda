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

-- Problem 1.5 --
--_+'_ : {n : Level} (A B : Set n) → Set n  
--A +' B = Σ x ∶ 𝟚 , (𝟚-rec A B x)
--
--inl'  : ∀ {n} {A B : Set n} → (A → A +' B)
--inl' a = (zero , a)
--
--inr'  : ∀ {n} {A B : Set n} → (B → A +' B)
--inr' b = (one , b)
--
--+'-induction  : ∀ {n m} {A B : Set n} {C : A +' B → Set m}
--              → ((a : A) → C (inl' a))
--              → ((b : B) → C (inr' b))
--              → ((z : A +' B) → C z)
--+'-induction {n} {m} {A} {B} {C} f g z = Σ-induction  {lzero} {n} {m}
--                                                      {𝟚}
--                                                      {λ x → (𝟚-rec A B x)}
--                                                      {C} 
--                                                      z

-- Problem 1.6 --

-- Problem 1.7 --
-- Problem 1.8 --

_∙ₙ_  : ℕ → ℕ → ℕ
n ∙ₙ m = ℕ-rec (λ n → 0) (λ n f → (λ m → f(m) +ₙ m)) n m

_^_ : ℕ → ℕ → ℕ
n ^ m = ℕ-rec (λ n → 0) (λ n f → (λ m → f(m) ∙ₙ m)) n m

-- We prove the properties of a semi ring separately and aggregate them at the end --

--ℕ_is_set : is_set ℕ



zero-mult : ((n : ℕ) → (0 ∙ₙ n) ≡ 0)
zero-mult = ℕ-induction (refl 0) (λ m p → refl 0)

zero-add-l : ((n : ℕ) → (0 +ₙ n) ≡ n)
zero-add-l  = ℕ-induction (refl 0) (λ m p → refl (succ m)) 

zero-add-r : ((n : ℕ) → (n +ₙ 0) ≡ n)
zero-add-r  = ℕ-induction (refl 0) (λ n p → ap succ p) 

succ-comm : (n m : ℕ) → (n +ₙ (succ m)) ≡ ((succ n) +ₙ m)
succ-comm = ℕ-induction (λ m → refl (succ m)) 
                        (λ n p m → ap succ (p m))

lemma-add-comm : (n m : ℕ) → ((succ n) +ₙ m) ≡ (m +ₙ (succ n))
lemma-add-comm n = ℕ-induction  ((zero-add-r (succ n)) ∙ ((zero-add-l (succ n)) ⁻¹))
                                (λ m p → (ap succ (succ-comm n m)) ∙ (ap succ p))

add-comm : ((n m : ℕ) → (n +ₙ m) ≡ (m +ₙ n))
add-comm = ℕ-induction  (λ m → (zero-add-l m) ∙ ((zero-add-r m) ⁻¹))
                        (λ n p m → (lemma-add-comm n m))

add-assoc : (n m l : ℕ) → ((n +ₙ m) +ₙ l) ≡ (n +ₙ (m +ₙ l))
add-assoc = ℕ-induction (λ m l → refl (m +ₙ l))
                        (λ n p m l → ap succ (p m l))


succ≡n+1 :  (n : ℕ) → (succ n) ≡ (n +ₙ 1)
succ≡n+1 = ℕ-induction  (refl 1)
                        (λ n p → ap succ p)


mult-assoc : (n m l : ℕ) → ((n ∙ₙ m) ∙ₙ l) ≡ (n ∙ₙ (m ∙ₙ l))
mult-assoc = ℕ-induction (λ m l → refl 0)
                        (λ n p m l → ap succ (p m l))
--
-- is_semi_ring A =  Σ zero ∶ A ,
--                    Σ _+ₐ_ ∶ (A → A → A) , 
--                    Σ _∙ₐ_ ∶ (A → A → A) , 
--                    (is_set A) 
--                    × ((n : A) → (zero +ₐ n) ≡ n)
--                    × ((n : A) → (n ∙ₐ zero) ≡ zero)
--                    × ((n m : A) → (n +ₐ m) ≡ (m +ₐ n))
--                    × ((n m l : A) → ((n +ₐ m) +ₐ l) ≡ (n +ₐ (m +ₐ l)))
--                    × ((n m l : A) → ((n ∙ₐ m) ∙ₐ l) ≡ (n ∙ₐ (m ∙ₐ l)))
--                    × ((n : A) → (n ∙ₙ 1) ≡ n)
--                    × ((n : A) → (1 ∙ₙ n) ≡ n)
--                    × ((n m l : A) → (n ∙ₐ (m +ₐ l)) ≡ ((n ∙ₐ m)  +ₐ (n ∙ₐ l)))
