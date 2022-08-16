{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT where
open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣  : Universe

data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ
 
ℕ-induction : {A : ℕ → 𝓤 ̇} 
            → A zero 
            → ((n : ℕ) → A n → A (succ n))
            → ((n : ℕ) →  A n)
ℕ-induction a₀ f  zero      = a₀ 
ℕ-induction a₀ f  (succ n)  = f n (ℕ-induction a₀ f n) 
