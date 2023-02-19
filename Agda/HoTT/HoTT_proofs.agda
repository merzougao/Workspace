module HoTT_proofs where

open import HoTT 

-- Proof 𝟙 is contractible with center ✭ --
𝟙-is-contr : is_contr 𝟙
𝟙-is-contr = (✭ , 𝟙-induction (refl ✭))

𝟘-is-prop : is_prop 𝟘
𝟘-is-prop = 𝟘-induction
