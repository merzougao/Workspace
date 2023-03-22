module Foundations.Homotopy_Type_Theory where

open import Agda.Primitive
open import Foundations.Type_Theory

-- Types are higher groupoids --
--------------------------------

variable
    n m : Level
    A B C : Set n
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
    p : a ≡ b

Lemma-2-1-4-i : p • (refl b) ≡ p
Lemma-2-1-4-i {p = p} = ≡-ind {P = λ a b p → p • (refl b) ≡ p} (λ c →  (refl (refl c))) (src p) (dst p) p

Lemma-2-1-4-i' : (refl a) • p ≡ p
Lemma-2-1-4-i' {p = p} = ≡-ind {P = λ a b p → (refl a) • p ≡ p} (λ c →  (refl (refl c))) (src p) (dst p) p

Lemma-2-1-4-ii : (p ⁻¹ • p) ≡ (refl a)
Lemma-2-1-4-ii {p = p} = ≡-ind {P = λ a b p → (p ⁻¹ • p) ≡ (refl b)} (λ c → (refl (refl c))) (src p) (dst p) p

Lemma-2-1-4-iii : (p ⁻¹) ⁻¹ ≡ p
Lemma-2-1-4-iii {p = p} = ≡-ind {P = λ a b p → (p ⁻¹) ⁻¹ ≡ p} (λ c → (refl (refl c))) (src p) (dst p) p



Lemma-2-1-4-iv : (p : a ≡ b) 
                → (c d : A) → (q : b ≡ c) → (r : c ≡ d) 
                → p • (q • r) ≡ (p • q) • r
Lemma-2-1-4-iv {A = A} {a} {b} p = ≡-ind {P = P} (λ z c d q r → (refl (q • r))) a b p where
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
    x y z : A
    r : x ≡ y

ap : (f : A → B) → x ≡ y → (f x) ≡ (f y)
ap f p = ≡-ind {P = λ x y p → f x ≡ f y} (λ z → refl (f z)) (src p) (dst p) p


lemma-2-2-2-i : (z : A) → (q : y ≡ z) → (ap f (r • q)) ≡ ((ap f r) • (ap f q))

lemma-2-2-2-i {A = A} {f = f} {r = r} = ≡-ind {P = λ x y r → (z : A) → (q : y ≡ z) → (ap f (r • q)) ≡ ((ap f r) • (ap f q))}
                                (λ c z q → (refl (ap f q))) (src r) (dst r) r 

lemma-2-2-2-ii : ap f (r ⁻¹) ≡ (ap f r) ⁻¹
lemma-2-2-2-ii {f = f} {r = r} = ≡-ind   {P = λ x y r → (ap f (r ⁻¹)) ≡ (ap f r) ⁻¹}
                                (λ c → refl (refl (f c))) (src r) (dst r) r

lemma-2-2-2-iii : (g : B → C) → ap g (ap f r) ≡ ap (g ∘ f) r
lemma-2-2-2-iii {f = f} {r = r} g = ≡-ind  {P = λ x y r → ap g (ap f r) ≡ ap (g ∘ f) r}
                                                (λ c → refl (refl (g (f c)))) (src r) (dst r) r

lemma-2-2-2-iv : (ap id r) ≡ r
lemma-2-2-2-iv {r = r} = ≡-ind   {P = λ x y r → (ap id r) ≡ r}
                        (λ c → refl (refl c)) (src r) (dst r) r


-- Type families are fibrations --
----------------------------------

-- Transport --
Tr : (Q : A → Set n) → x ≡ y → Q x → Q y
Tr Q p = ≡-ind  {P = λ x y p → Q x → Q y}
                (λ z → id)
                (src p) (dst p) p

lift : (Q : A → Set n) → (p : x ≡ y) → (u : Q x) → (x , u) ≡ (y , Tr Q p u)
lift Q p = ≡-ind  {P = λ x y p → (u : Q x) → (x , u) ≡ (y , Tr Q p u)}
                    (λ z u → refl (z , u))
                    (src p) (dst p) p


apd : {Q : A → Set n} (f :  ((x : A)  →  Q x)) 
        → (p : x ≡ y) →  Tr Q p (f x) ≡ f y
apd {A = A} {Q = Q} f p = ≡-ind {P = λ x y p → Tr Q p (f x) ≡ f y}
                (λ z → (refl (f z))) (src p) (dst p) p

Tr_const : (p : x ≡ y) → (b : B) → Tr (λ a → B) p b ≡ b
Tr_const {B = B} p = ≡-ind  {P = λ x y p → (b : B) → Tr (λ a → B) p b ≡ b}
                    (λ z b → (refl b)) (src p) (dst p) p 

--lemma2-3-8 : (f : A → B) → (p : x ≡ y) → apd f p ≡ (Tr_const p (f x)) • (ap f p)
--lemma2-3-8 {B = B} f p = ≡-ind  {λ x y p → apd (λ a → B) f p ≡ (Tr_const p (f x)) • (ap f p)}
--                    (λ z → (refl (refl (f z)))) (src p) (dst p) p

lemma-2-3-9 : (Q : A → Set n) → (p : x ≡ y) → (q : y ≡ z) → (u : Q x)
                → Tr Q q (Tr Q p u) ≡ Tr Q (p • q) u
lemma-2-3-9 {z = z} Q p  = ≡-ind {P = λ x y p → (q : y ≡ z) → (u : Q x) → Tr Q q (Tr Q p u) ≡ Tr Q (p • q) u}
                        (λ z q u → refl (Tr Q q u)) (src p) (dst p) p 

lemma-2-3-10 : (f : A → B) → (Q : B → Set n) → (p : x ≡ y) → (u : Q (f x))
                → Tr (Q ∘ f) p u ≡ Tr Q (ap f p) u
lemma-2-3-10 f Q p = ≡-ind    {P = λ x y p → (u : Q (f x)) → Tr (Q ∘ f) p u ≡ Tr Q (ap f p) u}
                            (λ z u → refl u) (src p) (dst p) p 

lemma-2-3-11 : (Q R : A → Set n) → (f : ((x : A) → Q x → R x)) → (p : x ≡ y) → (u : Q x) → Tr R p (f x u) ≡ f y (Tr Q p u)
lemma-2-3-11 Q R f p = ≡-ind    {P = λ x y p → (u : Q x) → Tr R p (f x u) ≡ f y (Tr Q p u)}
                                (λ z u → refl (f z u)) (src p) (dst p) p


-- Homotopies and Equivalences --
---------------------------------

_~_ : ∀ {n m} {A : Set n} {B : Set m} → (f g : A → B) → Set (n ⊔ m)
f ~ g = (x : dom f) → f x ≡ g x

variable
    Q : A → Set m
    g h k : (x : A) → Q x

Lemma-2-4-2-i : g ~ g
Lemma-2-4-2-i {g = g} = λ x → refl (g x)

Lemma-2-4-2-ii : h ~ g → g ~ h
Lemma-2-4-2-ii H = λ x → (H x) ⁻¹

Lemma-2-4-2-iii : h ~ g → g ~ k → h ~ k
Lemma-2-4-2-iii H G = λ x → (H x) • (G x)

Lemma-2-4-3 : (H : f ~ g) → (p : x ≡ y) → (H x) • (ap g p) ≡ (ap f p) • (H y)
Lemma-2-4-3 {f = f} {g = g} H p = ≡-ind {P = λ x y p → (H x) • (ap g p) ≡ (ap f p) • (H y)} 
                                        (λ z → (Lemma-2-1-4-i {p = H z}) • ((Lemma-2-1-4-i' {p = H z}) ⁻¹))
                                        (src p) (dst p) p

