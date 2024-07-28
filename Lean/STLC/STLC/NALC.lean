import Mathlib.Init.Data.List.Basic
--import Mathlib.Data.Tree.Basic

inductive Typ : Type
  | base : Typ
  | leftarrow : Typ → Typ → Typ
open Typ

inductive Term : Type
  | var : ℕ → Term
  | abs : ℕ → Term → Term
  | app : Term → Term → Term
  | leftarrow : Term → TreeTerm → Term

open Term

def subst : ℕ → Term → Term → Term := by
  intro n u t
  cases t
  case var m => exact if n = m then u else Term.var m
  case abs x p => exact if n = x then (abs x p) else (abs x (subst n u p))
  case app t₀ t₁ => exact app (subst n u t₀) (subst n u t₁)

notation:max t"["u"//"x"]" => subst x u t

-- Need this for dependencies between trees --
inductive TreeTyp : Type
  | hole : TreeTyp
  | leaf : Typ → TreeTyp
  | cons : TreeTyp → TreeTyp → TreeTyp

open TreeTyp

inductive TreeTerm : Type
  | nil : TreeTerm
  | hole : TreeTerm
  | leaf : Term → TreeTerm
  | cons : TreeTerm → TreeTerm → TreeTerm
open TreeTerm

inductive βRed : TreeTerm → TreeTerm → Type
  | id_left : βRed (cons nil t) t
  | id_right : βRed (cons t nil) t

inductive βClosure : TreeTerm → TreeTerm → Type
  | init : βRed t q → βClosure t q
  | rfl : βClosure t t
  | trans : βClosure t₁ t₂ → βClosure t₂ t₃ → βClosure t₁ t₃

--\ t--
notation t"▸"q => βClosure t q

def TreeTermSub : TreeTerm → TreeTerm → TreeTerm := by
  intro Γ Δ
  cases Γ
  case nil => exact nil
  case hole => exact Δ
  case leaf t => exact leaf t
  case cons Γ₁ Γ₂ => exact cons (TreeTermSub Γ₁ Δ) (TreeTermSub Γ₂ Δ)

def TreeTypSub : TreeTyp → TreeTyp → TreeTyp := by
  intro T Q
  cases T
  case hole => exact Q
  case leaf t => exact leaf t
  case cons T₁ T₂ => exact cons (TreeTypSub T₁ Q) (TreeTypSub T₂ Q)

inductive TreeDeduction : TreeTerm → TreeTerm → TreeTyp → Type
  | hole : TreeDeduction hole hole hole
  | leaf : (t : Term) → (T : Typ) → TreeDeduction nil (leaf t) (leaf T)
  | cons : (t = nil ∨ q = nil) → TreeDeduction  t t₁ T₁ → TreeDeduction  q q₁ Q₁ → TreeDeduction (cons t q) (cons t₁ q₁) (cons T₁ Q₁)

notation Γ "⊩" t":"T => TreeDeduction Γ t T
