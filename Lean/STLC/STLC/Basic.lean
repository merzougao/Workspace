import Mathlib.Init.Data.List.Basic

open List

inductive Typ : Type
  | base : Typ
  | arrow : Typ → Typ → Typ

export Typ (base)
notation A"->"B => Typ.arrow A B

inductive Term : Type
  | var : ℕ → Term
  | abs : ℕ → Term → Term
  | app : Term → Term → Term

instance : OfNat Term n where
  ofNat := Term.var n

def TermToString : Term → String := by
  intro t
  cases t
  case var m => exact "x"++toString m
  case abs x p => exact "λ" ++ "x"++toString x ++ ". " ++ TermToString p
  case app t₀ t₁ => exact "(" ++ TermToString t₀ ++ ")(" ++ TermToString t₁ ++ ")"

notation:max "λ["x"]."t => Term.abs x t
notation:max t₁"{"t₂"}" => Term.app t₁ t₂

#check (λ[0].5){4}
#eval TermToString (λ[0].5){3}

def subst : ℕ → Term → Term → Term := by
  intro n u t
  cases t
  case var m => exact if n = m then u else Term.var m
  case abs x p => exact if n = x then λ[x].p else λ[x].(subst n u p)
  case app t₀ t₁ => exact (subst n u t₀){subst n u t₁}

notation:max t"["u"//"x"]" => subst x u t

#eval TermToString (λ[0].5){3}[7 // 3]

structure ctx_elem where
  var : ℕ
  typ : Typ

def Ctx : Type := List ctx_elem

inductive Typing : Ctx → Term → Typ → Type
  | var : Typing (c :: Γ) (Term.var c.var) c.typ
  | weak : Typing Γ t T → c ∉ Γ → Typing (c :: Γ) t T
