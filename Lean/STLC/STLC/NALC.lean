import Mathlib.Init.Data.List.Basic
import Mathlib.Data.Tree.Basic

open List
open Tree

inductive Typ : Type
  | base : Typ
  | arrow : Typ → Typ → Typ

export Typ (base)
notation A"->"B => Typ.arrow A B

inductive Term : Type
  | var : ℕ → Term
  | abs : ℕ → Term → Term
  | abs_left : ℕ → Term → Term
  | abs_right : ℕ → Term → Term
  | app : Term → Term → Term


instance : OfNat Term n where
  ofNat := Term.var n

notation:max "λ["x"]."t => Term.abs x t
notation:max "λ←["x"]."t => Term.abs_left x t
notation:max "λ→["x"]."t => Term.abs_right x t
notation:max t₁"{"t₂"}" => Term.app t₁ t₂

#check (λ←[0].5){4}
#check (λ→[0].5){4}


inductive Ctx : Type
  | nil : Ctx
  | cons_typ : Typ → Ctx
  | cons : (Tree Typ) → Ctx → Ctx

notation:max "[]" => Ctx.nil
notation:max Γ"["A"]" => Ctx.cons Γ A

inductive Deduction : Ctx → Term → Typ → Type
  | id : Deduction [] (λ[x].Term.var x) A
  | cut {Γ : Tree Typ}{A B : Typ}: (Deduction Γ[Ctx.cons_typ A] b B)
                                    → Deduction Δ a A
                                    → Deduction Γ[Δ] λ γ. b(γ(a(δ))) B