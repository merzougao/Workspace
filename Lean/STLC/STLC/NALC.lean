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

-- Need to define PreCtx as a tree, can't use mathlib because we need to store
-- values in leaf nodes.

inductive PreCtx : Type
  | leaf : Term → Typ → PreCtx
  | cons : (left : PreCtx) → (right: PreCtx) → PreCtx

def left : PreCtx → PreCtx := by
  intro Γ
  cases Γ
  case leaf a A => exact PreCtx.leaf a A
  case cons l r => exact l

def right : PreCtx → PreCtx := by
  intro Γ
  cases Γ
  case leaf a A => exact PreCtx.leaf a A
  case cons l r => exact r

notation:max "["a"∶"A"]" => PreCtx.leaf a A

instance : Append (PreCtx) where
  append := PreCtx.cons

inductive Path : Type
  | dest : Path
  | left : Path → Path
  | right : Path → Path

inductive ValidPath : PreCtx → Path → Prop
  | dest (a : Term) (A : Typ) : ValidPath (PreCtx.leaf a A) dest
  | cons (l r : PreCtx): ValidPath (l ++ r) p

structure Ctx where
  tree : PreCtx
  path : Path
  valid : ValidPath tree path

def Γ : Ctx := Ctx.mk [0∶base] Path.dest (ValidPath.dest 0 base)

def Subst : Ctx → Term → Typ → Ctx := by
  intro Γ a A
  cases Γ
  case mk t₀ p₀ v₀ =>
    induction p₀
    case dest => exact Ctx.mk [a∶A] Path.dest (ValidPath.dest a A)
    case left pl iH =>
      exact (Ctx.mk (left t₀) pl (ValidPath.cons (left t₀) (right t₀) pl))



-- inductive Deduction : Ctx → Term → Typ → Type
--   | id : Deduction [] (λ[x].Term.var x) A
--   | cut {Γ : Tree Typ}{A B : Typ}: (Deduction Γ[Ctx.cons_typ A] b B)
--                                     → Deduction Δ a A
--                                     → Deduction Γ[Δ] λ γ. b(γ(a(δ))) B
