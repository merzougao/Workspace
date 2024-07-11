import Mathlib.Init.Data.List.Basic
import Mathlib.Data.Tree.Basic

open List
open Tree

inductive Typ : Type
  | base : Typ
  | arrow : Typ → Typ → Typ

export Typ (base)
notation A"->"B => Typ.arrow A B

def TypToString : Typ → String := by
  intro A
  cases A
  case base => exact "base"
  case arrow A₀ A₁ => exact TypToString A₀ ++ "->" ++ TypToString A₁

inductive Term : Type
  | var : ℕ → Term
  | abs : ℕ → Term → Term
  | app : Term → Term → Term

def TermToString : Term → String := by
  intro t
  cases t
  case var m => exact "x"++toString m
  case abs x p => exact "λ" ++ "x"++ (toString x) ++ ". " ++ (TermToString p)
  case app t₀ t₁ => exact "(" ++ TermToString t₀ ++ ")(" ++ TermToString t₁ ++ ")"

instance : ToString (Term) where
  toString := TermToString

instance : ToString (Typ) where
  toString := TypToString

instance : OfNat Term n where
  ofNat := Term.var n

notation:max "λ["x"]."t => Term.abs x t
-- notation:max "λ←["x"]."t => Term.abs_left x t
-- notation:max "λ→["x"]."t => Term.abs_right x t
notation:max t₁"{"t₂"}" => Term.app t₁ t₂

-- #check (λ←[0].5){4}
-- #check (λ→[0].5){4}

#check (λ[0].5){4}


-- Need to define PreCtx as a tree, can't use mathlib because we need to store
-- values in leaf nodes.

inductive PreCtx : Type
  | leaf : Term → Typ → PreCtx
  | cons : (left : PreCtx) → (right: PreCtx) → PreCtx

def PreCtxToString : PreCtx → String := by
  intro Γ
  cases Γ
  case leaf a A => exact toString a ++ ":" ++ toString A
  case cons l r => exact "(" ++ PreCtxToString l ++","++ PreCtxToString r ++ ")"

instance : ToString (PreCtx) where
  toString := PreCtxToString


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

def Γ' : PreCtx := [0∶base] ++ ([2∶base] ++ [5∶base->base])
#eval Γ'


inductive Path : Type
  | nil : Path
  | dest : Path
  | left : Path → Path
  | right : Path → Path

inductive ValidPath : PreCtx → Path → Prop
  | nil : ValidPath Γ Path.nil
  | dest (a : Term) (A : Typ) : ValidPath (PreCtx.leaf a A) dest
  | cons (l r : PreCtx): ValidPath (l ++ r) p

notation:max p"⊆"Γ => ValidPath Γ p

def Subst : PreCtx → Path → Term → Typ → PreCtx := by
  intro Γ p a A
  cases p
  case nil => exact Γ
  case dest => exact [a∶A]
  case left pl =>
    cases Γ
    case leaf a₀ A₀ => exact [a₀∶A₀]
    case cons l r => exact (Subst l pl a A) ++ r
  case right pr =>
    cases Γ
    case leaf a₀ A₀ => exact [a₀∶A₀]
    case cons l r => exact l ++ (Subst r pr a A)

notation:max Γ"←["a"∶"A"]"p => Subst Γ p a A

#eval [0∶base]←[4∶base](Path.left Path.dest)
#eval [0∶base]←[4∶base]Path.dest
#eval ([0∶base] ++ ([2∶base] ++ [5∶base->base]))←[4∶base](Path.left Path.dest)
#eval ([0∶base] ++ ([2∶base] ++ [5∶base->base]))←[4∶base](Path.right Path.dest)
#eval ([0∶base] ++ ([2∶base] ++ [5∶base->base]))←[4∶base](Path.right (Path.right Path.dest))





-- inductive Deduction : Ctx → Term → Typ → Type
--   | id : Deduction [] (λ[x].Term.var x) A
--   | cut {Γ : Tree Typ}{A B : Typ}: (Deduction Γ[Ctx.cons_typ A] b B)
--                                     → Deduction Δ a A
--                                     → Deduction Γ[Δ] λ γ. b(γ(a(δ))) B
