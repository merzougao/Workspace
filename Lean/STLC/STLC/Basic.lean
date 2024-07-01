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

-- Carefull, this is "\ :" not just ":"
notation:max a"∶"T => ctx_elem.mk a T

notation "Ctx" => List ctx_elem


-- TODO Fix this
-- instance : Membership ℕ Ctx where
--   mem := by
--     intro c Γ
--     cases Γ
--     case nil => exact False
--     case cons h Γ₀ => exact h.var = c ∨ Membership.mem c Γ₀

inductive NatInCtx : ℕ → Ctx → Prop
  | init : NatInCtx n ((n∶T) :: Γ)
  | cons : n ≠ c.var → NatInCtx n Γ → NatInCtx n (c :: Γ)

notation n"∈₁"Γ => NatInCtx n Γ
notation n"∉₁"Γ => ¬ NatInCtx n Γ

-- instance : HasSubset Ctx where
--   Subset := by
--     intro Γ Δ
--     cases Γ
--     case nil => exact True
--     case cons c₀ Γ₀ => exact (c₀ ∈ Δ) ∧ HasSubset.Subset Γ₀ Δ
inductive Valid : Ctx → Prop
  | nil : Valid []
  | cons : (c.var ∉₁ Γ) → Valid Γ → Valid (c :: Γ)

inductive Typing : Ctx → Term → Typ → Type
  | var : Valid (c :: Γ) → Typing (c :: Γ) (Term.var c.var) c.typ
  | ex : Typing (Γ ++ t₀ :: t₁ :: Δ) t T → Typing (Γ ++ t₁ :: t₀ :: Δ) t T
  | abs : Typing ((x∶A) :: Γ) t B → Typing Γ (λ[x].t) (A->B)
  | app : Typing Γ t₀ (A->B) → Typing Γ t₁ A → Typing Γ t₀{t₁} B

notation:max Γ "⊢" t "∶∶" A => Typing Γ t A


-- Weakening is admissible
def Weakening : (Γ ⊢ t ∶∶ A) → (Δ : Ctx) → (Γ ⊆ Δ) → (Δ ⊢ t ∶∶ A) := by
  intro d
  induction d
  case var c₀ Γ₀ p₀ =>
    intro Δ d₀
    induction Δ
    case nil => sorry --contradiction
    case cons h₀ Δ₀ iH =>
      cases d₀
      case intro l r =>
        have : c₀ = h₀ ∨ c₀ ∈ Δ₀ := @InCtx c₀ Δ₀
