import Mathlib.Init.Data.List.Basic
--import Mathlib.Data.Tree.Basic

inductive Typ : Type
  | base : Typ
  | leftarrow : Typ → Typ → Typ
  | rightarrow : Typ → Typ → Typ
open Typ

notation A"⇐"B => leftarrow A B
notation A"⇒"B => leftarrow A B

mutual
inductive Term : Type
  | var : ℕ → Term
  | absL : Term → Term → Term
  | absR : Term → Term → Term
  | app : TreeTerm → TreeTerm → Term

inductive TreeTerm : Type
  | hole : ℕ → TreeTerm
  | leaf : Term → TreeTerm
  | cons : TreeTerm → TreeTerm → TreeTerm
  | app : TreeTerm → TreeTerm → TreeTerm
end

open TreeTerm
open Term

notation t"{"q"}" => Term.app t q

instance : OfNat Term n where
  ofNat := Term.var n

-- Need this for dependencies between trees --
inductive TreeTyp : Type
  | hole : TreeTyp
  | leaf : Typ → TreeTyp
  | cons : TreeTyp → TreeTyp → TreeTyp
  | app : TreeTyp → TreeTyp → TreeTyp

open TreeTyp



instance : OfNat TreeTerm n where
  ofNat := TreeTerm.leaf (Term.var n)

class OfTyp (α : Type u) (T : Typ) where
  ofTyp : α

instance : OfTyp TreeTyp T where
  ofTyp := TreeTyp.leaf T



-- class OfNat (α : Type u) (_ : Nat) where
--   /-- The `OfNat.ofNat` function is automatically inserted by the parser when
--   the user writes a numeric literal like `1 : α`. Implementations of this
--   typeclass can therefore customize the behavior of `n : α` based on `n` and
--   `α`. -/
--   ofNat : α

notation "□"n => TreeTerm.hole n
notation "["a"]" => TreeTerm.leaf a
notation "("t","q")" => TreeTerm.cons t q
notation t"{"q"}" => TreeTerm.app t q

notation "□" => TreeTyp.hole
notation "["a"]" => TreeTyp.leaf a
notation "("t","q")" => TreeTyp.cons t q
notation t"{"q"}" => TreeTyp.app t q

inductive TreeDeduction : TreeTerm → TreeTyp → Type
  | hole : TreeDeduction (□ n) □
  | leaf : TreeDeduction [t] [T]
  | cons : TreeDeduction t₁ T₁ → TreeDeduction t₂ T₂ → TreeDeduction (t₁, t₂) (T₁,T₂)
  | appR : TreeDeduction (t, (□ n)) (T, □) → TreeDeduction q Q → TreeDeduction (t{q}) (T, Q)
  | appL : TreeDeduction ((□ n),t) (□ , T) → TreeDeduction q Q → TreeDeduction (t{q}) (Q , T)
open TreeDeduction

notation "⊩"q ":"Q => TreeDeduction q Q

variable {N S : Typ}
abbrev S₁ := ([N],([(N ⇐ S) ⇒ N] , [N]))

def ex₁ : ⊩ (0, 1) : ([N] , [N]) := by
  apply TreeDeduction.cons
  <;> apply TreeDeduction.leaf


def ex₂ : (t : TreeTerm) × ⊩ t : ([N],([(N ⇐ S) ⇒ N] , [N])) := by
  constructor
  case fst => exact [0]{[1]{[2]}}
  case snd =>
    apply appR
    case n => exact 0
    case a => apply TreeDeduction.cons ; apply TreeDeduction.leaf ; apply TreeDeduction.hole
    case a =>
      apply appL
      case n => exact 1
      case a => apply TreeDeduction.cons ; apply TreeDeduction.hole ;apply TreeDeduction.leaf
      case a => apply TreeDeduction.leaf

inductive Deduction : TreeTerm → TreeTyp → Term → Typ → Type
  | LeftIntro : Deduction ([t] , l) ([T], Λ) a A → Deduction l Λ (absL t a) (T ⇐ A)
  | RightIntro : Deduction (l, [t]) (Λ, [T]) a A → Deduction l Λ (absR a t) (A ⇒ T)
  | LeftElim : Deduction ([a] , [f]) ([A] , [A ⇐ B]) ([f]{[a]}) B
  | RightElim : Deduction ([f] , [a]) ([A ⇒ B] , [B]) ([f]{[a]}) A
  | cut : Deduction δ Δ a A → Deduction (γ{[a]}) (Γ{[A]}) b B → Deduction (γ{δ}) (Γ{Δ}) ([b]{γ{[a]{δ}}}) B

open Deduction

notation γ "∶" Γ "⊢" t ":" T => Deduction γ Γ t T

def ex₃ : (γ : TreeTerm) × (t : Term) × (γ ∶ ([N],([(N ⇐ S) ⇒ N] , [N])) ⊢ t : S) := by
  constructor
  sorry
