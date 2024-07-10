import Mathlib.Init.Data.List.Basic

open List

inductive Typ : Type
  | base : Typ
  | arrow : Typ → Typ → Typ

export Typ (base)
notation A"->"B => Typ.arrow A B

theorem uniquenessTypLeft {A B : Typ}: ((A -> B) = A) → False := by
  induction A
  case base =>
    intro H
    contradiction
  case arrow A₀ B₀ iH₀ iH₁ =>
    intro H
    injection H with inj₁ inj₂
    rw [←inj₂] at inj₁
    exact iH₀ inj₁

theorem uniquenessTypRight {A B : Typ}: ((A -> B) = B) → False := by
  induction A
  case base =>
    intro H
    induction B
    case base => contradiction
    case arrow C₀ C₁ iH₀ iH₁=>
      injection H with inj₁ inj₂
      rw [←inj₁] at inj₂
      exact iH₁ inj₂
  case arrow A₀ B₀ iH₀ iH₁ =>
    intro H
    induction B
    case base => contradiction
    case arrow C₀ C₁ iH₂ iH₃ =>
      injection H with inj₁ inj₂
      apply iH₃
      intro H₁
      rw [←inj₂] at H₁
      exact iH₀ H₁

def decidableTyp (n m : Nat) : (A : Typ) → (B : Typ) → (A = B) ∨ ¬ (A = B) := by
  intro A
  induction A
  case base =>
    intro B
    cases B
    case base =>
      apply Or.inl
      rfl
    case arrow B₀ B₁ =>
      apply Or.inr
      intro H
      contradiction
  case arrow A₀ A₁ iH₁ iH₂ =>
    intro B
    cases B
    case base =>
      apply Or.inr
      intro H
      contradiction
    case arrow B₀ B₁ =>
      have this₀ : (A₀ = B₀) ∨ ¬(A₀ = B₀) := iH₁ B₀
      have this₁ : (A₁ = B₁) ∨ ¬(A₁ = B₁) := iH₂ B₁
      match this₀ , this₁ with
      | inl , inl => sorry

      -- cases iH₁ B₀
      -- case inl H₀ =>
      --   rw [←H₀]
      --   cases iH₂ B₁
      --   case inl H₁ =>
      --     rw [←H₁]
      --     apply Or.inl
      --     rfl
      --   case inr H₁ =>
      --     apply Or.inr
      --     intro Hp
      --     apply H₁
      --     injection Hp
      -- case inr H₀ =>
      --   cases iH₂ B₁
      --   case inl H₁ =>
      --     rw [←H₁]
      --     apply Or.inr
      --     intro Hp
      --     apply H₀
      --     injection Hp
      --   case inr H₁ =>
      --     apply Or.inr
      --     intro Hp
      --     injection Hp with eq₀ _
      --     exact  H₀ eq₀

instance (A B : Typ) : Decidable (A = B) := by
  have : (A = B) ∨ ¬ (A = B) := decidableTyp A B
  apply Or.elim this











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

instance {c₀ c₁ : ctx_elem} : Decidable (c₀ = c₁) := by
  sorry




-- Carefull, this is "\ :" not just ":"
notation:max a"∶"T => ctx_elem.mk a T

def c₀ : ctx_elem := (3∶base)
def c₁ : ctx_elem := (3∶base)

#check c₀ = c₁
#eval c₀ = c₁

abbrev Ctx : Type := List ctx_elem

def NatInCtx : Ctx → ℕ → Prop
  | nil =>  λ (_ : ℕ)  => False
  | cons h Γ₀ => λ (n : ℕ ) => n = h.var ∨ (NatInCtx Γ₀ n)

def ElemInCtx : Ctx → ctx_elem → Prop
  | nil =>  λ (_ : ctx_elem)  => False
  | cons h Γ₀ => λ (c : ctx_elem ) => c = h ∨ (ElemInCtx Γ₀ c)


instance : Membership ℕ Ctx where
  mem := λ (n : ℕ ) => λ (Γ : Ctx) => NatInCtx Γ n

-- TODO Fix this
instance : Membership ctx_elem Ctx where
  mem := λ (c : ctx_elem ) => λ (Γ : Ctx) => ElemInCtx Γ c

notation:max c"∈"Γ => ElemInCtx Γ c
notation:max c"∉"Γ => ¬ ElemInCtx Γ c

def IsSubCtx : Ctx → Ctx → Prop := by
  intro Γ Δ
  cases Γ
  case nil => exact True
  case cons h Γ₀ =>
    exact (h ∈ Δ) ∧ (IsSubCtx Γ₀ Δ)

inductive Valid : Ctx → Prop
  | nil : Valid []
  | cons {c : ctx_elem} : (c.var ∉ Γ) → Valid Γ → Valid (c :: Γ)

inductive Typing : Ctx → Term → Typ → Type
  | var : Valid (c :: Γ) → Typing (c :: Γ) (Term.var c.var) c.typ
  | ex : Typing (Γ ++ t₀ :: t₁ :: Δ) t T → Typing (Γ ++ t₁ :: t₀ :: Δ) t T
  | abs : Typing ((x∶A) :: Γ) t B → Typing Γ (λ[x].t) (A->B)
  | app : Typing Γ t₀ (A->B) → Typing Γ t₁ A → Typing Γ t₀{t₁} B

notation:max Γ "⊢" t "∶∶" A => Typing Γ t A


-- Weakening is admissible
def Weakening : (Γ ⊢ t ∶∶ A) → (Δ : Ctx) → (Γ ⊆ Δ) → (Valid Δ) → (Δ ⊢ t ∶∶ A) := by
  intro d
  induction d
  case var c₀ Γ₀ p₀ =>
    intro Δ d₀
    induction Δ
    case nil => sorry --contradiction
    case cons h₀ Δ₀ iH =>
      intro H
      have : Decidable (c₀ = h₀) :=
