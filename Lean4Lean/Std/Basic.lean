import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas
import Std.Data.HashMap.Basic

theorem funext_iff {β : α → Sort u} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h _ ↦ h ▸ rfl) funext

protected theorem Nat.lt_add_left (a b c : Nat) (h : a < c) : a < b + c :=
  Nat.add_comm .. ▸ Nat.lt_add_right _ _ _ h

protected theorem Nat.le_iff_exists_add {a b : Nat} : a ≤ b ↔ ∃ c, b = a + c :=
  ⟨fun h => ⟨_, (Nat.add_sub_cancel' h).symm⟩, fun ⟨_, h⟩ => h ▸ Nat.le_add_right ..⟩

protected theorem Nat.le_iff_exists_add' {a b : Nat} : a ≤ b ↔ ∃ c, b = c + a := by
  simp [Nat.add_comm, Nat.le_iff_exists_add]

protected theorem List.Forall₂.rfl
    {R : α → α → Prop} {l : List α} (h : ∀ a ∈ l, R a a) : l.Forall₂ R l := by
  induction l with
  | nil => constructor
  | cons _ _ ih => simp at h; exact .cons h.1 (ih h.2)

theorem List.map_id' {f : α → α} (l : List α) (h : ∀ x ∈ l, f x = x) : map f l = l := by
  induction l <;> simp_all

def List.All (P : α → Prop) : List α → Prop
  | [] => True
  | a::as => P a ∧ as.All P

theorem List.All.imp {P Q : α → Prop} (h : ∀ a, P a → Q a) : ∀ {l : List α}, l.All P → l.All Q
  | [] => id
  | _::_ => And.imp (h _) (List.All.imp h)

instance [BEq α] [LawfulBEq α] : PartialEquivBEq α where
  symm h := by simp at *; exact h.symm
  trans h1 h2 := by simp at *; exact h1.trans h2

instance [BEq α] [LawfulBEq α] [Hashable α] : Std.HashMap.LawfulHashable α where
  hash_eq h := by simp at *; subst h; rfl

instance : LawfulBEq Lean.FVarId where
  eq_of_beq := @fun ⟨a⟩ ⟨b⟩ h => by cases LawfulBEq.eq_of_beq (α := Lean.Name) h; rfl
  rfl := LawfulBEq.rfl (α := Lean.Name)

theorem beq_comm [BEq α] [PartialEquivBEq α] (a b : α) : (a == b) = (b == a) :=
  Bool.eq_iff_iff.2 ⟨PartialEquivBEq.symm, PartialEquivBEq.symm⟩