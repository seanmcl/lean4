/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.Lemmas
import Std.Data.DTreeMap.Raw

/-!
# Dependent tree map lemmas

This file contains lemmas about `Std.Data.DTreeMap.Raw`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v

namespace Std.DTreeMap.Raw

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DTreeMap.Raw α β cmp}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

private theorem ext {t t' : Raw α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp]
theorem isEmpty_emptyc : (∅ : DTreeMap.Raw α β cmp).isEmpty :=
  Impl.isEmpty_empty

@[simp]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).isEmpty = false :=
  Impl.isEmpty_insert! h

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr h hab

@[simp]
theorem isEmpty_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).isEmpty = false :=
  Impl.isEmpty_insertIfNew! h

@[simp]
theorem contains_emptyc {k : α} : (∅ : Raw α β cmp).contains k = false :=
  Impl.contains_empty

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : Raw α β cmp) :=
  Impl.not_mem_empty

theorem contains_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → t.contains a = false :=
  Impl.contains_of_isEmpty h

theorem not_mem_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → a ∉ t :=
  Impl.not_mem_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  Impl.isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  Impl.isEmpty_eq_false_iff_exists_mem h

theorem isEmpty_iff_forall_contains [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  Impl.isEmpty_iff_forall_contains h

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  Impl.isEmpty_iff_forall_not_mem h

@[simp]
theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : Raw α β cmp).insert p.1 p.2 :=
  rfl

@[simp]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insert! h

@[simp]
theorem mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insert! h

theorem contains_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).contains k :=
  Impl.contains_insert!_self h

theorem mem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insert k v :=
  Impl.mem_insert!_self h

theorem contains_of_contains_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insert! h

theorem mem_of_mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.mem_of_mem_insert! h

@[simp]
theorem size_emptyc : (∅ : Raw α β cmp).size = 0 :=
  Impl.size_empty

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  Impl.isEmpty_eq_size_eq_zero h.out

theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  Impl.size_insert! h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert k v).size :=
  Impl.size_le_size_insert! h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size ≤ t.size + 1 :=
  Impl.size_insert!_le h

@[simp]
theorem erase_emptyc {k : α} :
    (∅ : Raw α β cmp).erase k = ∅ :=
  ext <| Impl.erase!_empty (instOrd := ⟨cmp⟩) (k := k)

@[simp]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  Impl.isEmpty_erase! h

@[simp]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  Impl.contains_erase! h

@[simp]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  Impl.mem_erase! h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  Impl.contains_of_contains_erase! h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  Impl.mem_of_mem_erase! h

theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  Impl.size_erase! h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  Impl.size_erase!_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  Impl.size_le_size_erase! h

@[simp]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).1 = t.contains k :=
  Impl.containsThenInsert!_fst h

@[simp]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| Impl.containsThenInsert!_snd h

@[simp]
theorem containsThenInsertIfNew_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  Impl.containsThenInsertIfNew!_fst h

@[simp]
theorem containsThenInsertIfNew_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| Impl.containsThenInsertIfNew!_snd h

@[simp]
theorem contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insertIfNew! h

@[simp]
theorem mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insertIfNew! h

theorem contains_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).contains k :=
  Impl.contains_insertIfNew!_self h

theorem mem_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insertIfNew k v :=
  Impl.mem_insertIfNew!_self h

theorem contains_of_contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insertIfNew! h

theorem mem_of_mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.contains_of_contains_insertIfNew! h

theorem size_insertIfNew [TransCmp cmp] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  Impl.size_insertIfNew! h

theorem size_le_size_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v).size :=
  Impl.size_le_size_insertIfNew! h

theorem size_insertIfNew_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  Impl.size_insertIfNew!_le h

@[simp]
theorem get?_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (∅ : DTreeMap α β cmp).get? a = none :=
  Impl.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none :=
  Impl.get?_of_isEmpty h

theorem get?_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v).get? a =
      if h : cmp k a = .eq then some (cast (congrArg β (compare_eq_iff_eq.mp h)) v) else t.get? a :=
  Impl.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get? k = some v :=
  Impl.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome :=
  Impl.contains_eq_isSome_get? h

theorem mem_iff_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  Impl.mem_iff_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none :=
  Impl.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  Impl.get?_eq_none h

theorem get?_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  Impl.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).get? k = none :=
  Impl.get?_erase!_self h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem get?_emptyc [TransCmp cmp] {a : α} :
    get? (∅ : Raw α β cmp) a = none :=
  Impl.Const.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → get? t a = none :=
  Impl.Const.get?_of_isEmpty h

theorem get?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert k v) a =
      if cmp k a = .eq then some v else get? t a :=
  Impl.Const.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get? (t.insert k v) k = some v :=
  Impl.Const.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (get? t a).isSome :=
  Impl.Const.contains_eq_isSome_get? h

theorem mem_iff_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (get? t a).isSome :=
  Impl.Const.mem_iff_isSome_get? h

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → get? t a = none :=
  Impl.Const.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → get? t a = none :=
  Impl.Const.get?_eq_none h

theorem get?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    get? (t.erase k) a = if cmp k a = .eq then none else get? t a :=
  Impl.Const.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    get? (t.erase k) k = none :=
  Impl.Const.get?_erase!_self h

theorem get?_eq_get? [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {a : α} : get? t a = t.get? a :=
  Impl.Const.get?_eq_get? h

theorem get?_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get? t a = get? t b :=
  Impl.Const.get?_congr h hab

end Const

theorem get_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v).get a h₁ =
      if h₂ : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (contains_of_contains_insert h h₁ h₂) :=
  Impl.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get k (contains_insert_self h) = v :=
  Impl.get_insert!_self h

@[simp]
theorem get_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (contains_of_contains_erase h h') :=
  Impl.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  Impl.get?_eq_some_get h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem get_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert k v) a h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (contains_of_contains_insert h h₁ h₂) :=
  Impl.Const.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get (t.insert k v) k (contains_insert_self h) = v :=
  Impl.Const.get_insert!_self h

@[simp]
theorem get_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    get (t.erase k) a h' = get t a (contains_of_contains_erase h h') :=
  Impl.Const.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    get? t a = some (get t a h') :=
  Impl.Const.get?_eq_some_get h

theorem get_eq_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    get t a h' = t.get a h' :=
  Impl.Const.get_eq_get h

theorem get_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) {h'} :
    get t a h' = get t b ((contains_congr h hab).symm.trans h') :=
  Impl.Const.get_congr h hab

end Const

@[simp]
theorem get!_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.isEmpty = true → t.get! a = default :=
  Impl.get!_of_isEmpty h

theorem get!_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)]
    {v : β k} : (t.insert k v).get! a =
      if h : cmp k a = .eq then cast (congrArg β (compare_eq_iff_eq.mp h)) v else t.get! a :=
  Impl.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)]
    {b : β a} : (t.insert a b).get! a = b :=
  Impl.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default :=
  Impl.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default :=
  Impl.get!_eq_default h

theorem get!_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  Impl.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase k).get! k = default :=
  Impl.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = true → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get!_of_contains h

theorem get?_eq_some_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! :=
  Impl.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] {h'} :
    t.get a h' = t.get! a :=
  Impl.get_eq_get! h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem get!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.Const.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → get! t a = default :=
  Impl.Const.get!_of_isEmpty h

theorem get!_insert [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert k v) a = if cmp k a = .eq then v else get! t a :=
  Impl.Const.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} {v : β} :
    get! (t.insert k v) k = v :=
  Impl.Const.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → get! t a = default :=
  Impl.Const.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → get! t a = default :=
  Impl.Const.get!_eq_default h

theorem get!_erase [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase k) a = if cmp k a = .eq then default else get! t a :=
  Impl.Const.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase k) k = default :=
  Impl.Const.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = true → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    a ∈ t → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = (get? t a).get! :=
  Impl.Const.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} {h'} :
    get t a h' = get! t a :=
  Impl.Const.get_eq_get! h

theorem get!_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = t.get! a :=
  Impl.Const.get!_eq_get! h

theorem get!_congr [TransCmp cmp] [Inhabited β] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get! t a = get! t b :=
  Impl.Const.get!_congr h hab

end Const

@[simp]
theorem getD_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    (∅ : DTreeMap α β cmp).getD a fallback = fallback :=
  Impl.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  Impl.getD_of_isEmpty h

theorem getD_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v).getD a fallback =
      if h : cmp k a = .eq then
        cast (congrArg β (compare_eq_iff_eq.mp h)) v
      else t.getD a fallback :=
  Impl.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert a b).getD a fallback = b :=
  Impl.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = false → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback h

theorem getD_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase k).getD a fallback = if cmp k a = .eq then fallback else t.getD a fallback :=
  Impl.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase k).getD k fallback = fallback :=
  Impl.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    {fallback : β a} : t.contains a = true → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback :=
  Impl.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} {h'} :
    t.get a h' = t.getD a fallback :=
  Impl.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default :=
  Impl.get!_eq_getD_default h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : Raw α β cmp) a fallback = fallback :=
  Impl.Const.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  Impl.Const.getD_of_isEmpty h

theorem getD_insert [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  Impl.Const.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  Impl.Const.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback h

theorem getD_erase [TransCmp cmp] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  Impl.Const.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  Impl.Const.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback :=
  Impl.Const.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} {h'} :
    get t a h' = getD t a fallback :=
  Impl.Const.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = getD t a default :=
  Impl.Const.get!_eq_getD_default h

theorem getD_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback :=
  Impl.Const.getD_eq_getD h

theorem getD_congr [TransCmp cmp] (h : t.WF) {a b : α} {fallback : β} (hab : cmp a b = .eq) :
    getD t a fallback = getD t b fallback :=
  Impl.Const.getD_congr h hab

end Const

end Std.DTreeMap.Raw
