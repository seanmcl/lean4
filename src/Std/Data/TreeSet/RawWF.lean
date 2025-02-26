/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.TreeMap.RawWF
import Std.Data.TreeSet.AdditionalOperations
import Std.Data.TreeSet.Raw

/-!
# Well-formedness proofs for raw tree sets

This file contains well-formedness proofs about `Std.Data.TreeSet.Raw`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.TreeSet.Raw.WF

open TreeMap.Raw renaming WF → InnerWF

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeSet.Raw α cmp}

variable {t : Raw α cmp}

theorem empty : (empty : Raw α cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨InnerWF.empty⟩

theorem emptyc : (∅ : Raw α cmp).WF :=
  empty

theorem erase [TransCmp cmp] {a} (h : t.WF) :
    WF (t.erase a) :=
  ⟨InnerWF.erase h⟩

theorem insert [TransCmp cmp] {a} (h : t.WF) :
    WF (t.insert a) :=
  ⟨InnerWF.insertIfNew h⟩

theorem containsThenInsert [TransCmp cmp] {a} (h : t.WF) :
    WF (t.containsThenInsert a).2 :=
  ⟨InnerWF.containsThenInsertIfNew h⟩

theorem filter [TransCmp cmp] {f} (h : t.WF) :
    WF (t.filter f) :=
  ⟨InnerWF.filter h⟩

theorem partition_fst [TransCmp cmp] {f} :
    WF (t.partition f).fst :=
  ⟨InnerWF.partition_fst⟩

theorem partition_snd [TransCmp cmp] {f} :
    WF (t.partition f).snd :=
  ⟨InnerWF.partition_snd⟩

theorem eraseMany [TransCmp cmp] {ρ} [ForIn Id ρ α] {l : ρ} {t : Raw α cmp} (h : t.WF) :
    WF (t.eraseMany l) :=
  ⟨InnerWF.eraseMany h⟩

theorem insertMany [TransCmp cmp] {ρ} [ForIn Id ρ α] {l : ρ} {t : Raw α cmp}
    (h : t.WF) : WF (t.insertMany l) :=
  ⟨InnerWF.insertManyIfNewUnit h⟩

theorem ofList [TransCmp cmp] {l : List α} :
    (Raw.ofList l cmp).WF :=
  ⟨InnerWF.unitOfList⟩

theorem ofArray [TransCmp cmp] {l : Array α} :
    (Raw.ofArray l cmp).WF :=
  ⟨InnerWF.unitOfArray⟩

end Std.TreeSet.Raw.WF
