/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Basic
import Std.Data.DTreeMap.Internal.WF

/-!
# Additional dependent tree map operations

This file defines more operations on `Std.DTreeMap`.
We currently do not provide lemmas for these functions.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {cmp : α → α → Ordering}

namespace Std.DTreeMap

namespace Raw

/--
Updates the values of the map by applying the given function to all mappings, keeping
only those mappings where the function returns `some` value.
-/
def filterMap (f : (a : α) → β a → Option (γ a)) (t : Raw α β cmp) : Raw α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filterMap! f⟩

variable {γ : α → Type w} in
/-- Updates the values of the map by applying the given function to all mappings. -/
@[inline]
def map (f : (a : α) → β a → γ a) (t : Raw α β cmp) : Raw α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f⟩

end Raw

variable {γ : α → Type w} in
@[inline, inherit_doc Raw.filterMap]
def filterMap (f : (a : α) → β a → Option (γ a)) (t : DTreeMap α β cmp) : DTreeMap α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filterMap f t.wf.balanced |>.impl, t.wf.filterMap⟩

variable {γ : α → Type w} in
@[inline, inherit_doc Raw.map]
def map (f : (a : α) → β a → γ a) (t : DTreeMap α β cmp) : DTreeMap α γ cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.map f, t.wf.map⟩

end Std.DTreeMap
