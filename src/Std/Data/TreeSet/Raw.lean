/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.TreeMap.Raw
import Std.Data.TreeSet.Basic

/-
# Tree sets with unbundled well-formedness invariant

This file develops the type `Std.TreeSet.Raw` of tree sets with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.TreeSet.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `TreeSet` over `TreeSet.Raw`.

Lemmas about the operations on `Std.TreeSet.Raw` will be available in the module
`Std.Data.TreeSet.RawLemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

namespace TreeSet

/--
Tree sets without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `TreeSet`
over `TreeSet.Raw`. Lemmas about the operations on `Std.TreeSet.Raw` are available in the
module `Std.Data.TreeSet.RawLemmas`.

A tree set stores elements of a certain type in a certain order. It depends on a comparator function
that defines an ordering on the keys and provides efficient order-dependent queries, such as
retrieval of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass).
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
is less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e only one of them
can be contained in a single tree set at the same time.

To avoid expensive copies, users should make sure that the tree set is used linearly.

Internally, the tree sets are represented as size-bounded trees, a type of self-balancing binary
search tree with efficient order statistic lookups.
-/
structure Raw (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree set. -/
  inner : TreeMap.Raw α Unit cmp

namespace Raw

/--
Well-formedness predicate for tree sets. Users of `TreeSet` will not need to interact with
this. Users of `TreeSet.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that set operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
structure WF (t : Raw α cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : t.inner.WF

instance {t : Raw α cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

@[inline, inherit_doc TreeSet.empty]
def empty : Raw α cmp :=
  ⟨TreeMap.Raw.empty⟩

instance : EmptyCollection (Raw α cmp) where
  emptyCollection := empty

instance : Inhabited (Raw α cmp) where
  default := ∅

@[inline, inherit_doc TreeSet.empty]
def insert (l : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨l.inner.insertIfNew a ()⟩

instance : Singleton α (Raw α cmp) where
  singleton e := empty.insert e

instance : Insert α (Raw α cmp) where
  insert e s := s.insert e

instance : LawfulSingleton α (Raw α cmp) where
  insert_emptyc_eq _ := rfl

@[inline, inherit_doc TreeSet.empty]
def containsThenInsert (t : Raw α cmp) (a : α) : Bool × Raw α cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a ()
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc TreeSet.empty]
def contains (l : Raw α cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (Raw α cmp) where
  mem t a := t.contains a

instance {t : Raw α cmp} {a : α} : Decidable (a ∈ t) :=
  inferInstanceAs <| Decidable (t.contains a)

@[inline, inherit_doc TreeSet.empty]
def size (t : Raw α cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc TreeSet.empty]
def isEmpty (t : Raw α cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc TreeSet.empty]
def erase (t : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨t.inner.erase a⟩

universe w w₂
variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc TreeSet.empty]
def filter (f : α → Bool) (t : Raw α cmp) : Raw α cmp :=
  ⟨t.inner.filter fun a _ => f a⟩

@[inline, inherit_doc TreeSet.empty]
def foldlM (f : δ → (a : α) → m δ) (init : δ) (t : Raw α cmp) : m δ :=
  t.inner.foldlM (fun c a _ => f c a) init

@[inline, inherit_doc TreeSet.empty]
def foldl (f : δ → (a : α) → δ) (init : δ) (t : Raw α cmp) : δ :=
  t.inner.foldl (fun c a _ => f c a) init

@[inline, inherit_doc TreeSet.empty]
def forM (f : α → m PUnit) (t : Raw α cmp) : m PUnit :=
  t.inner.forM (fun a _ => f a)

@[inline, inherit_doc TreeSet.empty]
def forIn (f : α → δ → m (ForInStep δ)) (init : δ) (t : Raw α cmp) : m δ :=
  t.inner.forIn (fun a _ c => f a c) init

instance : ForM m (Raw α cmp) α where
  forM t f := t.forM f

instance {t : Type w → Type w} : ForIn t (Raw α cmp) α where
  forIn t init f := t.forIn (fun a acc => f a acc) init

@[inline, inherit_doc TreeSet.empty]
def any (t : Raw α cmp) (p : α → Bool) : Bool :=
  t.inner.any (fun a _ => p a)

@[inline, inherit_doc TreeSet.empty]
def all (t : Raw α cmp) (p : α → Bool) : Bool :=
  t.inner.all (fun a _ => p a)

@[inline, inherit_doc TreeSet.empty]
def toList (t : Raw α cmp) : List α :=
  t.inner.inner.inner.foldr (fun l a _ => a :: l) ∅

@[inline, inherit_doc TreeSet.empty]
def ofList (l : List α) (cmp : α → α → Ordering) : Raw α cmp :=
  l.foldl (fun r a => r.insert a) ∅

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-06")]
def fromList (l : List α) (cmp : α → α → Ordering) : Raw α cmp :=
  ofList l cmp

@[inline, inherit_doc TreeSet.empty]
def toArray (t : Raw α cmp) : Array α :=
  t.foldl (init := #[]) fun acc k => acc.push k

@[inline, inherit_doc TreeSet.empty]
def ofArray (l : Array α) (cmp : α → α → Ordering) : Raw α cmp :=
  l.foldl (init := ∅) (fun t a => t.insert a)

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-06")]
def fromArray (l : Array α) (cmp : α → α → Ordering) : Raw α cmp :=
  ofArray l cmp

@[inline, inherit_doc TreeSet.empty]
def merge (t₁ t₂ : Raw α cmp) : Raw α cmp :=
  ⟨TreeMap.Raw.mergeWith (fun _ _ _ => ()) t₁.inner t₂.inner⟩

@[inline, inherit_doc TreeSet.empty]
def eraseMany {ρ} [ForIn Id ρ α] (t : Raw α cmp) (l : ρ) : Raw α cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] : Repr (Raw α cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeSet.Raw.ofList " ++ repr m.toList) prec

end Raw

end TreeSet

end Std
