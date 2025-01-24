/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.DRBMap
import Lake.Util.RBArray
import Lake.Util.Family
import Lake.Util.Store
import Std.Data.DTreeMap.Basic

open Lean Std
namespace Lake

instance [Monad m] [LawfulCmpEq κ cmp] : MonadDStore κ β (StateT (DTreeMap κ β cmp) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

instance [MonadLiftT (ST ω) m] [Monad m] [LawfulCmpEq κ cmp] : MonadDStore κ β (StateRefT' ω (DTreeMap κ β cmp) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

instance [Monad m] : MonadStore κ α (StateT (RBMap κ α cmp) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

instance [MonadLiftT (ST ω) m] [Monad m] : MonadStore κ α (StateRefT' ω (RBMap κ α cmp) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

instance [Monad m] : MonadStore κ α (StateT (RBArray κ α cmp) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

instance [MonadLiftT (ST ω) m] [Monad m] : MonadStore κ α (StateRefT' ω (RBArray κ α cmp) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

-- uses the eagerly specialized `RBMap` functions in `NameMap`
instance [Monad m] : MonadStore Name α (StateT (NameMap α) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

instance [MonadLiftT (ST ω) m] [Monad m] : MonadStore Name α (StateRefT' ω (NameMap α) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

@[inline] instance [MonadDStore κ β m] [t : FamilyOut β k α] : MonadStore1Of k α m where
  fetch? := cast (by rw [t.family_key_eq_type]) <| fetch? (m := m) k
  store a := store k <| cast t.family_key_eq_type.symm a
