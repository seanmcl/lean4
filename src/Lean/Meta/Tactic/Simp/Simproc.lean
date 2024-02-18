/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ScopedEnvExtension
import Lean.Compiler.InitAttr
import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

/--
Builtin simproc declaration extension state.

It contains:
- The discrimination tree keys for each simproc (including symbolic evaluation procedures) name.
- The actual procedure associated with a name.
-/
structure BuiltinSimprocs where
  keys  : HashMap Name (Array SimpTheoremKey) := {}
  procs : HashMap Name Simproc := {}
  deriving Inhabited

/--
This global reference is populated using the command `builtin_simproc_pattern%`.

This reference is then used to process the attributes `builtin_simproc` and `builtin_sevalproc`.
Both attributes need the keys and the actual procedure registered using the command `builtin_simproc_pattern%`.
-/
builtin_initialize builtinSimprocDeclsRef : IO.Ref BuiltinSimprocs ← IO.mkRef {}

structure SimprocDecl where
  declName : Name
  keys     : Array SimpTheoremKey
  deriving Inhabited

structure SimprocDeclExtState where
  builtin    : HashMap Name (Array SimpTheoremKey)
  newEntries : PHashMap Name (Array SimpTheoremKey) := {}
  deriving Inhabited

def SimprocDecl.lt (decl₁ decl₂ : SimprocDecl) : Bool :=
  Name.quickLt decl₁.declName decl₂.declName

builtin_initialize simprocDeclExt : PersistentEnvExtension SimprocDecl SimprocDecl SimprocDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { builtin := (← builtinSimprocDeclsRef.get).keys }
    addImportedFn   := fun _ => return { builtin := (← builtinSimprocDeclsRef.get).keys }
    addEntryFn      := fun s d => { s with newEntries := s.newEntries.insert d.declName d.keys }
    exportEntriesFn := fun s =>
      let result := s.newEntries.foldl (init := #[]) fun result declName keys => result.push { declName, keys }
      result.qsort SimprocDecl.lt
  }

def getSimprocDeclKeys? (declName : Name) : CoreM (Option (Array SimpTheoremKey)) := do
  let env ← getEnv
  let keys? ← match env.getModuleIdxFor? declName with
    | some modIdx => do
      let some decl := (simprocDeclExt.getModuleEntries env modIdx).binSearch { declName, keys := #[] } SimprocDecl.lt
        | pure none
      pure (some decl.keys)
    | none        => pure ((simprocDeclExt.getState env).newEntries.find? declName)
  if let some keys := keys? then
    return some keys
  else
    return (simprocDeclExt.getState env).builtin.find? declName

def isBuiltinSimproc (declName : Name) : CoreM Bool := do
  let s := simprocDeclExt.getState (← getEnv)
  return s.builtin.contains declName

def isSimproc (declName : Name) : CoreM Bool :=
  return (← getSimprocDeclKeys? declName).isSome

/--
Given a declaration name `declName`, store the discrimination tree keys and the actual procedure.

This method is invoked by the command `builtin_simproc_pattern%` elaborator.
-/
def registerBuiltinSimproc (declName : Name) (key : Array SimpTheoremKey) (proc : Simproc) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError s!"invalid builtin simproc declaration, it can only be registered during initialization")
  if (← builtinSimprocDeclsRef.get).keys.contains declName then
    throw (IO.userError s!"invalid builtin simproc declaration '{declName}', it has already been declared")
  builtinSimprocDeclsRef.modify fun { keys, procs } =>
    { keys := keys.insert declName key, procs := procs.insert declName proc }

def registerSimproc (declName : Name) (keys : Array SimpTheoremKey) : CoreM Unit := do
  let env ← getEnv
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid simproc declaration '{declName}', function declaration is in an imported module"
  if (← isSimproc declName) then
    throwError "invalid simproc declaration '{declName}', it has already been declared"
  modifyEnv fun env => simprocDeclExt.modifyState env fun s => { s with newEntries := s.newEntries.insert declName keys }

instance : BEq SimprocEntry where
  beq e₁ e₂ := e₁.declName == e₂.declName

instance : ToFormat SimprocEntry where
  format e := format e.declName

def Simprocs.erase (s : Simprocs) (declName : Name) : Simprocs :=
  { s with erased := s.erased.insert declName, simprocNames := s.simprocNames.erase declName }

/-- Builtin simprocs. -/
builtin_initialize builtinSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

/-- Builtin symbolic evaluation procedures. -/
builtin_initialize builtinSEvalprocsRef : IO.Ref Simprocs ← IO.mkRef {}

abbrev SimprocExtension := ScopedEnvExtension SimprocOLeanEntry SimprocEntry Simprocs

unsafe def getSimprocFromDeclImpl (declName : Name) : ImportM Simproc := do
  let ctx ← read
  match ctx.env.evalConstCheck Simproc ctx.opts ``Lean.Meta.Simp.Simproc declName with
  | .ok proc  => return proc
  | .error ex => throw (IO.userError ex)

@[implemented_by getSimprocFromDeclImpl]
opaque getSimprocFromDecl (declName: Name) : ImportM Simproc

def toSimprocEntry (e : SimprocOLeanEntry) : ImportM SimprocEntry := do
  return { toSimprocOLeanEntry := e, proc := (← getSimprocFromDecl e.declName) }

def eraseSimprocAttr (ext : SimprocExtension) (declName : Name) : AttrM Unit := do
  let s := ext.getState (← getEnv)
  unless s.simprocNames.contains declName do
    throwError "'{declName}' does not have [simproc] attribute"
  modifyEnv fun env => ext.modifyState env fun s => s.erase declName

def addSimprocAttr (ext : SimprocExtension) (declName : Name) (kind : AttributeKind) (post : Bool) : CoreM Unit := do
  let proc ← getSimprocFromDecl declName
  let some keys ← getSimprocDeclKeys? declName |
    throwError "invalid [simproc] attribute, '{declName}' is not a simproc"
  ext.add { declName, post, keys, proc } kind

/--
Implements attributes `builtin_simproc` and `builtin_sevalproc`.
-/
def addSimprocBuiltinAttrCore (ref : IO.Ref Simprocs) (declName : Name) (post : Bool) (proc : Simproc) : IO Unit := do
  let some keys := (← builtinSimprocDeclsRef.get).keys.find? declName |
    throw (IO.userError "invalid [builtin_simproc] attribute, '{declName}' is not a builtin simproc")
  if post then
    ref.modify fun s => { s with post := s.post.insertCore keys { declName, keys, post, proc } }
  else
    ref.modify fun s => { s with pre := s.pre.insertCore keys { declName, keys, post, proc } }

def addSimprocBuiltinAttr (declName : Name) (post : Bool) (proc : Simproc) : IO Unit :=
  addSimprocBuiltinAttrCore builtinSimprocsRef declName post proc

def addSEvalprocBuiltinAttr (declName : Name) (post : Bool) (proc : Simproc) : IO Unit :=
  addSimprocBuiltinAttrCore builtinSEvalprocsRef declName post proc

def Simprocs.add (s : Simprocs) (declName : Name) (post : Bool) : CoreM Simprocs := do
  let proc ←
    try
      getSimprocFromDecl declName
    catch e =>
      if (← isBuiltinSimproc declName) then
        let some proc := (← builtinSimprocDeclsRef.get).procs.find? declName
          | throwError "invalid [simproc] attribute, '{declName}' is not a simproc"
        pure proc
      else
        throw e
  let some keys ← getSimprocDeclKeys? declName |
    throwError "invalid [simproc] attribute, '{declName}' is not a simproc"
  if post then
    return { s with post := s.post.insertCore keys { declName, keys, post, proc } }
  else
    return { s with pre := s.pre.insertCore keys { declName, keys, post, proc } }

def SimprocEntry.try (s : SimprocEntry) (numExtraArgs : Nat) (e : Expr) : SimpM Step := do
  let mut extraArgs := #[]
  let mut e := e
  for _ in [:numExtraArgs] do
    extraArgs := extraArgs.push e.appArg!
    e := e.appFn!
  extraArgs := extraArgs.reverse
  let s ← s.proc e
  s.addExtraArgs extraArgs

def simprocCore (post : Bool) (s : SimprocTree) (erased : PHashSet Name) (e : Expr) : SimpM Step := do
  let candidates ← s.getMatchWithExtra e (getDtConfig (← getConfig))
  if candidates.isEmpty then
    let tag := if post then "post" else "pre"
    trace[Debug.Meta.Tactic.simp] "no {tag}-simprocs found for {e}"
    return .continue
  else
    let mut e  := e
    let mut proof? : Option Expr := none
    let mut found := false
    let mut cache := true
    for (simprocEntry, numExtraArgs) in candidates do
      unless erased.contains simprocEntry.declName do
        let s ← simprocEntry.try numExtraArgs e
        match s with
        | .visit r =>
          trace[Debug.Meta.Tactic.simp] "simproc result {e} => {r.expr}"
          recordSimpTheorem (.decl simprocEntry.declName post)
          return .visit (← mkEqTransOptProofResult proof? cache r)
        | .done r =>
          trace[Debug.Meta.Tactic.simp] "simproc result {e} => {r.expr}"
          recordSimpTheorem (.decl simprocEntry.declName post)
          return .done (← mkEqTransOptProofResult proof? cache r)
        | .continue (some r) =>
          trace[Debug.Meta.Tactic.simp] "simproc result {e} => {r.expr}"
          recordSimpTheorem (.decl simprocEntry.declName post)
          e := r.expr
          proof? ← mkEqTrans? proof? r.proof?
          cache := cache && r.cache
          found := true
        | .continue none =>
          pure ()
    if found then
      return .continue (some { expr := e, proof?, cache })
    else
      return .continue

abbrev SimprocsArray := Array Simprocs

def SimprocsArray.add (ss : SimprocsArray) (declName : Name) (post : Bool) : CoreM SimprocsArray :=
  if ss.isEmpty then
    let s : Simprocs := {}
    return #[ (← s.add declName post) ]
  else
    ss.modifyM 0 fun s => s.add declName post

def SimprocsArray.erase (ss : SimprocsArray) (declName : Name) : SimprocsArray :=
  ss.map fun s => s.erase declName

def SimprocsArray.isErased (ss : SimprocsArray) (declName : Name) : Bool :=
  ss.any fun s => s.erased.contains declName

def simprocArrayCore (post : Bool) (ss : SimprocsArray) (e : Expr) : SimpM Step := do
  let mut found := false
  let mut e  := e
  let mut proof? : Option Expr := none
  let mut cache := true
  for s in ss do
    match (← simprocCore (post := post) (if post then s.post else s.pre) s.erased e) with
    | .visit r => return .visit (← mkEqTransOptProofResult proof? cache r)
    | .done r =>  return .done (← mkEqTransOptProofResult proof? cache r)
    | .continue none => pure ()
    | .continue (some r) =>
      e := r.expr
      proof? ← mkEqTrans? proof? r.proof?
      cache := cache && r.cache
      found := true
  if found then
    return .continue (some { expr := e, proof? })
  else
    return .continue

register_builtin_option simprocs : Bool := {
  defValue := true
  descr    := "Enable/disable `simproc`s (simplification procedures)."
}

def userPreSimprocs (s : SimprocsArray) : Simproc := fun e => do
  unless simprocs.get (← getOptions) do return .continue
  simprocArrayCore (post := false) s e

def userPostSimprocs (s : SimprocsArray) : Simproc := fun e => do
  unless simprocs.get (← getOptions) do return .continue
  simprocArrayCore (post := true) s e

def mkSimprocExt (name : Name := by exact decl_name%) (ref? : Option (IO.Ref Simprocs)) : IO SimprocExtension :=
  registerScopedEnvExtension {
    name          := name
    mkInitial     :=
      if let some ref := ref? then
        ref.get
      else
        return {}
    ofOLeanEntry  := fun _ => toSimprocEntry
    toOLeanEntry  := fun e => e.toSimprocOLeanEntry
    addEntry      := fun s e =>
      if e.post then
        { s with post := s.post.insertCore e.keys e }
      else
        { s with pre := s.pre.insertCore e.keys e }
  }

def mkSimprocAttr (attrName : Name) (attrDescr : String) (ext : SimprocExtension) (name : Name) : IO Unit := do
  registerBuiltinAttribute {
    ref   := name
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind =>
      let go : MetaM Unit := do
        let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
        addSimprocAttr ext declName attrKind post
      discard <| go.run {} {}
    erase := eraseSimprocAttr ext
  }

abbrev SimprocExtensionMap := HashMap Name SimprocExtension

builtin_initialize simprocExtensionMapRef : IO.Ref SimprocExtensionMap ← IO.mkRef {}

def registerSimprocAttr (attrName : Name) (attrDescr : String) (ref? : Option (IO.Ref Simprocs))
    (name : Name := by exact decl_name%) : IO SimprocExtension := do
  let ext ← mkSimprocExt name ref?
  mkSimprocAttr attrName attrDescr ext name
  simprocExtensionMapRef.modify fun map => map.insert attrName ext
  return ext

builtin_initialize simprocExtension : SimprocExtension ← registerSimprocAttr `simprocAttr "Simplification procedure" (some builtinSimprocsRef)

builtin_initialize simprocSEvalExtension : SimprocExtension ← registerSimprocAttr `sevalprocAttr "Symbolic evaluator procedure" (some builtinSEvalprocsRef)

private def addBuiltin (declName : Name) (stx : Syntax) (addDeclName : Name) : AttrM Unit := do
  let go : MetaM Unit := do
    let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
    let val := mkAppN (mkConst addDeclName) #[toExpr declName, toExpr post, mkConst declName]
    let initDeclName ← mkFreshUserName (declName ++ `declare)
    declareBuiltin initDeclName val
  go.run' {}

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `simprocBuiltinAttr
    descr           := "Builtin simplification procedure"
    applicationTime := AttributeApplicationTime.afterCompilation
    erase           := fun _ => throwError "Not implemented yet, [-builtin_simproc]"
    add             := fun declName stx _ => addBuiltin declName stx ``addSimprocBuiltinAttr
  }

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `sevalprocBuiltinAttr
    descr           := "Builtin symbolic evaluation procedure"
    applicationTime := AttributeApplicationTime.afterCompilation
    erase           := fun _ => throwError "Not implemented yet, [-builtin_sevalproc]"
    add             := fun declName stx _ => addBuiltin declName stx ``addSEvalprocBuiltinAttr
  }

def getSimprocs : CoreM Simprocs :=
  return simprocExtension.getState (← getEnv)

def getSEvalSimprocs : CoreM Simprocs :=
  return simprocSEvalExtension.getState (← getEnv)

def getSimprocExtensionCore? (attrName : Name) : IO (Option SimprocExtension) :=
  return (← simprocExtensionMapRef.get).find? attrName

def simpAttrNameToSimprocAttrName (attrName : Name) : Name :=
  if attrName == `simp then `simprocAttr
  else if attrName == `seval then `sevalprocAttr
  else attrName.appendAfter "_proc"

/--
Try to retrieve the simproc set using the `simp` or `simproc` attribute names.
Recall that when we declare a `simp` set using `register_simp_attr`, an associated
`simproc` set is automatically created. We use the function `simpAttrNameToSimprocAttrName` to
find the `simproc` associated with the `simp` attribute.
-/
def getSimprocExtension? (simprocAttrNameOrsimpAttrName : Name)
    : IO (Option SimprocExtension) := do
  let some ext ← getSimprocExtensionCore? simprocAttrNameOrsimpAttrName
    | getSimprocExtensionCore? (simpAttrNameToSimprocAttrName simprocAttrNameOrsimpAttrName)
  return some ext

def SimprocExtension.getSimprocs (ext : SimprocExtension) : CoreM Simprocs :=
  return ext.getState (← getEnv)

end Lean.Meta.Simp
