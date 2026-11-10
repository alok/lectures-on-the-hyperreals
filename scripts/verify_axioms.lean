import LecturesOnTheHyperreals
import Lean

/-!
# Kernel Axiom & `sorryAx` Verification Script

Run with:
```bash
lake env lean scripts/verify_axioms.lean
```

Iterates over every non-internal `Goldblatt.*` constant in the compiled Lean 4 kernel environment
and verifies that:
1. **Zero** declarations depend transitively on `sorryAx`, and
2. **Zero** custom axioms exist anywhere in the transitive axiom closure — only Lean 4's three
   foundational classical axioms (`propext`, `Classical.choice`, `Quot.sound`) are used.
-/

open Lean

#eval show MetaM Unit from do
  let env ← getEnv
  let allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut totalDecls : Nat := 0
  let mut thmCount : Nat := 0
  let mut defCount : Nat := 0
  let mut sorryUsers : Array Name := #[]
  let mut disallowedAxioms : Array Name := #[]
  let allEntries := env.constants.map₁.toList ++ env.constants.map₂.toList
  for (name, cinfo) in allEntries do
    if (`Goldblatt).isPrefixOf name && !name.isInternalDetail then
      totalDecls := totalDecls + 1
      match cinfo with
      | .thmInfo _ => thmCount := thmCount + 1
      | .defnInfo _ | .inductInfo _ | .opaqueInfo _ => defCount := defCount + 1
      | .axiomInfo _ => disallowedAxioms := disallowedAxioms.push name
      | _ => pure ()
      let axs ← collectAxioms name
      if axs.contains ``sorryAx then
        sorryUsers := sorryUsers.push name
      for ax in axs do
        if !allowedAxioms.contains ax && !disallowedAxioms.contains ax then
          disallowedAxioms := disallowedAxioms.push ax
  IO.println s!"Verified `Goldblatt.*` kernel declarations : {totalDecls}"
  IO.println s!"  Theorems / lemmas                        : {thmCount}"
  IO.println s!"  Definitions / inductives / structures    : {defCount}"
  IO.println s!"  Declarations using `sorryAx`             : {sorryUsers.size}"
  IO.println s!"  Disallowed / custom axioms               : {disallowedAxioms.size}"
  if !sorryUsers.isEmpty || !disallowedAxioms.isEmpty then
    throwError s!"Audit failed! sorryUsers={sorryUsers}, disallowedAxioms={disallowedAxioms}"
  IO.println "KERNEL AUDIT PASSED: 0 sorryAx, 0 custom axioms (only propext, Classical.choice, Quot.sound)."
