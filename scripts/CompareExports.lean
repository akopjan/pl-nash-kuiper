module

public import Lake.Check.Compare
public import Lake.Check.Axioms

/-!
# Read-only comparison of two freshly generated exports

This operator program imports no project module. It reads the NDJSON exports
as data and calls the toolchain's own statement/dependency comparison and
axiom audit. It does not build the project, load its object files, change
Comparator's sandbox, or claim a sandboxed Comparator acceptance certificate.
-/

private def permitted : Array Lean.Name :=
  #["propext", "Quot.sound", "Classical.choice"].map String.toName

private def targets : Array Lean.Name :=
  #["PLGeometry.akopyan_pl_nash_kuiper"].map String.toName

private def primitives : Array Lean.Name :=
  #["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
    "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk", "Char",
    "optParam", "autoParam", "semiOutParam", "outParam"].map String.toName

public def main (args : List String) : IO UInt32 := do
  let [challengePath, solutionPath] := args
    | IO.eprintln "Usage: lean --run scripts/CompareExports.lean CHALLENGE.ndjson SOLUTION.ndjson"
      return 2
  let challenge ← LeanExport.parseStream <| .ofHandle
    (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle
    (← IO.FS.Handle.mk solutionPath .read)
  match Lake.Check.compareAt challenge solution (targets ++ permitted) #[] primitives with
  | .error message =>
    IO.eprintln message
    return 1
  | .ok _ => pure ()
  match Lake.Check.checkAxioms solution targets #[] permitted with
  | .error message =>
    IO.eprintln message
    return 1
  | .ok _ => pure ()
  IO.println "Original target statements and all referenced definitions match."
  IO.println "Transitive target dependencies use only propext, Quot.sound and Classical.choice."
  IO.println "Read-only export comparison passed; sandboxed Comparator is a separate check."
  return 0
