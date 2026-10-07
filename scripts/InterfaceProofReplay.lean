module
public import Solution
public import DensityInterfaces.PositiveCount
public meta import Lean.Replay

@[expose] public section

/- Receiver-side verification harness, not an imported mathematical premise.
Run from the repository root:
  scripts/with-lean.sh lake env lean -DwarningAsError=true ../scripts/InterfaceProofReplay.lean

Traverse declaration types and bodies, close mutual inductives and constructors,
reject unsafe/partial declarations and nonstandard assumptions, then replay the
entire closure into an empty environment through the installed Lean kernel.

-/

set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env ← liftIO <| importModules #[{ module := `Solution },
    { module := `DensityInterfaces.PositiveCount }] {} (level := .private)
  let roots : Array Name := #[
    ``DensityInterfaces.positive_count_density_bound,
    ``DensityThreeQuarters.density_bound,
    ``DensityThreeQuarters.v1.challenge_density_bound,
    ``DensityInterfaces.ieantn_order_eq,
    ``DensityInterfaces.ieantn_count_summable,
    ``DensityInterfaces.ieantn_count_le,
    ``DensityInterfaces.antedb_shifted_density_bound,
    ``DensityInterfaces.antedb_density_exponent_two,
    ``MathCollab.Density.zeta_density_bound]
  let mut pending := roots
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if declarations.contains name then
      continue
    let some ci := env.find? name | throwError "Missing proof dependency {name}"
    if ci.isUnsafe || ci.isPartial then
      throwError "Unsafe or partial declaration in mathematical closure: {name}"
    declarations := declarations.insert name ci
    for dependency in ci.getUsedConstantsAsSet do
      pending := pending.push dependency
    match ci with
    | .inductInfo info =>
      for other in info.all do
        pending := pending.push other
      for ctor in info.ctors do
        pending := pending.push ctor
    | .quotInfo _ => pending := pending.push ``Eq
    | _ => pure ()
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : Array Name := #[]
  for (name,ci) in declarations.toList do
    if ci.isAxiom then
      unless allowed.contains name do
        throwError "Unexpected axiom in proof closure: {name}"
      axioms := axioms.push name
  logInfo m!"Proof closure: {declarations.size} declarations. Axioms: {axioms}"
  let names := (declarations.toList.map (fun (n,_) => n.toString)).mergeSort
  liftIO <| IO.FS.createDirAll "../build"
  liftIO <| IO.FS.writeFile "../build/interface-proof-dependencies.txt"
    (String.intercalate "\n" names ++ "\n")
  let fresh ← mkEmptyEnvironment
  let checked ← fresh.toKernelEnv.replay declarations
  for root in roots do
    unless (checked.find? root).isSome do
      throwError "Replay omitted root {root}"
  logInfo m!"FRESH PROOF CLOSURE REPLAY PASS: {declarations.size} declarations, {roots.size} roots."
