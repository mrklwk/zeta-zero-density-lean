module
public import MathCollab
public import Solution
public import DensityInterfaces.PositiveCount
public import Lean

@[expose] public section

-- Exhaustive production-declaration audit, including private helpers and generated equations.
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  liftIO enableInitializersExecution
  let env ← liftIO <| importModules #[{ module := `MathCollab }, { module := `Solution },
    { module := `DensityInterfaces.PositiveCount }] {} (loadExts := true) (level := .private)
  let localModules : List Name := [
    `DensityInterfaces.IEANTNAdapter,
    `DensityInterfaces.ANTEDBAdapter,
    `DensityInterfaces.ClosedCount,
    `DensityInterfaces.PositiveCount,
    `DensityInterfaces.IEANTNSolution,
    `IEANTN.Vocabulary.Zeta,
    `IEANTN.Nodes.DensityThreeQuarters.v1.Conclusions,
    `Solution,
    `GuthMaynard.SecondDerivative,
    `GuthMaynard.SecondOrderMeanValue,
    `GuthMaynard.VanDerCorput,
    `GuthMaynard.Weyl,
    `GuthMaynard.WeylExplicit,
    `GuthMaynard.WeylZeta,
    `MathCollab.Density.AbelZetaGrowth,
    `MathCollab.Density.AllFrequency,
    `MathCollab.Density.AnalyticTransforms,
    `MathCollab.Density.BandEnergy,
    `MathCollab.Density.BootstrapAbsorption,
    `MathCollab.Density.BootstrapDomain,
    `MathCollab.Density.BootstrapShell,
    `MathCollab.Density.BootstrapShells,
    `MathCollab.Density.BootstrapSupremum,
    `MathCollab.Density.Comparison,
    `MathCollab.Density.ComparisonAlgebra,
    `MathCollab.Density.ComparisonCutoff,
    `MathCollab.Density.ComparisonExpansion,
    `MathCollab.Density.CompletePairs,
    `MathCollab.Density.CutoffTransforms,
    `MathCollab.Density.DensityConclusion,
    `MathCollab.Density.DensityDyadicSummation,
    `MathCollab.Density.DensityExponentAccounting,
    `MathCollab.Density.DensitySlabBound,
    `MathCollab.Density.DensityTheorem,
    `MathCollab.Density.DetectorAdmissibility,
    `MathCollab.Density.DetectorBinomial,
    `MathCollab.Density.DetectorBlockExpansion,
    `MathCollab.Density.DetectorContour,
    `MathCollab.Density.DetectorConvolution,
    `MathCollab.Density.DetectorDyadic,
    `MathCollab.Density.DetectorError,
    `MathCollab.Density.DetectorEstimates,
    `MathCollab.Density.DetectorFamilyScales,
    `MathCollab.Density.DetectorGamma,
    `MathCollab.Density.DetectorIdentity,
    `MathCollab.Density.DetectorMellin,
    `MathCollab.Density.DetectorNormalization,
    `MathCollab.Density.DetectorParameters,
    `MathCollab.Density.DetectorPowerScales,
    `MathCollab.Density.DetectorPoweredHeight,
    `MathCollab.Density.DetectorPoweredPieces,
    `MathCollab.Density.DetectorTaylorFamily,
    `MathCollab.Density.DetectorTruncation,
    `MathCollab.Density.DivisorGrowth,
    `MathCollab.Density.DyadicBlocks,
    `MathCollab.Density.FiniteDetector,
    `MathCollab.Density.FixedBandError,
    `MathCollab.Density.FixedDetectorCover,
    `MathCollab.Density.GammaMellin,
    `MathCollab.Density.GammaStrip,
    `MathCollab.Density.IndexedZeroLargeValues,
    `MathCollab.Density.LargeValueDefinitions,
    `MathCollab.Density.LargeValues,
    `MathCollab.Density.LargeValuesOptimization,
    `MathCollab.Density.LocalCover,
    `MathCollab.Density.LocalZeroCount,
    `MathCollab.Density.MellinKernel,
    `MathCollab.Density.MollifierBound,
    `MathCollab.Density.MollifierCoefficients,
    `MathCollab.Density.MollifierDirichlet,
    `MathCollab.Density.Oscillatory,
    `MathCollab.Density.Packing,
    `MathCollab.Density.PoweredDetectorFamily,
    `MathCollab.Density.ProductGrouping,
    `MathCollab.Density.RectangleResidue,
    `MathCollab.Density.Reflection,
    `MathCollab.Density.ReflectionApplication,
    `MathCollab.Density.ReflectionAssembly,
    `MathCollab.Density.ReflectionDefinitions,
    `MathCollab.Density.UniformIBP,
    `MathCollab.Density.UniformThreshold,
    `MathCollab.Density.WeightedSquare,
    `MathCollab.Density.WeylInput,
    `MathCollab.Density.ZeroLargeValues,
    `MathCollab.Density.ZeroSeparation,
    `MathCollab.Density.ZetaConjugation,
    `MathCollab.Density.ZetaCounting,
    `MathCollab.Density.ZetaJensenInputs,
    `MathCollab.MathlibSmoke,
    `MathCollab.Smoke,
    `WeylPort.AFE.AFESecondLimits,
    `WeylPort.AFE.AFESecondModes,
    `WeylPort.AFE.AFESecondWeights,
    `WeylPort.AFE.AbelSawtooth,
    `WeylPort.AFE.AlternatingHarmonic,
    `WeylPort.AFE.ChiGammaFactor,
    `WeylPort.AFE.ChiReflection,
    `WeylPort.AFE.DampedWeightedKernel,
    `WeylPort.AFE.EulerMaclaurin,
    `WeylPort.AFE.ExponentialTails,
    `WeylPort.AFE.FiniteExponentialSums,
    `WeylPort.AFE.FirstDerivativeTest,
    `WeylPort.AFE.HarmonicDigamma,
    `WeylPort.AFE.LowerIntegralEstimate,
    `WeylPort.AFE.MonotoneAmplitude,
    `WeylPort.AFE.NonstationaryPhase,
    `WeylPort.AFE.Objects,
    `WeylPort.AFE.OscillatoryParts,
    `WeylPort.AFE.PartIISignReview,
    `WeylPort.AFE.PoissonApplications,
    `WeylPort.AFE.PoissonFourier,
    `WeylPort.AFE.PoissonPartI,
    `WeylPort.AFE.PoissonShift,
    `WeylPort.AFE.PowerWeights,
    `WeylPort.AFE.SecondCoeffBounds,
    `WeylPort.AFE.SecondCoefficients,
    `WeylPort.AFE.SecondEndpoints,
    `WeylPort.AFE.SecondModeTails,
    `WeylPort.AFE.SecondTailSharp,
    `WeylPort.AFE.UniformCoefficients,
    `WeylPort.AFE.UniformElementary,
    `WeylPort.AFE.UniformError,
    `WeylPort.AFE.UpperIntegralEstimate,
    `WeylPort.AFE.UpperModeTails,
    `WeylPort.AFE.WeightedIntegralAssembly,
    `WeylPort.AFE.WeightedIntegralPhase,
    `WeylPort.AFE.WeightedIntegralSums,
    `WeylPort.AFE.WeightedIntegrals,
    `WeylPort.AFE.ZetaTruncation,
    `WeylPort.ActualZeta,
    `WeylPort.Analytic.ComplexLaplace,
    `WeylPort.Analytic.DigammaSeries,
    `WeylPort.Analytic.EulerMaclaurin,
    `WeylPort.Analytic.NonstationaryFoundation,
    `WeylPort.Analytic.RealLaplace,
    `WeylPort.Analytic.ZetaContinuation,
    `WeylPort.Block,
    `WeylPort.CutoffSelection,
    `WeylPort.GapSum,
    `WeylPort.GrowthAlgebra,
    `WeylPort.Reflection,
    `WeylPort.ShortSum]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut seenModules : List Name := []
  let mut seenTargets : List Name := []
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if localModules.contains modName then
      seenModules := modName :: seenModules
      for target in env.header.moduleData[i]!.constNames do
        if seenTargets.contains target then continue
        seenTargets := target :: seenTargets
        let dependencies ← withEnv env <| Lean.collectAxioms target
        for dependency in dependencies do
          unless allowed.contains dependency do
            throwError "Disallowed transitive assumption {dependency} in {target}"
        logInfo (s!"AUDIT_DECL|{modName}|{target}|" ++
          String.intercalate "," (dependencies.toList.map Name.toString))
        count := count + 1
  for modName in localModules do
    unless seenModules.contains modName do
      throwError "Unaudited production module {modName}"
  logInfo m!"Full assumption allowlist passed: {count} declarations in {seenModules.length} modules."
