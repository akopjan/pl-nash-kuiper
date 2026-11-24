module

public import Solution
public import Compatibility.PLContinuity

/-! # Transitive dependency audit of the unchanged original Challenge target -/

#check PLGeometry.akopyan_pl_nash_kuiper
#print axioms PLGeometry.akopyan_pl_nash_kuiper
#print axioms PLGeometry.PLIsometry.continuous

#print axioms ArchivePLGeometry.pl_nash_kuiper_euclidean
#print axioms ArchivePLGeometry.pl_nash_kuiper_spherical
#print axioms ArchivePLGeometry.pl_nash_kuiper_hyperbolic
#print axioms ArchivePLGeometry.FiniteChartedComplex.hasSmallFiniteFolding
#print axioms ArchivePLGeometry.FiniteChartedComplex.isFinitePolyhedron_foldedIntrinsicMetric
