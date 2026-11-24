module

-- Formal Systems (fs)
public import Mathlib.ModelTheory.Syntax

-- Propositional Calculus (pc)
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Bool.Basic

-- First-Order Logic (lpc)
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Complexity

-- First-Order Logic with = (lpce)
public import Mathlib.Logic.Relation

-- Peano Arithmetic (nn)
public import Mathlib.Data.Nat.Basic
public import Mathlib.Computability.Primrec.Basic

-- Integer Arithmetic (zz)
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Int.Basic

-- Prime Fields of Characteristic 0 (qq)
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.NumberTheory.Real.Irrational

-- Complete Ordered Fields (rr)
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.CompleteField
public import Mathlib.Topology.MetricSpace.Sequences

-- Algebraically Closed Fields (cc)
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

-- 4D Real Division Algebras (hh)
public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Quaternion

-- 8D Normed Division Algebras (oo)
public import MathTree.Octonion

-- Monoids (mon)
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic

-- Commutative Monoids (cmon)
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.Order.WellFoundedSet

-- Semirings (sr)
public import Mathlib.Algebra.Ring.Defs

-- Rings (ri)
public import Mathlib.Algebra.Ring.Basic

-- Integral Domains (ind)
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs

-- Division Rings (dr)
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.LittleWedderburn

-- Fields (fi)
public import Mathlib.Algebra.Field.Basic

-- Vector Spaces (vs)
public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank

-- Groups (gr)
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.GroupTheory.SchurZassenhaus

-- Abelian Groups (ag)
public import Mathlib.GroupTheory.FiniteAbelian.Basic

-- Double Fields (df)
public import MathTree.DoubleField

-- Triple Fields (tf)
public import MathTree.TripleField
public import MathTree.MLISP
public import MathTree.MLISPTuring

-- Quadruple Fields (qf)
public import MathTree.QuadrupleField

-- Lie Algebras (la)
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Engel
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.Algebra.Lie.Semisimple.Defs

-- Linear Operators (lo)
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

-- Sets (sets)
public import Mathlib.SetTheory.ZFC.Basic
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.SetTheory.Cardinal.Basic

-- Topological Spaces (top)
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.Compactification.StoneCech

-- Measure Spaces (mea)
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

-- Real Functions (rf)
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

-- nD Real Vector Spaces (rn)
public import Mathlib.Analysis.InnerProductSpace.PiL2

-- nD Complex Vector Spaces (cn)
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum

-- Differential Operators (do)
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique

-- Relations (rel)
public import Mathlib.Basic.Rel
public import Mathlib.Order.RelClasses
public import Mathlib.Data.Setoid.Basic

-- Models (mod)
public import Mathlib.ModelTheory.Basic
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.ModelTheory.Ultraproducts

-- Commutative Rings (cr)
public import Mathlib.Algebra.Ring.Defs

-- Modules (modu)
public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID

-- Ordered Fields (of)
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic

-- Normed Vector Spaces (nvs)
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach

-- Inner Product Spaces (ips)
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.OfNorm

-- Sets with Choice (zfc)
public import Mathlib.SetTheory.ZFC.Basic
public import Mathlib.Order.Zorn

-- Magmas (mg)
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Free
public import Mathlib.RingTheory.PowerSeries.Catalan

-- Semigroups (sg)
public import Mathlib.Algebra.Group.Defs

-- Digraphs (dg)
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Digraph.Basic

-- Graphs (graph)
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.ModelTheory.Graph
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.Hall.Basic

-- Posets (po)
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Basic
public import Mathlib.Order.Extension.Linear

-- Preorders (pre)
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.CategoryTheory.Category.Preorder

-- Equivalence Relations (eq)
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Data.Setoid.Partition.Card
public import Mathlib.Combinatorics.Enumerative.Bell

-- Total Orders (tord)
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Extension.Linear
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Data.Finset.Sort

-- Bands (band)
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Idempotent

-- Semilattices (sl)
public import Mathlib.Order.Lattice

-- Lattices (lat)
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Birkhoff

-- Frames (fr)
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Order

-- Functions (fn)
public import Mathlib.ModelTheory.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.Perm

-- Languages (lang)
public import Mathlib.ModelTheory.Syntax
public import Mathlib.ModelTheory.Basic

-- Theories (th)
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.ModelTheory.Semantics

-- Presentations (pres)
public import Mathlib.ModelTheory.Basic
public import Mathlib.ModelTheory.Semantics

-- Structures (struct)
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Equivalence

-- Presentations, Mathematical Structures and Clones as theories (pres, struct, clone)
public import MathTree.Clones
public import Mathlib.ModelTheory.Equivalence

-- Probability Spaces (pr)
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Real

-- Matrices (mat)
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

-- Differentiable Functions (dfn)
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Exp

-- Distributive Lattices (dl)
public import Mathlib.Order.Lattice
public import Mathlib.Order.Birkhoff
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.BooleanAlgebra.Basic

-- Boolean Algebras (ba)
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Algebra.Ring.BooleanRing

-- Finite Sets (fset)
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.Finite.Defs

-- Robinson Arithmetic (rq)
public import MathTree.Arithmetic

-- Presburger Arithmetic (pa)

-- Metric Spaces (ms)
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Defs

-- Banach Spaces (bs)
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Module.DoubleDual

-- Hilbert Spaces (hs)
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic

-- Real Manifolds (rm)
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.WhitneyEmbedding

-- Lie Groups (lg)
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

-- Algebras (al)
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.LinearAlgebra.CrossProduct

-- Associative Algebras (aa)
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin


-- Tensor Spaces (ts)
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# The math tree in Mathlib

One import block per box of the tree (the comments name the boxes), giving the Mathlib module(s)
in which the formal system is defined and, for a few boxes, the module proving its flagship theorem.
Boxes that Mathlib does not have are defined in `MathTree/*.lean`.
-/
