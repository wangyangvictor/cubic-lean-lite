import CubicTenVariables.DavenportCount
import CubicTenVariables.TensorHessian

/-! The full displayed Davenport dichotomy is now proved on the exact
integral symmetric-tensor objects used by the literature interface. The
singular-series application therefore retains only Bernert's theorem. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial

/-- The geometric rank-count condition for every anisotropic integral
symmetric tensor. Its rank is Bernert's matrix rank, with normalization
proved in TensorHessian. -/
theorem proved_tensorDavenportGood_of_no_integer_zero {n : ℕ}
    (T : SymmetricIntegerCubicTensor n) (hzero : ¬ HasIntegerZero T.polynomial) :
    Literature.TensorDavenportGood T := by
  apply (Literature.tensorDavenportGood_iff_davenportGood T T.polynomial
    (tensorMatrixRank_eq_integerHessianRank T)).mpr
  exact proved_davenportGood_of_no_integer_zero T.polynomial
    T.polynomial_homogeneous hzero

/-- An actual inhabitant of the complete previously external proposition,
in every number of variables. No new geometric or counting input remains. -/
theorem provedDavenportGeometricDichotomy : Literature.DavenportGeometricDichotomy := by
  intro n T hnotgood
  by_contra hzero
  exact hnotgood (proved_tensorDavenportGood_of_no_integer_zero T hzero)

/-- The original cubic singular-series conclusion now has just one explicit
literature argument. It is still not a counting asymptotic. -/
theorem bernert_of_no_integer_zero_proved_davenport
    (bernert : Literature.Bernert2025Theorem1) {n : ℕ}
    (T : SymmetricIntegerCubicTensor n) (hn : 10 ≤ n)
    (hzero : ¬ HasIntegerZero T.polynomial) :
    SingularSeriesAbsolutelyConvergent T.polynomial ∧
      Literature.PositiveRealSingularSeries T.polynomial :=
  bernert n T hn (proved_tensorDavenportGood_of_no_integer_zero T hzero)

end CubicTenVariables
