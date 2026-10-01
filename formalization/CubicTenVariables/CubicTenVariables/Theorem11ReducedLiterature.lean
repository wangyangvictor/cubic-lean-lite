import CubicTenVariables.CubicGenericIntegralityUniform
import CubicTenVariables.CubicPrincipalOpenUniform
import CubicTenVariables.Theorem11ModuloLiterature
import CubicTenVariables.SmoothInfinityGeometricIntegralityProved
import CubicTenVariables.FixedFamilyPrimeFieldPointCountProved
import CubicTenVariables.ScalarLatticePoissonProved
import CubicTenVariables.PleasantsProved

/-!
The literal n >= 10 theorem with smooth-point-at-infinity integrality, the
required cubic spreading statements, and finite-field point counts supplied
by internal proofs. The broader general spreading and degree-only counting
statements are no longer required. Scalar-lattice Poisson summation is also
proved internally, as are the exact homogeneous fiber-depth models.
The ordinary and localized series and the positive zero-frequency main term
are proved internally, without the general Bernert proposition. Hooley--Katz
remains an input for the sharper pointwise estimates used by the shifted average.
The required cubic oscillatory localization and rapid frequency decay are
proved internally; the general BHB proposition is unused.
The delta kernels are constructed internally.
Seven literature propositions remain unproved.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Theorem11ReducedLiterature

/-- Theorem 1.1 with seven explicit literature inputs. -/
theorem main
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : TranslatedDepthSeven.StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (weil : Literature.AffinePlaneCurveWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : TranslatedDepthSeven.Published.Salberger2023Theorem04)
    (hk : Literature.HooleyKatzPointCount)
    (browning : Literature.BrowningCubicPointCount)
    
     : MainTheorem :=
  Theorem11ModuloLiterature.main microlocal degreeSpan
    SmoothInfinityGeometricIntegralityProved.proved CubicGenericIntegralityUniform.proved weil dichotomy
    salberger CubicPrincipalOpenUniform.proved hk browning FixedFamilyPrimeFieldPointCountProved.proved
    PleasantsProved.proved ScalarLatticePoissonProved.proved

end CubicTenVariables.Theorem11ReducedLiterature
