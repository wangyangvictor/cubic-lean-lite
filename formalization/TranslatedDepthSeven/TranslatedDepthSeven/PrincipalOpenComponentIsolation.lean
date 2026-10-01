import TranslatedDepthSeven.MinimalComponentIsolation
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Principal-open component extraction and generic freeness

`MinimalComponentIsolation.lean` already proves the qualitative component
extraction needed for a fixed Noetherian equation ring: after inverting one
element outside a selected minimal prime, the localized radical is exactly
that component.  This file records two consequences in the precise forms
needed downstream.

First, the selected component is the unique minimal prime on that principal
open.  Second, a finitely presented module over a domain is free, with its
generic rank, on some nonempty principal open.  Applied after a finite
projection, the latter turns the selected component algebra into a finite
free algebra without introducing an effective or geometric interface.

For the vertical application all these objects belong to one fixed
polynomial ring.  Once chosen, their evaluation bounds are therefore the
elementary fixed-polynomial bounds already proved elsewhere; no separate
relative effectivity theorem is asserted here.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Generic freeness in the exact principal-open form needed after a finite
projection.  A finitely presented module over a domain becomes free, with
its generic rank, after inverting one nonzero element. -/
theorem exists_nonzero_away_free_of_finitePresentation
    [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r)
        (LocalizedModule (Submonoid.powers r) M) ∧
      Module.finrank (Localization.Away r)
          (LocalizedModule (Submonoid.powers r) M) =
        Module.finrank (FractionRing R)
          (LocalizedModule (nonZeroDivisors R) M) := by
  obtain ⟨r, hr, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors R)
      (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) (FractionRing R)
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hfree, hrank⟩

variable [IsNoetherianRing R]

/-- On the component-isolating principal open, the selected component is the
unique minimal prime of the localized equation ideal. -/
theorem exists_away_minimalPrimes_eq_singleton
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes) :
    ∃ s : R, s ∉ P ∧
      ((I.map (algebraMap R (Localization.Away s))).minimalPrimes =
        {P.map (algebraMap R (Localization.Away s))}) := by
  obtain ⟨s, hsP, hmap⟩ :=
    exists_map_away_radical_eq_minimalComponent I P hP
  refine ⟨s, hsP, ?_⟩
  let A := Localization.Away s
  let f : R →+* A := algebraMap R A
  have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hdisjP : Disjoint (Submonoid.powers s : Set R) P :=
    (Ideal.disjoint_powers_iff_notMem s hPprime.isRadical).mpr hsP
  letI : (P.map f).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers s) A P hPprime hdisjP
  change (I.map f).minimalPrimes = {P.map f}
  rw [← Ideal.radical_minimalPrimes,
    ← IsLocalization.map_radical (Submonoid.powers s) A I,
    hmap, Ideal.minimalPrimes_eq_subsingleton_self]

/-- Equivalently, the reduced localization of the original closed subscheme
is exactly the selected irreducible component. -/
theorem exists_away_radical_eq_selectedMinimalPrime
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes) :
    ∃ s : R, s ∉ P ∧
      (I.map (algebraMap R (Localization.Away s))).radical =
        P.map (algebraMap R (Localization.Away s)) := by
  obtain ⟨s, hsP, hmap⟩ :=
    exists_map_away_radical_eq_minimalComponent I P hP
  refine ⟨s, hsP, ?_⟩
  rw [← IsLocalization.map_radical (Submonoid.powers s)
    (Localization.Away s) I]
  exact hmap

end

end TranslatedDepthSeven
