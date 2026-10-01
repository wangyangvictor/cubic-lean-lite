import TranslatedDepthSeven.TaggedLineCount
import Mathlib.Tactic

/-!
# Counting a normalized radial lattice plane

This file proves the elementary lattice estimate behind the radial-plane
count in the translated depth-seven argument.  In normalized coordinates the
two generators are

`e₁ = (1, 0)` and `(0, z)`.

Thus an integral point in the plane is parametrized by a unique pair
`(a,b) : ℤ × ℤ` and has coordinates `(a, b z₁, ..., b zₙ)`.  We count such
pairs in an arbitrary real translated coordinate box.  No integrality is
assumed of the centre.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Two integers lying in the same real interval of radius `R` differ by at
most the integer `⌈2R⌉`. -/
theorem int_abs_sub_le_ceil_two_mul
    {x y : ℤ} {center R : ℝ}
    (hx : |(x : ℝ) - center| ≤ R)
    (hy : |(y : ℝ) - center| ≤ R) :
    |x - y| ≤ (⌈2 * R⌉₊ : ℤ) := by
  have hreal : |(((x - y : ℤ) : ℝ))| ≤ 2 * R := by
    calc
      |(((x - y : ℤ) : ℝ))| =
          |((x : ℝ) - center) - ((y : ℝ) - center)| := by
            congr 1
            push_cast
            ring
      _ ≤ |(x : ℝ) - center| + |(y : ℝ) - center| := abs_sub _ _
      _ ≤ R + R := add_le_add hx hy
      _ = 2 * R := by ring
  have hceil : 2 * R ≤ (⌈2 * R⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : ((|x - y| : ℤ) : ℝ) ≤ (⌈2 * R⌉₊ : ℝ) := by
    rw [Int.cast_abs]
    exact hreal.trans hceil
  exact_mod_cast hcast

/-- A finite set of integers of integral diameter at most `W` has at most
`W+1` elements. -/
theorem finset_card_le_one_add_of_diameter
    (S : Finset ℤ) {W : ℕ}
    (hdiameter : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ (W : ℤ)) :
    S.card ≤ W + 1 := by
  have hmod : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [ZMOD (1 : ℤ)] := by
    intro x _ y _
    rw [Int.modEq_iff_dvd]
    exact one_dvd _
  have h := finset_card_le_one_add_div_of_modEq_of_diameter
    S (s := 1) (W := W) (by norm_num) hmod hdiameter
  simpa [Nat.add_comm] using h

/-- Exact rectangular estimate for the normalized radial plane.

For every `(a,b) ∈ A`, the hypotheses say precisely that the integral vector
`(a,bz)` lies in the coordinatewise real box of radius `R` centred at
`(centerFirst, centerTail)`.  If `z` is primitive, then

`#A ≤ (⌈2R⌉+1) (1 + ⌈2R⌉ / ‖z‖∞)`.
-/
theorem radialPairs_card_le_realBox_exact
    {n : ℕ} {z : IntVector n}
    (A : Finset (ℤ × ℤ))
    {centerFirst R : ℝ} {centerTail : RealVector n}
    (hprimitive : PrimitiveDirection z)
    (hbox : ∀ p ∈ A,
      |(p.1 : ℝ) - centerFirst| ≤ R ∧
      ∀ i, |((p.2 * z i : ℤ) : ℝ) - centerTail i| ≤ R) :
    A.card ≤
      (⌈2 * R⌉₊ + 1) *
        (1 + ⌈2 * R⌉₊ / directionHeight z) := by
  classical
  obtain ⟨j, hj, hheight⟩ :=
    hprimitive.exists_natAbs_eq_directionHeight
  let encode : ℤ × ℤ → ℤ × ℤ := fun p ↦ (p.1, p.2 * z j)
  let encoded : Finset (ℤ × ℤ) := A.image encode
  let firstCoordinates : Finset ℤ := A.image Prod.fst
  let radialCoordinates : Finset ℤ := A.image fun p ↦ p.2 * z j
  have hencode_injective : Function.Injective encode := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hpq
    simp only [encode, Prod.mk.injEq] at hpq ⊢
    exact ⟨hpq.1, mul_right_cancel₀ hj hpq.2⟩
  have hencoded_card : encoded.card = A.card := by
    dsimp [encoded]
    exact Finset.card_image_of_injective A hencode_injective
  have hencoded_subset : encoded ⊆ firstCoordinates ×ˢ radialCoordinates := by
    intro q hq
    simp only [encoded, Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
        Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hfirst_diameter : ∀ x ∈ firstCoordinates, ∀ y ∈ firstCoordinates,
      |x - y| ≤ (⌈2 * R⌉₊ : ℤ) := by
    intro x hx y hy
    simp only [firstCoordinates, Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    exact int_abs_sub_le_ceil_two_mul (hbox p hp).1 (hbox q hq).1
  have hfirst_card : firstCoordinates.card ≤ ⌈2 * R⌉₊ + 1 :=
    finset_card_le_one_add_of_diameter firstCoordinates hfirst_diameter
  have hradial_diameter :
      ∀ x ∈ radialCoordinates, ∀ y ∈ radialCoordinates,
        |x - y| ≤ (⌈2 * R⌉₊ : ℤ) := by
    intro x hx y hy
    simp only [radialCoordinates, Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    exact int_abs_sub_le_ceil_two_mul ((hbox p hp).2 j) ((hbox q hq).2 j)
  have hradial_mod :
      ∀ x ∈ radialCoordinates, ∀ y ∈ radialCoordinates,
        x ≡ y [ZMOD ((z j).natAbs : ℤ)] := by
    intro x hx y hy
    simp only [radialCoordinates, Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    apply Int.modEq_natAbs.mpr
    rw [Int.modEq_iff_dvd]
    refine ⟨q.2 - p.2, ?_⟩
    ring
  have hradial_card :
      radialCoordinates.card ≤
        1 + ⌈2 * R⌉₊ / (z j).natAbs := by
    exact finset_card_le_one_add_div_of_modEq_of_diameter
      radialCoordinates (Int.natAbs_pos.mpr hj) hradial_mod hradial_diameter
  have hsubset_card := Finset.card_le_card hencoded_subset
  rw [Finset.card_product, hencoded_card] at hsubset_card
  calc
    A.card ≤ firstCoordinates.card * radialCoordinates.card := hsubset_card
    _ ≤ (⌈2 * R⌉₊ + 1) *
        (1 + ⌈2 * R⌉₊ / (z j).natAbs) :=
      Nat.mul_le_mul hfirst_card hradial_card
    _ = (⌈2 * R⌉₊ + 1) *
        (1 + ⌈2 * R⌉₊ / directionHeight z) := by rw [hheight]

/-- The elementary comparison turning the exact rectangular estimate into
the conventional `1 + W + W²/H` form. -/
theorem radialRectangle_le_two
    (W H : ℕ) :
    (W + 1) * (1 + W / H) ≤
      2 * (1 + W + (W * W) / H) := by
  have hquotient : W / H ≤ W := Nat.div_le_self W H
  have hproduct : W * (W / H) ≤ (W * W) / H :=
    Nat.mul_div_le_mul_div_assoc W W H
  calc
    (W + 1) * (1 + W / H) =
        W + 1 + (W * (W / H) + W / H) := by ring
    _ ≤ W + 1 + ((W * W) / H + W) :=
      Nat.add_le_add_left (Nat.add_le_add hproduct hquotient) _
    _ ≤ 2 * (1 + W + (W * W) / H) := by omega

/-- Manuscript-form radial lattice estimate.  With
`W = ⌈2R⌉` and `H = ‖z‖∞`, it gives the explicit bound

`#A ≤ 2 (1 + W + W²/H)`.

This is the claimed `O(1 + R + R²/‖z‖∞)` estimate, with the real translated
box handled by the ceiling in `W` and with the absolute constant equal to
two.
-/
theorem radialPairs_card_le_realBox
    {n : ℕ} {z : IntVector n}
    (A : Finset (ℤ × ℤ))
    {centerFirst R : ℝ} {centerTail : RealVector n}
    (hprimitive : PrimitiveDirection z)
    (hbox : ∀ p ∈ A,
      |(p.1 : ℝ) - centerFirst| ≤ R ∧
      ∀ i, |((p.2 * z i : ℤ) : ℝ) - centerTail i| ≤ R) :
    A.card ≤ 2 *
      (1 + ⌈2 * R⌉₊ +
        (⌈2 * R⌉₊ * ⌈2 * R⌉₊) / directionHeight z) := by
  have hexact := radialPairs_card_le_realBox_exact A hprimitive hbox
  exact hexact.trans
    (radialRectangle_le_two ⌈2 * R⌉₊ (directionHeight z))

end

end TranslatedDepthSeven
