import EnvelopeProperty.Berkovich.SpectrumGrading
import EnvelopeProperty.Berkovich.SpectrumLocalization
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Actual native Proj valued points of original relevant graded seminorms

The original seminorm is restricted to the TRUE degree-zero projective
stalk before descending to its TRUE projective residue field.
The proof generalizes the actual stalk construction of NativeComparison;
no affine-cone/projective residue-field identification is made.
-/
open scoped Classical NNReal Topology
open Topology MvPolynomial AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelevantGradedSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The original valuation uniquely extended to the full ordinary localization at its support. -/
def localValuation (x : RelevantGradedSpectrum 𝒜) :
    Valuation (Localization.AtPrime x.1.val.supp) ℝ≥0 :=
  x.1.val.extendToLocalization le_rfl _

/-- The genuine ordinary localized valuation has exactly the actual local maximal support. -/
theorem localValuation_supp (x : RelevantGradedSpectrum 𝒜) :
    (localValuation x).supp = IsLocalRing.maximalIdeal (Localization.AtPrime x.1.val.supp) := by
  ext z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq x.1.val.supp.primeCompl z
  rw [Valuation.mem_supp_iff, localValuation, Valuation.extendToLocalization_mk',
    IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime x.1.val.supp) x.1.val.supp]
  change x.1.val a * (x.1.val s.1)⁻¹ = 0 ↔ x.1.val a = 0
  have hs : x.1.val s.1 ≠ 0 := s.2
  simp only [mul_eq_zero, inv_eq_zero, hs, or_false]

/-- Restrict the actual ordinary localized valuation to the true degree-zero homogeneous local ring. -/
def homogeneousLocalValuation (x : RelevantGradedSpectrum 𝒜) :
    Valuation (HomogeneousLocalization.AtPrime 𝒜 x.1.val.supp) ℝ≥0 :=
  (localValuation x).comap (algebraMap
    (HomogeneousLocalization.AtPrime 𝒜 x.1.val.supp)
      (Localization.AtPrime x.1.val.supp))

/-- The homogeneous local valuation also has its true local maximal ideal as support. -/
theorem homogeneousLocalValuation_supp (x : RelevantGradedSpectrum 𝒜) :
    (homogeneousLocalValuation x).supp =
      IsLocalRing.maximalIdeal (HomogeneousLocalization.AtPrime 𝒜 x.1.val.supp) := by
  ext z
  change localValuation x z.val = 0 ↔ ¬ IsUnit z
  rw [← Valuation.mem_supp_iff, localValuation_supp]
  change ¬ IsUnit z.val ↔ ¬ IsUnit z
  exact not_congr (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜 x.1.val.supp z)

/-- Transport the true homogeneous local valuation to the actual projective structure-sheaf stalk. -/
def nativeStalkValuation (x : RelevantGradedSpectrum 𝒜) :
    Valuation ((Proj 𝒜).presheaf.stalk (support x)) ℝ≥0 :=
  (homogeneousLocalValuation x).comap
    (AlgebraicGeometry.Proj.stalkIso' 𝒜 (support x)).toRingHom

/-- The actual projective stalk valuation vanishes exactly on its genuine local maximal ideal. -/
theorem nativeStalkValuation_supp (x : RelevantGradedSpectrum 𝒜) :
    (nativeStalkValuation x).supp =
      IsLocalRing.maximalIdeal ((Proj 𝒜).presheaf.stalk (support x)) := by
  ext a
  change homogeneousLocalValuation x
    (AlgebraicGeometry.Proj.stalkIso' 𝒜 (support x) a) = 0 ↔ ¬ IsUnit a
  erw [← Valuation.mem_supp_iff, homogeneousLocalValuation_supp]
  change ¬ IsUnit (AlgebraicGeometry.Proj.stalkIso' 𝒜 (support x) a) ↔ ¬ IsUnit a
  apply not_congr
  constructor
  · intro h
    have hu := h.map (AlgebraicGeometry.Proj.stalkIso' 𝒜 (support x)).symm.toRingHom
    simpa using hu
  · intro h
    exact h.map (AlgebraicGeometry.Proj.stalkIso' 𝒜 (support x)).toRingHom

/-- Descend the true projective stalk valuation to its actual residue field, giving a canonical native point. -/
def nativePoint (x : RelevantGradedSpectrum 𝒜) : SchemeValuedPoint (Proj 𝒜) where
  point := support x
  residueVal := (nativeStalkValuation x).onQuot (le_of_eq (nativeStalkValuation_supp x).symm)

/-- The canonical native valued point retains the original homogeneous prime scheme support. -/
@[simp]
theorem nativePoint_point (x : RelevantGradedSpectrum 𝒜) :
    (nativePoint x).point = support x := rfl

/-- Every actual stalk residue retains the original stalk valuation. -/
theorem nativePoint_residue (x : RelevantGradedSpectrum 𝒜)
    (a : (Proj 𝒜).presheaf.stalk (support x)) :
    (nativePoint x).residueVal ((Proj 𝒜).residue (support x) a) =
      nativeStalkValuation x a := rfl

/-- The true homogeneous local value of every original chart fraction is the original fraction value. -/
theorem homogeneousLocalValuation_mapId_chart (x : RelevantGradedSpectrum 𝒜)
    (f : A) {m : ℕ} (hf : f ∈ 𝒜 m) (hx : support x ∈ Proj.basicOpen 𝒜 f)
    (q : HomogeneousLocalization.Away 𝒜 f) :
    homogeneousLocalValuation x
      (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx) q) =
      (Spectrum.awayLift f x.1 hx).val q.val := by
  obtain ⟨d, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf q
  have hd : f ^ d ∈ x.1.val.supp.primeCompl := by
    change x.1.val (f ^ d) ≠ 0
    rw [map_pow]
    exact pow_ne_zero d hx
  change localValuation x (Localization.mk p ⟨f ^ d, hd⟩) =
    (Spectrum.awayLift f x.1 hx).val
      (Localization.mk p (⟨f ^ d, d, rfl⟩ : Submonoid.powers f))
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', localValuation,
    Spectrum.awayLift, Spectrum.Away.lift,
    Valuation.extendToLocalization_mk', Valuation.extendToLocalization_mk']

/-- EVERY actual native homogeneous chart section retains its SAME original fraction valuation. -/
theorem nativePoint_eval_awayToSection (x : RelevantGradedSpectrum 𝒜)
    (f : A) {m : ℕ} (hf : f ∈ 𝒜 m) (hx : support x ∈ Proj.basicOpen 𝒜 f)
    (q : HomogeneousLocalization.Away 𝒜 f) :
    SchemeValuedPoint.eval (nativePoint x) (Proj.basicOpen 𝒜 f) hx
      (Proj.awayToSection 𝒜 f q) =
      (Spectrum.awayLift f x.1 hx).val q.val := by
  change (nativePoint x).residueVal ((Proj 𝒜).residue (support x)
    ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) (support x) hx
      (Proj.awayToSection 𝒜 f q))) = _
  rw [nativePoint_residue]
  have hg := congrArg (fun g => g q)
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f (support x) hx)
  change (Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) (support x) hx
      (Proj.awayToSection 𝒜 f q) =
    (Proj.stalkIso' 𝒜 (support x)).symm
      (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx) q) at hg
  rw [hg]
  change homogeneousLocalValuation x
    ((Proj.stalkIso' 𝒜 (support x)) ((Proj.stalkIso' 𝒜 (support x)).symm _)) = _
  rw [RingEquiv.apply_symm_apply]
  exact homogeneousLocalValuation_mapId_chart x f hf hx q

/-- Every SAME original homogeneous numerator/coordinate power gives its exact fraction value. -/
theorem nativePoint_eval_mk (x : RelevantGradedSpectrum 𝒜)
    (f : A) {m : ℕ} (hf : f ∈ 𝒜 m) (hx : support x ∈ Proj.basicOpen 𝒜 f)
    (d : ℕ) (p : A) (hp : p ∈ 𝒜 (d • m)) :
    SchemeValuedPoint.eval (nativePoint x) (Proj.basicOpen 𝒜 f) hx
      (Proj.awayToSection 𝒜 f (HomogeneousLocalization.Away.mk 𝒜 hf d p hp)) =
      x.1.val p / x.1.val f ^ d := by
  rw [nativePoint_eval_awayToSection x f hf hx,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  simp only [Spectrum.awayLift, Spectrum.Away.lift, Valuation.extendToLocalization_mk', map_pow,
    div_eq_mul_inv]

end EnvelopeProperty.Berkovich.RelevantGradedSpectrum
