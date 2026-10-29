/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NormalizedSpectrum
import EnvelopeProperty.Projective.NativeCharts
import EnvelopeProperty.Projective.PolynomialGrading
import EnvelopeProperty.Berkovich.SchemeHausdorff
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Actual native polynomial Proj and normalized graded seminorms

For arbitrary coefficient rings and prescribed real seminorms, the normalized model
is genuinely homeomorphic to the native valued-point space of the actual polynomial
Proj scheme. The point map is constructed canonically from the homogeneous kernel,
its true degree-zero localized stalk and its actual residue valuation. Both whole
coordinate evaluations and the original coefficient scheme morphism are preserved.

The actual native residue field is formed from the projective degree-zero stalk.
It is distinct from the generally larger residue field of the affine cone seminorm;
no identification of those fields is made. Compactness of the fixed-base normalized
space and the proven Hausdorff native topology of separated schemes supply the
homeomorphism after the genuine whole-point chart bijection and continuity proofs.

This is a point-space and topology comparison. An analytic structure sheaf, coherent
ideal identification and scheme-general analytic gluing are separate constructions.
-/

open scoped Classical NNReal Topology
open Topology MvPolynomial AlgebraicGeometry CategoryTheory Opposite
open EnvelopeProperty.ProjBerk EnvelopeProperty.Berkovich
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum
variable {R : Type*} [CommRing R] {n : ℕ}
private local instance nativeComparisonChartAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

/-- Normalization supplies a genuine relevant graded spectrum point, with its actual homogeneous prime kernel. -/
def toRelevantGradedSpectrum (x : NormalizedProjectiveSpectrum R n) :
    RelevantGradedSpectrum (ProjectiveGrading R n) :=
  ⟨x.1, (Spectrum.isPolynomialGraded_iff_isGraded x.1).mp x.2.1, by
    intro h
    obtain ⟨j, hj⟩ := exists_val_X_eq_one x
    have hX := h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X R j))
    change x.1.val (MvPolynomial.X j) = 0 at hX
    exact one_ne_zero (hj.symm.trans hX)⟩

/-- Forgetting normalization to the true relevant graded subspace is continuous. -/
@[fun_prop]
theorem continuous_toRelevantGradedSpectrum :
    Continuous (toRelevantGradedSpectrum (R := R) (n := n)) := continuous_val.subtype_mk _

/-- The actual polynomial Proj scheme point given by the normalized seminorm kernel. -/
def nativeSupport (x : NormalizedProjectiveSpectrum R n) : NativeProjectiveScheme R n :=
  RelevantGradedSpectrum.support (toRelevantGradedSpectrum x)

/-- The actual native projective scheme support varies continuously. -/
@[fun_prop]
theorem continuous_nativeSupport : Continuous (nativeSupport (R := R) (n := n)) :=
  RelevantGradedSpectrum.continuous_support.comp continuous_toRelevantGradedSpectrum

/-- The genuine native homogeneous ideal is the original full valuation kernel. -/
@[simp]
theorem nativeSupport_toIdeal (x : NormalizedProjectiveSpectrum R n) :
    (nativeSupport x).asHomogeneousIdeal.toIdeal = x.1.val.supp := rfl

/-- A coordinate is nonzero exactly on its actual native projective coordinate open. -/
@[simp]
theorem nativeSupport_mem_coordinateOpen (x : NormalizedProjectiveSpectrum R n) (j : Fin (n + 1)) :
    nativeSupport x ∈ nativeCoordinateOpen j ↔ x.1.val (MvPolynomial.X j) ≠ 0 := Iff.rfl

/-- The original valuation uniquely extended to the full ordinary localization at its support. -/
def localValuation (x : NormalizedProjectiveSpectrum R n) :
    Valuation (Localization.AtPrime x.1.val.supp) ℝ≥0 :=
  x.1.val.extendToLocalization le_rfl _

/-- The genuine ordinary localized valuation has exactly the actual local maximal support. -/
theorem localValuation_supp (x : NormalizedProjectiveSpectrum R n) :
    (localValuation x).supp = IsLocalRing.maximalIdeal (Localization.AtPrime x.1.val.supp) := by
  ext z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq x.1.val.supp.primeCompl z
  rw [Valuation.mem_supp_iff, localValuation, Valuation.extendToLocalization_mk',
    IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime x.1.val.supp) x.1.val.supp]
  change x.1.val a * (x.1.val s.1)⁻¹ = 0 ↔ x.1.val a = 0
  have hs : x.1.val s.1 ≠ 0 := s.2
  simp only [mul_eq_zero, inv_eq_zero, hs, or_false]

/-- Restrict the actual ordinary localized valuation to the true degree-zero homogeneous local ring. -/
def homogeneousLocalValuation (x : NormalizedProjectiveSpectrum R n) :
    Valuation (HomogeneousLocalization.AtPrime (ProjectiveGrading R n) x.1.val.supp) ℝ≥0 :=
  (localValuation x).comap (algebraMap
    (HomogeneousLocalization.AtPrime (ProjectiveGrading R n) x.1.val.supp)
      (Localization.AtPrime x.1.val.supp))

/-- The homogeneous local valuation also has its true local maximal ideal as support. -/
theorem homogeneousLocalValuation_supp (x : NormalizedProjectiveSpectrum R n) :
    (homogeneousLocalValuation x).supp =
      IsLocalRing.maximalIdeal (HomogeneousLocalization.AtPrime (ProjectiveGrading R n) x.1.val.supp) := by
  ext z
  change localValuation x z.val = 0 ↔ ¬ IsUnit z
  rw [← Valuation.mem_supp_iff, localValuation_supp]
  change ¬ IsUnit z.val ↔ ¬ IsUnit z
  exact not_congr (HomogeneousLocalization.isUnit_iff_isUnit_val (ProjectiveGrading R n) x.1.val.supp z)

/-- Transport the true homogeneous local valuation to the actual projective structure-sheaf stalk. -/
def nativeStalkValuation (x : NormalizedProjectiveSpectrum R n) :
    Valuation ((NativeProjectiveScheme R n).presheaf.stalk (nativeSupport x)) ℝ≥0 :=
  (homogeneousLocalValuation x).comap
    (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x)).toRingHom

/-- The actual projective stalk valuation vanishes exactly on its genuine local maximal ideal. -/
theorem nativeStalkValuation_supp (x : NormalizedProjectiveSpectrum R n) :
    (nativeStalkValuation x).supp =
      IsLocalRing.maximalIdeal ((NativeProjectiveScheme R n).presheaf.stalk (nativeSupport x)) := by
  ext a
  change homogeneousLocalValuation x
    (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x) a) = 0 ↔ ¬ IsUnit a
  erw [← Valuation.mem_supp_iff, homogeneousLocalValuation_supp]
  change ¬ IsUnit (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x) a) ↔ ¬ IsUnit a
  apply not_congr
  constructor
  · intro h
    have hu := h.map (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x)).symm.toRingHom
    simpa using hu
  · intro h
    exact h.map (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x)).toRingHom

/-- Descend the true projective stalk valuation to its actual residue field, giving a canonical native point. -/
def nativePoint (x : NormalizedProjectiveSpectrum R n) : SchemeValuedPoint (NativeProjectiveScheme R n) where
  point := nativeSupport x
  residueVal := (nativeStalkValuation x).onQuot (le_of_eq (nativeStalkValuation_supp x).symm)

/-- The canonical native valued point retains the original homogeneous prime scheme support. -/
@[simp]
theorem nativePoint_point (x : NormalizedProjectiveSpectrum R n) :
    (nativePoint x).point = nativeSupport x := rfl

/-- Every actual stalk residue retains the original stalk valuation. -/
theorem nativePoint_residue (x : NormalizedProjectiveSpectrum R n)
    (a : (NativeProjectiveScheme R n).presheaf.stalk (nativeSupport x)) :
    (nativePoint x).residueVal ((NativeProjectiveScheme R n).residue (nativeSupport x) a) =
      nativeStalkValuation x a := rfl

/-- Every genuine homogeneous chart fraction has the same value in the true local ring and principal localization. -/
theorem homogeneousLocalValuation_mapId_chart (x : NormalizedProjectiveSpectrum R n)
    (j : Fin (n + 1)) (hx : nativeSupport x ∈ nativeCoordinateOpen j)
    (q : HomogeneousChartRing R j) :
    homogeneousLocalValuation x
      (HomogeneousLocalization.mapId (ProjectiveGrading R n) (Submonoid.powers_le.mpr hx) q) =
      (Spectrum.awayLift (MvPolynomial.X j) x.1 hx).val (homogeneousChartVal j q) := by
  obtain ⟨d, F, hF, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) q
  have hd : (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ d ∈ x.1.val.supp.primeCompl := by
    change x.1.val (MvPolynomial.X j ^ d) ≠ 0
    rw [map_pow]
    exact pow_ne_zero d hx
  change localValuation x (Localization.mk F ⟨MvPolynomial.X j ^ d, hd⟩) =
    (Spectrum.awayLift (MvPolynomial.X j) x.1 hx).val
      (Localization.mk F (⟨MvPolynomial.X j ^ d, d, rfl⟩ : Submonoid.powers (MvPolynomial.X j)))
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', localValuation,
    Spectrum.awayLift, Spectrum.Away.lift,
    Valuation.extendToLocalization_mk', Valuation.extendToLocalization_mk']

/-- The actual native point evaluates every homogeneous chart section by its genuine original fraction. -/
theorem nativePoint_eval_homogeneousChart (x : NormalizedProjectiveSpectrum R n)
    (j : Fin (n + 1)) (hx : nativeSupport x ∈ nativeCoordinateOpen j)
    (q : HomogeneousChartRing R j) :
    SchemeValuedPoint.eval (nativePoint x) (nativeCoordinateOpen j) hx
      ((nativeHomogeneousChartSectionsIso j).hom q) =
      (Spectrum.awayLift (MvPolynomial.X j) x.1 hx).val (homogeneousChartVal j q) := by
  change (nativePoint x).residueVal ((NativeProjectiveScheme R n).residue (nativeSupport x)
    ((NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen j) (nativeSupport x) hx
      ((nativeHomogeneousChartSectionsIso j).hom q))) = _
  rw [nativePoint_residue]
  have hg := congrArg (fun f => f q)
    (nativeHomogeneousChartSectionsIso_germ (R := R) j (nativeSupport x) hx)
  change (NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen j) (nativeSupport x) hx
      ((nativeHomogeneousChartSectionsIso j).hom q) =
    (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x)).symm
      (HomogeneousLocalization.mapId (ProjectiveGrading R n) (Submonoid.powers_le.mpr hx) q) at hg
  rw [hg]
  change homogeneousLocalValuation x
    ((AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x))
      ((AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) (nativeSupport x)).symm _)) = _
  rw [RingEquiv.apply_symm_apply]
  exact homogeneousLocalValuation_mapId_chart x j hx q

/-- Every affine polynomial section has its whole ratio-chart seminorm value. -/
theorem nativePoint_eval_coordinateChart (x : NormalizedProjectiveSpectrum R n)
    (j : Fin (n + 1)) (hx : nativeSupport x ∈ nativeCoordinateOpen j)
    (a : CoordinateRing R j) :
    SchemeValuedPoint.eval (nativePoint x) (nativeCoordinateOpen j) hx
      ((nativeCoordinateSectionsIso j).hom a) =
        (coordinateChartMap j ⟨x, hx⟩).val a := by
  change SchemeValuedPoint.eval (nativePoint x) (nativeCoordinateOpen j) hx
    ((nativeHomogeneousChartSectionsIso j).hom (homogeneousChartRatioHom j a)) = _
  rw [nativePoint_eval_homogeneousChart]
  have h := AlgHom.congr_fun (homogeneousChartVal_comp_ratioHom (R := R) j) a
  rw [AlgHom.comp_apply] at h
  rw [h]
  rfl

end EnvelopeProperty.Berkovich.NormalizedProjectiveSpectrum

namespace EnvelopeProperty.ProjBerk
variable {R : Type*} [CommRing R] {n : ℕ}
/-- The true coordinate opens cover actual polynomial Proj by the real irrelevant-ideal identity. -/
theorem iSup_nativeCoordinateOpen_eq_top :
    (⨆ j : Fin (n + 1), nativeCoordinateOpen (R := R) j) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
  rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]

/-- The actual native coordinate support open is the absolute affine coordinate seminorm spectrum. -/
def nativeAbsoluteCoordinateHomeomorph (j : Fin (n + 1)) :
    {y : SchemeValuedPoint (NativeProjectiveScheme R n) // y.point ∈ nativeCoordinateOpen j} ≃ₜ
      Spectrum (CoordinateRing R j) :=
  (SchemeValuedPoint.affineOpenSpectrumHomeomorph (nativeCoordinateOpen_isAffine j)).trans
    (Spectrum.ringEquivHomeomorph (nativeCoordinateSectionsIso (R := R) j).commRingCatIsoToRingEquiv)

/-- The absolute native chart preserves every original coordinate-ring polynomial section. -/
theorem nativeAbsoluteCoordinateHomeomorph_val_apply (j : Fin (n + 1))
    (y : {y : SchemeValuedPoint (NativeProjectiveScheme R n) // y.point ∈ nativeCoordinateOpen j})
    (a : CoordinateRing R j) :
    (nativeAbsoluteCoordinateHomeomorph j y).val a =
      SchemeValuedPoint.eval y.1 (nativeCoordinateOpen j) y.2 ((nativeCoordinateSectionsIso j).hom a) :=
  SchemeValuedPoint.affineOpenSpectrumHomeomorph_val_apply (nativeCoordinateOpen_isAffine j) y _

end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}

/-- The canonical stalk-residue native point equals the whole actual relative native chart inverse. -/
theorem nativePoint_eq_chart_inverse (j : Fin (n + 1)) (x : chartOpen v j) :
    NormalizedProjectiveSpectrum.nativePoint x.1.1 =
      ((nativeCoordinateSpectrumHomeomorph v j).symm (coordinateChartHomeomorph v j x)).1.1 := by
  let y := (nativeCoordinateSpectrumHomeomorph v j).symm (coordinateChartHomeomorph v j x)
  have h := (nativeAbsoluteCoordinateHomeomorph (R := R) j).injective
    (show nativeAbsoluteCoordinateHomeomorph j
      ⟨NormalizedProjectiveSpectrum.nativePoint x.1.1, x.2⟩ =
        nativeAbsoluteCoordinateHomeomorph j ⟨y.1.1, y.2⟩ from by
      apply Spectrum.ext_val
      intro a
      rw [nativeAbsoluteCoordinateHomeomorph_val_apply,
        NormalizedProjectiveSpectrum.nativePoint_eval_coordinateChart,
        nativeAbsoluteCoordinateHomeomorph_val_apply]
      exact (nativeCoordinateSpectrumHomeomorph_symm_val v j
        (coordinateChartHomeomorph v j x) a))
  exact congrArg Subtype.val h

/-- All original coefficient values put the canonical native point above the whole prescribed base point. -/
theorem nativePoint_mem_relativeLocus (x : RelativeNormalizedProjectiveSpectrum v n) :
    NormalizedProjectiveSpectrum.nativePoint x.1 ∈
      SchemeValuedPoint.relativeLocus v (nativeStructureMap (R := R) (n := n)) := by
  obtain ⟨j, hj⟩ := exists_mem_chartOpen v x
  rw [nativePoint_eq_chart_inverse v j ⟨x, hj⟩]
  exact ((nativeCoordinateSpectrumHomeomorph v j).symm (coordinateChartHomeomorph v j ⟨x, hj⟩)).1.2

/-- Descend the true projective stalk valuation to its actual residue field, giving a canonical native point. -/
def nativePoint (x : RelativeNormalizedProjectiveSpectrum v n) :
    RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n)) :=
  ⟨NormalizedProjectiveSpectrum.nativePoint x.1, nativePoint_mem_relativeLocus v x⟩

/-- The prescribed-base packaging retains the entire canonical native residue valuation. -/
@[simp]
theorem nativePoint_val (x : RelativeNormalizedProjectiveSpectrum v n) :
    (nativePoint v x).1 = NormalizedProjectiveSpectrum.nativePoint x.1 := rfl

/-- The whole point map agrees with the genuine normalized/native relative chart comparison. -/
@[simp]
theorem nativePoint_onChart (j : Fin (n + 1)) (x : chartOpen v j) :
    nativePoint v x.1 =
      ((nativeCoordinateSpectrumHomeomorph v j).symm (coordinateChartHomeomorph v j x)).1 :=
  Subtype.ext (nativePoint_eq_chart_inverse v j x)

/-- Whole native points and their genuine affine charts determine the entire normalized seminorm. -/
theorem nativePoint_injective : Function.Injective (nativePoint v (n := n)) := by
  intro x y h
  obtain ⟨j, hx⟩ := exists_mem_chartOpen v x
  have hp := congrArg (fun z => z.1.point) h
  change NormalizedProjectiveSpectrum.nativeSupport x.1 =
    NormalizedProjectiveSpectrum.nativeSupport y.1 at hp
  have hy : y ∈ chartOpen v j := by
    change NormalizedProjectiveSpectrum.nativeSupport y.1 ∈ nativeCoordinateOpen j
    rw [← hp]
    exact hx
  have he : (nativeCoordinateSpectrumHomeomorph v j).symm (coordinateChartHomeomorph v j ⟨x, hx⟩) =
      (nativeCoordinateSpectrumHomeomorph v j).symm (coordinateChartHomeomorph v j ⟨y, hy⟩) := by
    apply Subtype.ext
    exact (nativePoint_onChart v j ⟨x, hx⟩).symm.trans (h.trans (nativePoint_onChart v j ⟨y, hy⟩))
  exact congrArg Subtype.val ((coordinateChartHomeomorph v j).injective
    ((nativeCoordinateSpectrumHomeomorph v j).symm.injective he))

/-- Every actual native prescribed-base point is recovered by a true coordinate Gauss inverse. -/
theorem nativePoint_surjective : Function.Surjective (nativePoint v (n := n)) := by
  intro y
  have hcov : y.1.point ∈ ⨆ j : Fin (n + 1), nativeCoordinateOpen (R := R) j := by
    rw [iSup_nativeCoordinateOpen_eq_top]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  let x := (coordinateChartHomeomorph v j).symm (nativeCoordinateSpectrumHomeomorph v j ⟨y, hj⟩)
  refine ⟨x.1, ?_⟩
  rw [nativePoint_onChart v j x]
  simp only [x, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- The canonical point map is continuous on the genuine covering coordinate opens, hence globally. -/
@[fun_prop]
theorem continuous_nativePoint : Continuous (nativePoint v (n := n)) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hx⟩ := exists_mem_chartOpen v x
  have hc : Continuous fun z : chartOpen v j => nativePoint v z.1 := by
    have ht : Continuous fun z : chartOpen v j =>
        ((nativeCoordinateSpectrumHomeomorph v j).symm (coordinateChartHomeomorph v j z)).1 :=
      continuous_subtype_val.comp ((nativeCoordinateSpectrumHomeomorph v j).symm.continuous.comp
        (coordinateChartHomeomorph v j).continuous)
    exact ht.congr (fun z => (nativePoint_onChart v j z).symm)
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt
    ((isOpen_chartOpen v j).mem_nhds hx)

private local instance nativeProjectiveSchemeSeparated : Scheme.IsSeparated (NativeProjectiveScheme R n) := by
  dsimp [NativeProjectiveScheme]
  infer_instance

private local instance nativeProjectivePointT2 :
    T2Space (RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n))) :=
  inferInstanceAs (T2Space {y : SchemeValuedPoint (NativeProjectiveScheme R n) //
    y ∈ SchemeValuedPoint.relativeLocus v nativeStructureMap})

/-- The actual prescribed-base native polynomial Proj space is homeomorphic to the normalized graded spectrum. -/
def nativeHomeomorph : RelativeNormalizedProjectiveSpectrum v n ≃ₜ
    RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n)) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (nativePoint v) ⟨nativePoint_injective v, nativePoint_surjective v⟩)
      (continuous_nativePoint v)

/-- The homeomorphism uses the canonical actual stalk-residue point construction. -/
@[simp]
theorem nativeHomeomorph_apply (x : RelativeNormalizedProjectiveSpectrum v n) :
    nativeHomeomorph v x = nativePoint v x := rfl

/-- The homeomorphism preserves the genuine homogeneous prime scheme support. -/
@[simp]
theorem nativeHomeomorph_point (x : RelativeNormalizedProjectiveSpectrum v n) :
    (nativeHomeomorph v x).1.point = NormalizedProjectiveSpectrum.nativeSupport x.1 := rfl

/-- The native homogeneous ideal remains the entire original polynomial valuation kernel. -/
@[simp]
theorem nativeHomeomorph_support_toIdeal (x : RelativeNormalizedProjectiveSpectrum v n) :
    (nativeHomeomorph v x).1.point.asHomogeneousIdeal.toIdeal = x.1.1.val.supp := rfl

/-- The homeomorphism preserves every affine polynomial as an actual coordinate-open section. -/
theorem nativeHomeomorph_val_apply (j : Fin (n + 1)) (x : chartOpen v j) (a : CoordinateRing R j) :
    SchemeValuedPoint.eval (nativeHomeomorph v x.1).1 (nativeCoordinateOpen j) x.2
      ((nativeCoordinateSectionsIso j).hom a) = (coordinateChartHomeomorph v j x).1.val a :=
  NormalizedProjectiveSpectrum.nativePoint_eval_coordinateChart x.1.1 j x.2 a

/-- The normalized and actual native relative coordinate charts commute as whole-point maps. -/
theorem nativeHomeomorph_chart (j : Fin (n + 1)) (x : chartOpen v j) :
    nativeCoordinateSpectrumHomeomorph v j ⟨nativeHomeomorph v x.1, x.2⟩ =
      coordinateChartHomeomorph v j x := by
  apply Subtype.ext
  apply Spectrum.ext_val
  intro a
  rw [nativeCoordinateSpectrumHomeomorph_val_apply]
  exact nativeHomeomorph_val_apply v j x a

/-- The inverse native homeomorphism is the genuine Gauss inverse in every actual coordinate chart. -/
theorem nativeHomeomorph_symm_onChart (j : Fin (n + 1))
    (y : {y : RelativeSchemeValuedPoint v (nativeStructureMap (R := R) (n := n)) //
      y.1.point ∈ nativeCoordinateOpen j}) :
    (nativeHomeomorph v).symm y.1 =
      ((coordinateChartHomeomorph v j).symm (nativeCoordinateSpectrumHomeomorph v j y)).1 := by
  apply (nativeHomeomorph v).injective
  rw [Homeomorph.apply_symm_apply, nativeHomeomorph_apply, nativePoint_onChart]
  simp only [Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- A homogeneous form has its original normalized value in a genuine chart whose coordinate has value one. -/
theorem nativeHomeomorph_eval_form_of_val_X_eq_one (x : RelativeNormalizedProjectiveSpectrum v n)
    (j : Fin (n + 1)) (hj : x.1.1.val (MvPolynomial.X j) = 1) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ ProjectiveGrading R n (d • (1 : ℕ))) :
    SchemeValuedPoint.eval (nativeHomeomorph v x).1 (nativeCoordinateOpen j)
      (show (nativeHomeomorph v x).1.point ∈ nativeCoordinateOpen j from by
        change x.1.1.val (MvPolynomial.X j) ≠ 0
        rw [hj]
        exact one_ne_zero)
      ((nativeHomogeneousChartSectionsIso j).hom
        (HomogeneousLocalization.Away.mk (ProjectiveGrading R n)
          (MvPolynomial.isHomogeneous_X R j) d F hF)) = x.1.1.val F := by
  simp only [nativeHomeomorph_apply, nativePoint_val]
  have hx : NormalizedProjectiveSpectrum.nativeSupport x.1 ∈ nativeCoordinateOpen j := by
    change x.1.1.val (MvPolynomial.X j) ≠ 0
    rw [hj]
    exact one_ne_zero
  erw [NormalizedProjectiveSpectrum.nativePoint_eval_homogeneousChart]
  change (Spectrum.awayLift (MvPolynomial.X j) x.1.1 hx).val
    (Localization.mk F (⟨MvPolynomial.X j ^ d, d, rfl⟩ : Submonoid.powers (MvPolynomial.X j))) = _
  rw [Localization.mk_eq_mk', Spectrum.awayLift, Spectrum.Away.lift,
    Valuation.extendToLocalization_mk', map_pow, hj, one_pow, inv_one, mul_one]

end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
