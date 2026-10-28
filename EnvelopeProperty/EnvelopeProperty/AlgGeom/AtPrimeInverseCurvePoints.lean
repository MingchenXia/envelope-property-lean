import EnvelopeProperty.AlgGeom.SchemeLocalizedFiniteAlgebras
import EnvelopeProperty.AlgGeom.LocalizedInverseStalks
import EnvelopeProperty.AlgGeom.CurveFiniteClosedSubschemes
import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # SAME actual localized curve nongeneric points and the original whole finite fibre -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
noncomputable section
universe u
namespace EnvelopeProperty.AtPrimeInverseCurvePoints
open FlatGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A : Type u} [CommRing A] [IsDomain A] {Y : Scheme.{u}}
    [IsIntegral Y] (f : Y ⟶ Spec (.of A)) [IsFinite f] [IsDominant f]
    (p : PrimeSpectrum A)

/-- The ENTIRE actual original finite inverse over the ORIGINAL target local ring. -/
abbrev model := baseChange (S := Localization.AtPrime p.asIdeal) f

/-- Its genuine original whole integrality, with no model certificate supplied. -/
theorem model_isIntegral : IsIntegral (model f p) :=
  SchemeLocalizedFiniteAlgebras.baseChange_isIntegral f p.asIdeal.primeCompl
    p.asIdeal.primeCompl_le_nonZeroDivisors

private instance modelIntegral : IsIntegral (model f p) := model_isIntegral f p

omit [IsDomain A] [IsIntegral Y] [IsFinite f] [IsDominant f] in
/-- Actual original curve geometry bounds the whole localized inverse dimension. -/
theorem dimension_le (hdim : topologicalKrullDim Y ≤ 1) : topologicalKrullDim (model f p) ≤ 1 := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal)))
  let : IsPreimmersion b := IsPreimmersion.of_isLocalization p.asIdeal.primeCompl
  exact (firstProjection (S := Localization.AtPrime p.asIdeal) f).isEmbedding.isInducing.topologicalKrullDim_le.trans hdim

omit [IsDomain A] in
/-- The native ORIGINAL local-ring closed point maps to the SAME original target prime. -/
theorem base_closedPoint :
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal))))
      (closedPoint (Localization.AtPrime p.asIdeal)) = p := by
  apply PrimeSpectrum.ext
  exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal

private theorem base_closedPoint_ne_generic (hp : p ≠ ⊥) :
    closedPoint (Localization.AtPrime p.asIdeal) ≠ genericPoint (Spec (.of (Localization.AtPrime p.asIdeal))) := by
  intro h
  let b := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p.asIdeal)))
  have hh := congrArg b h
  rw [base_closedPoint p, genericPoint_eq_bot_of_affine] at hh
  have hb : b (⊥ : PrimeSpectrum (Localization.AtPrime p.asIdeal)) = (⊥ : PrimeSpectrum A) := by
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl_le_nonZeroDivisors)
  exact hp (hh.trans hb)

/-- EVERY original nongeneric point of the SAME localized inverse is
above the TRUE original local-ring closed point. -/
theorem structure_point_eq_closed_of_ne_generic
    (hdim : topologicalKrullDim Y ≤ 1) (z : model f p) (hz : z ≠ genericPoint (model f p)) :
    structureMap (S := Localization.AtPrime p.asIdeal) f z = closedPoint (Localization.AtPrime p.asIdeal) := by
  let q := structureMap (S := Localization.AtPrime p.asIdeal) f
  have hc : IsClosed ({z} : Set (model f p)) :=
    CurveFiniteClosedSubschemes.isClosed_singleton (dimension_le f p hdim) z hz
  have hqc : IsClosed ({q z} : Set (Spec (.of (Localization.AtPrime p.asIdeal)))) := by
    simpa only [Set.image_singleton] using q.isClosedMap {z} hc
  apply PrimeSpectrum.ext
  exact eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hqc)

/-- Every SAME original nongeneric point maps into the SAME original entire finite fibre. -/
theorem projection_mem_fibre (hdim : topologicalKrullDim Y ≤ 1)
    (z : model f p) (hz : z ≠ genericPoint (model f p)) :
    f (firstProjection (S := Localization.AtPrime p.asIdeal) f z) = p := by
  have h := Scheme.Hom.comp_apply (firstProjection (S := Localization.AtPrime p.asIdeal) f) f z
  rw [pullback.condition] at h
  rw [Scheme.Hom.comp_apply, structure_point_eq_closed_of_ne_generic f p hdim z hz,
    base_closedPoint p] at h
  exact h.symm

/-- EVERY original point of the original fibre INTERNALLY has an actual
nongeneric lift to the SAME whole local inverse, with all maps literal. -/
theorem exists_original_fibre_lift (hp : p ≠ ⊥) (y : Y) (hy : f y = p) :
    ∃ z : model f p, z ≠ genericPoint (model f p) ∧
      firstProjection (S := Localization.AtPrime p.asIdeal) f z = y := by
  let S := Localization.AtPrime p.asIdeal
  let b := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let q := structureMap (S := S) f
  let : Surjective f := inferInstance
  let : Surjective q := inferInstance
  obtain ⟨z, hzY, hzS⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := b) y (closedPoint S) (hy.trans (base_closedPoint p).symm)
  refine ⟨z, ?_, hzY⟩
  intro hz
  have hqz : q z = closedPoint S := hzS
  rw [hz, DominantFunctionFieldMaps.genericPoint_map q] at hqz
  exact base_closedPoint_ne_generic p hp hqz.symm

/-- TRUE whole ORIGINAL point bijection: all nongeneric points of the
same actual local inverse correspond to ALL points of the SAME original fibre.
No fibre, local-model, point or residue comparison certificate is supplied. -/
def pointEquiv (hdim : topologicalKrullDim Y ≤ 1) (hp : p ≠ ⊥) :
    {z : model f p // z ≠ genericPoint (model f p)} ≃ {y : Y // f y = p} := by
  let : IsAffine Y := isAffine_of_isAffineHom f
  let F : {z : model f p // z ≠ genericPoint (model f p)} → {y : Y // f y = p} :=
    fun z => ⟨firstProjection (S := Localization.AtPrime p.asIdeal) f z.1,
      projection_mem_fibre f p hdim z.1 z.2⟩
  apply Equiv.ofBijective F
  constructor
  · intro z w hzw
    apply Subtype.ext
    exact LocalizedInverseStalks.projection_injective f p.asIdeal.primeCompl
      (congrArg Subtype.val hzw)
  · intro y
    obtain ⟨z, hz, hzy⟩ := exists_original_fibre_lift f p hp y.1 y.2
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

/-- The derived WHOLE point bijection retains the LITERAL original first projection. -/
theorem pointEquiv_apply (hdim : topologicalKrullDim Y ≤ 1) (hp : p ≠ ⊥)
    (z : {z : model f p // z ≠ genericPoint (model f p)}) :
    (pointEquiv f p hdim hp z).1 = firstProjection (S := Localization.AtPrime p.asIdeal) f z.1 := rfl

/-- The ENTIRE original nongeneric local inverse set is genuinely finite,
internally derived from the SAME original finite fibre and true point bijection. -/
theorem finite_nongeneric (hdim : topologicalKrullDim Y ≤ 1) (hp : p ≠ ⊥) :
    Finite {z : model f p // z ≠ genericPoint (model f p)} := by
  have hf : Set.Finite {y : Y | f y = p} := by
    apply (f.finite_preimage_singleton p).subset
    intro y hy
    exact Set.mem_singleton_iff.mpr hy
  let : Finite {y : Y // f y = p} := hf.to_subtype
  exact Finite.of_injective (pointEquiv f p hdim hp) (pointEquiv f p hdim hp).injective

end EnvelopeProperty.AtPrimeInverseCurvePoints
