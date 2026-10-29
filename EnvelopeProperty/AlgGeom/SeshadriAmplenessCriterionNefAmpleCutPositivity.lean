import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionNefAmpleMixedIntersections
import EnvelopeProperty.AlgGeom.NativeNumericalAmpleClasses

/-! # Ample cuts in the dimension induction for nef plus ample

Let `X` be an integral projective scheme of dimension `d + 1` (resp. at most `d + 2`), let `A`
be ample and let `B` be an invertible module whose restriction to every closed subscheme of
dimension at most `d` (resp. `d + 1`) is ample. Cutting `X` by the zero scheme of a nonzero
section of a positive power of `A` we prove

* `Δ_A Δ_B^d χ(X, 𝒪_X) > 0` (`mixedEulerDifference_ample_cons_pos_of_closed_pullback_ample`),
* `Δ_A^2 Δ_B^d χ(X, 𝒪_X) ≥ 0`
  (`mixedEulerDifference_two_ample_cons_nonneg_of_closed_pullback_ample`).

Ampleness of `B` on `X` itself is not assumed: in the proof of
`SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef` the hypothesis on lower-dimensional
closed subschemes is the induction hypothesis, applied to `B = N^b ⊗ A^a`. These are the
positivity inputs `A · (N + tA)^d > 0` and `A^2 · (N + tA)^{d-1} ≥ 0` of Kleiman's theorem
(Lazarsfeld, *Positivity I*, proof of Theorem 1.4.9).

Blueprint: `seshadri-ampleness-criterion-nef-ample-cut-positivity.tex`.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionNefAmpleCutPositivity
open SeshadriAmplenessCriterion SeshadriAmplenessCriterionNefAmpleMixedIntersections
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem projective_closed_comp {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  exact ⟨E, hE, hEF, i ≫ j, inferInstance,
    (Category.assoc i j E.projectiveBundleπ).trans
      (congrArg (fun q => i ≫ q) hjp)⟩

private theorem unit_finiteType (X : Scheme.{u}) : (unitObj X).IsFiniteType := by
  let : (unitObj X).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := X.ringCatSheaf) (unitObj X)

/-- **First cut.** If `X` is integral of dimension `d + 1`, `A` is ample and `B` restricts
to an ample line on every closed subscheme of dimension at most `d`, then
`Δ_A Δ_B^d χ(X, 𝒪_X) > 0`. Ampleness of `B` on `X` is not assumed. -/
theorem mixedEulerDifference_ample_cons_pos_of_closed_pullback_ample
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p] (d : ℕ)
    (hdim : topologicalKrullDim X = (d + 1 : ℕ)) (A B : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (hB : IsInvertible B)
    (hclosed : ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i],
      topologicalKrullDim Y ≤ d →
        SchemeLineAmpleness.IsAmple (i ≫ p) ((Scheme.Modules.pullback i).obj B)) :
    0 < mixedEulerDifference p (A :: List.replicate d B) (unitObj X) := by
  have hls : ∀ L ∈ List.replicate d B, IsInvertible L := by
    intro L hL
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
    exact hB
  obtain ⟨eta, hproper, hdimZ⟩ := exists_pointClosure_dimension_eq d hdim
  let Z : Closeds X := ⟨closure ({eta} : Set X), isClosed_closure⟩
  let IZ := Scheme.IdealSheafData.vanishingIdeal Z
  let : IsIntegral IZ.subscheme := SchemePointClosureIntegral.isIntegral_pointClosure eta
  let : CompactSpace IZ.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace IZ.subschemeι
  let : IZ.subscheme.IsSeparated := ⟨by
    have hsep : IsSeparated (IZ.subschemeι ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  obtain ⟨r, hr, s, hs, j, hj, _htriangle⟩ :=
    ProjectiveAmpleSectionContainingClosedSubset.exists_nonzero_power_section_containing_closed
      p Z hproper A hA
  let P := CanonicalGeometry.bundleTensorPower A r
  let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 r
  let D := LineSectionZeroIdeal.zeroIdeal P hP s
  let i := D.subschemeι
  let j' : IZ.subscheme ⟶ D.subscheme := j
  let : IsClosedImmersion j' := hj
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := ⟨by
    have hsep : IsSeparated (i ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let : IsProjective (i ≫ p) := projective_closed_comp i p
  let : IsProjective (j' ≫ (i ≫ p)) := projective_closed_comp j' (i ≫ p)
  have hdimD : topologicalKrullDim D.subscheme ≤ d :=
    sectionZero_dimension_drop d hdim.le P hP s hs
  let BD := (Scheme.Modules.pullback i).obj B
  let BZ := (Scheme.Modules.pullback j').obj BD
  have hBD : SchemeLineAmpleness.IsAmple (i ≫ p) BD := hclosed i hdimD
  have hBZ : SchemeLineAmpleness.IsAmple (j' ≫ (i ≫ p)) BZ :=
    isAmple_closedPullback j' (i ≫ p) BD hBD
  have hZpos := mixedEulerDifference_replicate_pos_of_isAmple
    (j' ≫ (i ≫ p)) d hdimZ BZ hBZ
  have hmono := mixedEulerDifference_replicate_closed_unit_le (i ≫ p) d hdimD BD hBD j'
  have hDpos : 0 < mixedEulerDifference (i ≫ p) (List.replicate d BD) (unitObj D.subscheme) :=
    lt_of_lt_of_le hZpos hmono
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType := unit_finiteType X
  have hlsD : ∀ L ∈ List.replicate d BD, IsInvertible L := by
    intro L hL
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
    exact hBD.1
  let T := (Scheme.Modules.pullback i).obj (unitObj X ⊗ P)
  have hUP : IsInvertible (unitObj X ⊗ P) :=
    (isInvertible_unit.tensorObj hP).of_iso (ModularCurves.monoidalTensorObjIso (unitObj X) P)
  have hT : IsInvertible T := hUP.pullback i
  have hcoeff := mixedEulerDifference_eq_unit_of_dimension_le (i ≫ p) d hdimD
    (List.replicate d BD) (by simp) hlsD T hT
  have hcut := mixedEulerDifference_sectionDifference p P hP s hs
    (List.replicate d B) hls (unitObj X) isInvertible_unit
  simp only [List.map_replicate] at hcut
  change mixedEulerDifference p (P :: List.replicate d B) (unitObj X) =
    mixedEulerDifference (i ≫ p) (List.replicate d BD) T at hcut
  rw [mixedEulerDifference_tensorPower_cons p (d + 1) hdim.le A hA.1
    (List.replicate d B) (by simp) hls (unitObj X) r, hcoeff] at hcut
  have hmul : 0 < (r : ℤ) * mixedEulerDifference p
      (A :: List.replicate d B) (unitObj X) := by
    rw [hcut]
    exact hDpos
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  exact (mul_pos_iff_of_pos_left hrZ).mp hmul

/-- **Second cut.** If `X` is integral with `dim X ≤ d + 2`, `A` is ample and `B` restricts
to an ample line on every closed subscheme of dimension at most `d + 1`, then
`Δ_A Δ_A Δ_B^d χ(X, 𝒪_X) ≥ 0`. -/
theorem mixedEulerDifference_two_ample_cons_nonneg_of_closed_pullback_ample
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d + 1 + 1 : ℕ)) (A B : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (hB : IsInvertible B)
    (hclosed : ∀ {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i],
      topologicalKrullDim Y ≤ (d + 1 : ℕ) →
        SchemeLineAmpleness.IsAmple (i ≫ p) ((Scheme.Modules.pullback i).obj B)) :
    0 ≤ mixedEulerDifference p (A :: A :: List.replicate d B) (unitObj X) := by
  have hls : ∀ L ∈ A :: List.replicate d B, IsInvertible L := by
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hA.1
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL
      exact hB
  obtain ⟨r, hr, s, hs, _⟩ :=
    ProjectiveAmpleSectionContainingClosedSubset.exists_nonzero_power_section_containing_closed
      p ⊥ (closeds_bot_ne_top_of_isIntegral X) A hA
  let P := CanonicalGeometry.bundleTensorPower A r
  let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 r
  let D := LineSectionZeroIdeal.zeroIdeal P hP s
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := ⟨by
    have hsep : IsSeparated (i ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let : IsProjective (i ≫ p) := projective_closed_comp i p
  have hdimD : topologicalKrullDim D.subscheme ≤ (d + 1 : ℕ) :=
    sectionZero_dimension_drop (d + 1) hdim P hP s hs
  let AD := (Scheme.Modules.pullback i).obj A
  let BD := (Scheme.Modules.pullback i).obj B
  let T := (Scheme.Modules.pullback i).obj (unitObj X ⊗ P)
  have hAD : SchemeLineAmpleness.IsAmple (i ≫ p) AD := isAmple_closedPullback i p A hA
  have hBD : SchemeLineAmpleness.IsAmple (i ≫ p) BD := hclosed i hdimD
  have hnefAD := NativeRealNumericalClasses.ampleLineClass_mem_nefCone (i ≫ p) AD hAD
  have hUP : IsInvertible (unitObj X ⊗ P) :=
    (isInvertible_unit.tensorObj hP).of_iso (ModularCurves.monoidalTensorObjIso (unitObj X) P)
  have hT : IsInvertible T := hUP.pullback i
  let : T.IsQuasicoherent := hT.isQuasicoherent
  let : T.IsFinitePresentation := hT.isFinitePresentation
  let : T.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := D.subscheme.ringCatSheaf) T
  have hD := mixedEulerDifference_nef_ample_nonneg d (i ≫ p) hdimD AD hAD.1 hnefAD BD hBD T
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType := unit_finiteType X
  have hcut := mixedEulerDifference_sectionDifference p P hP s hs
    (A :: List.replicate d B) hls (unitObj X) isInvertible_unit
  simp only [List.map_cons, List.map_replicate] at hcut
  change mixedEulerDifference p (P :: A :: List.replicate d B) (unitObj X) =
    mixedEulerDifference (i ≫ p) (AD :: List.replicate d BD) T at hcut
  rw [mixedEulerDifference_tensorPower_cons p (d + 1 + 1) hdim A hA.1
    (A :: List.replicate d B) (by simp) hls (unitObj X) r] at hcut
  have hmul : 0 ≤ (r : ℤ) * mixedEulerDifference p
      (A :: A :: List.replicate d B) (unitObj X) := by
    rw [hcut]
    exact hD
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  exact (mul_nonneg_iff_of_pos_left hrZ).mp hmul

end EnvelopeProperty.SeshadriAmplenessCriterionNefAmpleCutPositivity
