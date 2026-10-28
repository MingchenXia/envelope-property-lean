import EnvelopeProperty.AlgGeom.NativeProjectiveVarietyComparison
import EnvelopeProperty.Projective.NativeBridge

/-! # The ORIGINAL analytic variety is the valued-point space of its ORIGINAL scheme -/

open scoped Classical NNReal Topology
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjSubvariety

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)

/-- The original analytic zero locus is EXACTLY the original whole ideal-sheaf
support condition at the SAME actual native scheme support point. -/
theorem nativeSupport_mem_original_ideal_iff (x : ProjBerk k n) :
    (ProjBerk.nativeHomeomorph x).1.point ∈ X.nativeIdeal.support ↔ x ∈ X.an := by
  change (ProjBerk.nativeHomeomorph x).1.point ∈
    (GradedQuotient.quotientIdealSheaf _ X.nativeHomogeneousIdeal).support ↔ _
  rw [← SetLike.mem_coe, GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus]
  change X.ideal ≤ (ProjBerk.nativeHomeomorph x).1.point.asHomogeneousIdeal.toIdeal ↔ _
  rw [ProjBerk.nativeHomeomorph_support_toIdeal]
  rfl

/-- The original analytic variety is the ENTIRE original normalized closed locus. -/
def originalNormalizedClosedHomeomorph : X.an ≃ₜ
    ProjBerk.normalizedClosedLocus (1 : Valuation k ℝ≥0) X.nativeInclusion :=
  ProjBerk.normalizedSpectrumHomeomorph.subtype fun x => by
    change x ∈ X.an ↔ (ProjBerk.nativeHomeomorph x).1.point ∈ Set.range X.nativeInclusion
    rw [show Set.range X.nativeInclusion = X.nativeIdeal.support from
      X.nativeIdeal.range_subschemeι]
    exact (X.nativeSupport_mem_original_ideal_iff x).symm

/-- The ORIGINAL whole analytic variety is canonically homeomorphic to actual
residue-field-valued points of its EXISTING original native scheme over the trivial base. -/
def nativeAnalyticHomeomorph : X.an ≃ₜ
    Berkovich.RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeStructure :=
  X.originalNormalizedClosedHomeomorph.trans
    (ProjBerk.nativeClosedProjectiveHomeomorph (1 : Valuation k ℝ≥0) X.nativeInclusion).symm

private theorem nativeClosed_map_symm {Y : Scheme.{u}}
    (g : Y ⟶ ProjBerk.NativeProjectiveScheme k n) [IsClosedImmersion g]
    (z : ProjBerk.normalizedClosedLocus (1 : Valuation k ℝ≥0) g) :
    Berkovich.RelativeSchemeValuedPoint.map g rfl
        ((ProjBerk.nativeClosedProjectiveHomeomorph (1 : Valuation k ℝ≥0) g).symm z) =
      Berkovich.RelativeNormalizedProjectiveSpectrum.nativeHomeomorph
        (1 : Valuation k ℝ≥0) z.1 := by
  have h := ProjBerk.nativeClosedProjectiveHomeomorph_apply
    (1 : Valuation k ℝ≥0) g
      ((ProjBerk.nativeClosedProjectiveHomeomorph (1 : Valuation k ℝ≥0) g).symm z)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- The entire analytic comparison retains the LITERAL original native closed
inclusion point, not merely its abstract topological support. -/
theorem nativeAnalyticHomeomorph_inclusion (x : X.an) :
    Berkovich.RelativeSchemeValuedPoint.map X.nativeInclusion rfl
        (X.nativeAnalyticHomeomorph x) = ProjBerk.nativeHomeomorph x.1 :=
  nativeClosed_map_symm X.nativeInclusion (X.originalNormalizedClosedHomeomorph x)

/-- Every ORIGINAL affine coordinate domain is the SAME original scheme preimage open. -/
theorem nativeAnalyticHomeomorph_mem_coordinateOpen (x : X.an) (j : Fin (n+1)) :
    (X.nativeAnalyticHomeomorph x).1.point ∈
        X.nativeInclusion ⁻¹ᵁ ProjBerk.nativeCoordinateOpen j ↔
      x.1 ∈ ProjBerk.chartOpen j := by
  change (Berkovich.RelativeSchemeValuedPoint.map X.nativeInclusion rfl
    (X.nativeAnalyticHomeomorph x)).1.point ∈ ProjBerk.nativeCoordinateOpen j ↔ _
  rw [nativeAnalyticHomeomorph_inclusion]
  rfl

private theorem eval_congr {Z : Scheme.{u}} (y z : Berkovich.SchemeValuedPoint Z)
    (h : y = z) (U : Z.Opens) (hy : y.point ∈ U) (hz : z.point ∈ U)
    (s : Γ(Z, U)) : y.eval U hy s = z.eval U hz s := by
  subst z
  rfl

/-- EVERY original affine coordinate polynomial has exactly its original
seminorm value on the SAME actual pulled-back whole coordinate section. -/
theorem nativeAnalyticHomeomorph_eval_coordinate (x : X.an) (j : Fin (n+1))
    (hx : x.1 ∈ ProjBerk.chartOpen j) (a : ProjBerk.CoordinateRing k j) :
    Berkovich.SchemeValuedPoint.eval (X.nativeAnalyticHomeomorph x).1
      (X.nativeInclusion ⁻¹ᵁ ProjBerk.nativeCoordinateOpen j)
      ((X.nativeAnalyticHomeomorph_mem_coordinateOpen x j).mpr hx)
      (X.nativeInclusion.app (ProjBerk.nativeCoordinateOpen j)
        ((ProjBerk.nativeCoordinateSectionsIso j).hom a)) =
      (ProjBerk.coordinateChartMap j ⟨x.1, hx⟩).val a := by
  have h := ProjBerk.nativeHomeomorph_val_apply j ⟨x.1, hx⟩ a
  have heq := congrArg Subtype.val (X.nativeAnalyticHomeomorph_inclusion x)
  have hv := eval_congr _ _ heq (ProjBerk.nativeCoordinateOpen j)
    ((X.nativeAnalyticHomeomorph_mem_coordinateOpen x j).mpr hx) hx
    ((ProjBerk.nativeCoordinateSectionsIso j).hom a)
  exact (Berkovich.SchemeValuedPoint.eval_map X.nativeInclusion
    (X.nativeAnalyticHomeomorph x).1 (ProjBerk.nativeCoordinateOpen j)
    ((X.nativeAnalyticHomeomorph_mem_coordinateOpen x j).mpr hx)
    ((ProjBerk.nativeCoordinateSectionsIso j).hom a)).symm.trans (hv.trans h)

end EnvelopeProperty.ProjSubvariety
