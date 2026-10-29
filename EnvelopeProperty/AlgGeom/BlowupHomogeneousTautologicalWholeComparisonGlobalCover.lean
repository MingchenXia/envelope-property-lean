import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalFractionBases
import EnvelopeProperty.Alterations.Geometry.BlowupProjectiveEmbedding

/-! # The actual original finite-generator fraction cover of the native global blowup -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Alterations Alterations.Geometry.ProjectiveIdeal
  Alterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

/-- Every map is the actual prescribed-generator fraction inclusion followed by
the original native affine chart inclusion; all domain/open/cover facts are internal. -/
def specifiedOriginalGlobalFractionOpenCover
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) :
    (Alterations.Geometry.BlowupGluing.blowup
      ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j)).OpenCover := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let Z : Scheme.{u} := Alterations.Geometry.BlowupGluing.blowup D
  let μ : Z ⟶ X := Alterations.Geometry.BlowupGluing.blowupStructure D
  let A := {U : SubordinateAffineSite j // Nonempty U.1.1}
  let U₀ (a : A) : X.affineOpens := ⟨a.1.1.1, a.1.1.2⟩
  let _ (a : A) : IsDomain Γ(X, U₀ a) := by
    let : Nonempty a.1.1.1 := a.2
    exact IsIntegral.component_integral a.1.1.1
  let g (a : A) : Fin (m+1) → Γ(X, U₀ a) := fun row =>
    pulledForm j (U₀ a) (subordinateCoordinate j a.1) (subordinateCoordinate_le j a.1) (F row)
  let hgs (a : A) : Ideal.span (Set.range (g a)) = D.ideal (U₀ a) :=
    pulledForm_span_fin j (U₀ a) J F hspan
      (subordinateCoordinate j a.1) (subordinateCoordinate_le j a.1)
  let ι := Σ a : A, {row : Fin (m+1) // g a row ≠ 0}
  let W (a : ι) : Scheme.{u} :=
    Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal (U₀ a.1)) (g a.1 a.2.val)))
  let f (a : ι) : W a ⟶ Z :=
    affineBlowupChartInclusion (D.ideal (U₀ a.1)) (g a.1 a.2.val)
      (generator_mem (D.ideal (U₀ a.1)) (g a.1) (hgs a.1) a.2.val) a.2.property ≫
      Alterations.Geometry.BlowupGluing.chartInclusion D a.1.1.1
  let hfOpen : ∀ a : ι, IsOpenImmersion (f a) := by
    intro a
    let hc : IsOpenImmersion (affineBlowupChartInclusion (D.ideal (U₀ a.1)) (g a.1 a.2.val)
        (generator_mem (D.ideal (U₀ a.1)) (g a.1) (hgs a.1) a.2.val) a.2.property) :=
      affineBlowupChartInclusion_isOpenImmersion (D.ideal (U₀ a.1)) (g a.1 a.2.val)
        (generator_mem (D.ideal (U₀ a.1)) (g a.1) (hgs a.1) a.2.val) a.2.property
    let hk : IsOpenImmersion (Alterations.Geometry.BlowupGluing.chartInclusion D a.1.1.1) :=
      Alterations.Geometry.BlowupGluing.chartInclusion_isOpenImmersion D a.1.1.1
    let := hc
    let := hk
    infer_instance
  let := hfOpen
  exact Scheme.Cover.mkOfCovers ι W f (by
    intro z
    have hzCoord : j (μ z) ∈ ⨆ i : Fin (n+1), nativeCoordinateOpen (R := R) i := by
      rw [iSup_nativeCoordinateOpen_eq_top]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hzCoord
    obtain ⟨V, hV, hzV, hVi⟩ := exists_isAffineOpen_mem_and_subset
      (show μ z ∈ j ⁻¹ᵁ nativeCoordinateOpen i from hi)
    let V' : SubordinateAffineSite j := ⟨⟨V, hV⟩, i, hVi⟩
    let a : A := ⟨V', ⟨⟨μ z, hzV⟩⟩⟩
    have hzRange : z ∈ (Alterations.Geometry.BlowupGluing.chartInclusion D V'.1).opensRange := by
      rw [Alterations.Geometry.BlowupGluing.chartInclusion_opensRange]
      exact hzV
    obtain ⟨b, hb⟩ := hzRange
    have hbTop : b ∈ (⊤ : (affineBlowup (D.ideal (U₀ a))).Opens) := trivial
    rw [← iSup_specifiedNonzeroGeneratorChartOpen (D.ideal (U₀ a)) (g a) (hgs a)] at hbTop
    obtain ⟨row, hrow⟩ := TopologicalSpace.Opens.mem_iSup.mp hbTop
    have hbRange : b ∈ (affineBlowupChartInclusion (D.ideal (U₀ a)) (g a row.val)
        (generator_mem (D.ideal (U₀ a)) (g a) (hgs a) row.val) row.property).opensRange := by
      rw [affineBlowupFractionChartInclusion_opensRange]
      exact hrow
    obtain ⟨w, hw⟩ := hbRange
    refine ⟨⟨a, row⟩, w, ?_⟩
    change (Alterations.Geometry.BlowupGluing.chartInclusion D V'.1)
      ((affineBlowupChartInclusion (D.ideal (U₀ a)) (g a row.val)
        (generator_mem (D.ideal (U₀ a)) (g a) (hgs a) row.val) row.property) w) = z
    exact (congrArg (fun b : affineBlowup (D.ideal (U₀ a)) =>
      Alterations.Geometry.BlowupGluing.chartInclusion D V'.1 b) hw).trans hb)

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
