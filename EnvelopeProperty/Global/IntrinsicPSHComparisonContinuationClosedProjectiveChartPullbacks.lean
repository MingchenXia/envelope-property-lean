import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveAllOriginalChartAlgebras
import EnvelopeProperty.Global.NativeRankOneAnalyticCharts

/-!
# Actual fixed original/native chart scheme isomorphisms retain their whole pullback

The entire section identity is DERIVED from actual canonical affine/native
scheme isomorphisms. No section/frame matching certificate is assumed.
Route: owned `closed-projective-chart-pullbacks-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native WHOLE original-chart section map is its actual geometric spectrum-chart pullback. -/
theorem nativeOriginalSectionsIso_geometric {k K : Type u} [Field k] [Field K]
    [Algebra k K] (M : MultiModel k K 1) (b : M.ChartIndex)
    (hb : ∀ c, M.coord c (b c) ≠ 0) :
    M.nativeRankOneOriginalSectionsIso b hb =
      (Scheme.ΓSpecIso (.of (M.chartAlg b))).symm ≪≫
        Scheme.Γ.mapIso (M.nativeRankOneOriginalChartIso b hb).op ≪≫
          (M.nativeRankOneCoordinateOpen (b 0)).topIso := by
  have hhom : (M.nativeRankOneHomogeneousSectionsIso (b 0)).hom =
      (Scheme.ΓSpecIso (.of (M.nativeRankOneChartRing (b 0)))).inv ≫
        (M.nativeRankOneHomogeneousChartIso (b 0)).hom.appTop ≫
          (M.nativeRankOneCoordinateOpen (b 0)).topIso.hom := by
    change (Proj.basicOpenIsoAway M.nativeTotalGrading (M.coordElem ⟨0, b 0⟩)
      (M.nativeRankOneCoordinate_mem (b 0)) (by decide : 0 < (1 : ℕ))).hom = _
    rw [MultiModel.nativeRankOneHomogeneousChartIso, Proj.basicOpenIsoSpec_hom]
    simp only [Scheme.Hom.appTop]
    rw [Proj.basicOpenToSpec_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso (.of (M.chartAlg b))).inv ≫
    (Spec.map (CommRingCat.ofHom (M.nativeRankOneChartEquiv b hb).symm.toRingHom)).appTop ≫
      (M.nativeRankOneHomogeneousChartIso (b 0)).hom.appTop ≫
        (M.nativeRankOneCoordinateOpen (b 0)).topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  change CommRingCat.ofHom (M.nativeRankOneChartEquiv b hb).symm.toRingHom ≫
    (M.nativeRankOneHomogeneousSectionsIso (b 0)).hom = _
  simpa only [Category.assoc] using congrArg
    (fun g : CommRingCat.of (M.nativeRankOneChartRing (b 0)) ⟶
        Γ(M.nativeRankOneScheme, M.nativeRankOneCoordinateOpen (b 0)) =>
      CommRingCat.ofHom (M.nativeRankOneChartEquiv b hb).symm.toRingHom ≫ g) hhom

/-- A canonical actual affine-open spectrum comparison retains the SAME WHOLE original inverse ring map. -/
theorem affineOpenSectionsRingIso_geometric {X : Scheme.{u}} (V : X.Opens)
    (hV : IsAffineOpen V) {A : CommRingCat.{u}} (e : Γ(X, V) ≃+* A) :
    e.symm.toCommRingCatIso =
      (Scheme.ΓSpecIso A).symm ≪≫
        Scheme.Γ.mapIso (hV.isoSpec ≪≫ (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm).op ≪≫
          V.topIso := by
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso A).inv ≫
    (Spec.map (CommRingCat.ofHom e.symm.toRingHom)).appTop ≫ hV.isoSpec.hom.appTop ≫ V.topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rw [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_appTop]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change CommRingCat.ofHom e.symm.toRingHom =
    CommRingCat.ofHom e.symm.toRingHom ≫
      (Scheme.ΓSpecIso Γ(X, V)).inv ≫ (Scheme.ΓSpecIso Γ(X, V)).hom
  simp only [Iso.inv_hom_id, Category.comp_id]

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]
variable (s : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)]

/-- The actual inverse original/native chart iso induces EXACTLY the constructed entire original section map. -/
theorem fixedOriginalNativeCoordinateChartIso_sections :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
      (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)
    let M := originalRankOneCoordinateModel i j
    let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let U := M.nativeRankOneCoordinateOpen s
    V.topIso.inv ≫ (fixedOriginalNativeCoordinateChartIso i j s).inv.appTop ≫ U.topIso.hom =
      CommRingCat.ofHom (fixedOriginalCoordinateChartSectionsAlgEquiv i j s).toRingHom ≫
        (M.nativeRankOneOriginalSectionsIso (fun _ => s)
          (fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j s c)).hom := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra V
  let M := originalRankOneCoordinateModel i j
  let b : M.ChartIndex := fun _ => s
  let hb := fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j s c
  let U := M.nativeRankOneCoordinateOpen s
  let E := fixedOriginalCoordinateChartSectionsAlgEquiv i j s
  let o := fixedOriginalCoordinateChartIso i j s
  let q := M.nativeRankOneOriginalChartIso b hb
  have hV : IsAffineOpen V :=
    (isAffineOpen_opensRange (coordinateChartInclusion (R := k) s)).preimage i
  have hE := affineOpenSectionsRingIso_geometric (X := X) V hV
    (A := .of (M.chartAlg b)) E.toRingEquiv
  change E.symm.toRingEquiv.toCommRingCatIso =
    (Scheme.ΓSpecIso (.of (M.chartAlg b))).symm ≪≫ Scheme.Γ.mapIso o.op ≪≫ V.topIso at hE
  have ho := congrArg
    (fun e : CommRingCat.of (M.chartAlg b) ≅ Γ(X, V) => e.inv) hE
  change CommRingCat.ofHom E.toRingHom =
    V.topIso.inv ≫ o.inv.appTop ≫ (Scheme.ΓSpecIso (.of (M.chartAlg b))).hom at ho
  have hn := congrArg
    (fun e : CommRingCat.of (M.chartAlg b) ≅ Γ(M.nativeRankOneScheme, U) => e.hom)
      (nativeOriginalSectionsIso_geometric M b hb)
  change (M.nativeRankOneOriginalSectionsIso b hb).hom =
    (Scheme.ΓSpecIso (.of (M.chartAlg b))).inv ≫ q.hom.appTop ≫ U.topIso.hom at hn
  change V.topIso.inv ≫ (q.hom ≫ o.inv).appTop ≫ U.topIso.hom =
    CommRingCat.ofHom E.toRingHom ≫ (M.nativeRankOneOriginalSectionsIso b hb).hom
  rw [Scheme.Hom.comp_appTop, hn, ho]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.nativeOriginalSectionsIso_geometric
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.nativeOriginalSectionsIso_geometric
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.affineOpenSectionsRingIso_geometric
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.affineOpenSectionsRingIso_geometric
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_sections
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_sections
