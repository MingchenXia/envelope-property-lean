import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveNativeInverse

/-!
# Actual global pullback of native hyperplane equations to the ORIGINAL equations

All local coefficients and section maps are the genuine original/global maps.
The numerator coordinate is arbitrary, including vanishing coordinates.
Route: owned `closed-projective-hyperplane-pullbacks-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open DeJongAlterations DeJongAlterations.Geometry DeJongAlterations.Geometry.Segre
  DeJongAlterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]
variable (s : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)]

/-- Actual whole chart restriction internally gives the genuine native-open containment. -/
theorem fixedOriginalNativeMap_chartContainment :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange ≤
      (fixedOriginalNativeMap i j) ⁻¹ᵁ
        (originalRankOneCoordinateModel i j).nativeRankOneCoordinateOpen s := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let U := M.nativeRankOneCoordinateOpen s
  let e := fixedOriginalNativeCoordinateChartIso i j s
  intro x hx
  let z : V := ⟨x, hx⟩
  have h := congrArg (fun f : V.toScheme ⟶ M.nativeRankOneScheme => f z)
    (fixedOriginalNativeMap_onChart i j s)
  change fixedOriginalNativeMap i j x = U.ι (e.hom z) at h
  change fixedOriginalNativeMap i j x ∈ U
  rw [h]
  exact (e.hom z).property

/-- The ENTIRE actual original homogeneous coordinate coefficient has its literal fixed-model ratio. -/
theorem fixedOriginalCoordinateChartSectionsAlgEquiv_coordinate (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    letI := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
      (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)
    ((fixedOriginalCoordinateChartSectionsAlgEquiv i j s)
      (i.app (coordinateChartInclusion (R := k) s).opensRange
        (homogeneousCoordinateOnChartRange (R := k) s l)) : X.functionField) =
      (originalRankOneCoordinateModel i j).coord 0 l /
        (originalRankOneCoordinateModel i j).coord 0 s := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra
    (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)
  rw [fixedOriginalCoordinateChartSectionsAlgEquiv_apply]
  exact (projectiveCoordinateGenericHom_homogeneous i s l).symm.trans
    (fixedOriginalCoordinateModel_coord_div i j s 0 l).symm

/-- The ACTUAL inverse whole chart pullback identifies the original coordinate and native hyperplane equation. -/
theorem fixedOriginalNativeCoordinateChartIso_hyperplane_inv (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let U := M.nativeRankOneCoordinateOpen s
    (V.topIso.inv ≫ (fixedOriginalNativeCoordinateChartIso i j s).inv.appTop ≫ U.topIso.hom)
        (i.app (coordinateChartInclusion (R := k) s).opensRange
          (homogeneousCoordinateOnChartRange (R := k) s l)) =
      M.nativeRankOneHyperplaneLocalEquation s l := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let U := M.nativeRankOneCoordinateOpen s
  let _ := (i ≫ projectiveSpaceStructure k n).sectionsAlgebra V
  let q := i.app (coordinateChartInclusion (R := k) s).opensRange
    (homogeneousCoordinateOnChartRange (R := k) s l)
  let b : M.ChartIndex := fun _ => s
  let hb := fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j s d
  have h := ConcreteCategory.congr_hom
    (fixedOriginalNativeCoordinateChartIso_sections i j s) q
  change _ = (M.nativeRankOneOriginalSectionsIso b hb).hom
    ((fixedOriginalCoordinateChartSectionsAlgEquiv i j s) q) at h
  calc
    _ = (M.nativeRankOneOriginalSectionsIso b hb).hom
        ((fixedOriginalCoordinateChartSectionsAlgEquiv i j s) q) := h
    _ = (M.nativeRankOneOriginalSectionsIso b hb).hom
        ⟨M.coord 0 l / M.coord 0 s, M.coord_div_mem_chartAlg b 0 l⟩ := by
      congr 1
      apply Subtype.ext
      exact fixedOriginalCoordinateChartSectionsAlgEquiv_coordinate i j s l
    _ = M.nativeRankOneHyperplaneLocalEquation s l :=
      (M.nativeRankOneHyperplaneLocalEquation_original b hb l).symm

/-- The actual forward whole chart pullback is the LITERAL ORIGINAL projective hyperplane equation. -/
theorem fixedOriginalNativeCoordinateChartIso_hyperplane_hom (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let U := M.nativeRankOneCoordinateOpen s
    (U.topIso.inv ≫ (fixedOriginalNativeCoordinateChartIso i j s).hom.appTop ≫ V.topIso.hom)
        (M.nativeRankOneHyperplaneLocalEquation s l) =
      i.app (coordinateChartInclusion (R := k) s).opensRange
        ((projectiveSpace k n).presheaf.map
          (eqToHom (projectiveCoordinateChart_opensRange (R := k) s)).op
          (MvPolynomial.coordinateHyperplaneLocalEquation (R := k) s l)) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let U := M.nativeRankOneCoordinateOpen s
  let e := fixedOriginalNativeCoordinateChartIso i j s
  let f := V.topIso.inv ≫ e.inv.appTop ≫ U.topIso.hom
  let g := U.topIso.inv ≫ e.hom.appTop ≫ V.topIso.hom
  let q := i.app (coordinateChartInclusion (R := k) s).opensRange
    (homogeneousCoordinateOnChartRange (R := k) s l)
  have he : e.inv.appTop ≫ e.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
  have hfg : f ≫ g = 𝟙 _ := by
    dsimp only [f, g]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc e.inv.appTop e.hom.appTop V.topIso.hom, he]
    simp only [Category.id_comp, Iso.inv_hom_id]
  have h : f q = M.nativeRankOneHyperplaneLocalEquation s l :=
    fixedOriginalNativeCoordinateChartIso_hyperplane_inv i j s l
  have hc := ConcreteCategory.congr_hom hfg q
  change g (f q) = q at hc
  rw [h] at hc
  simpa only [g, e, q, homogeneousCoordinateOnChartRange,
    ProjectiveHomogeneousSections.coefficient_X] using hc

/-- The actual GLOBAL Scheme section pullback retains the literal ORIGINAL hyperplane equation. -/
theorem fixedOriginalNativeMap_hyperplane (l : Fin (n + 1)) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let U := M.nativeRankOneCoordinateOpen s
    (fixedOriginalNativeMap i j).appLE U V (fixedOriginalNativeMap_chartContainment i j s)
        (M.nativeRankOneHyperplaneLocalEquation s l) =
      i.app (coordinateChartInclusion (R := k) s).opensRange
        ((projectiveSpace k n).presheaf.map
          (eqToHom (projectiveCoordinateChart_opensRange (R := k) s)).op
          (MvPolynomial.coordinateHyperplaneLocalEquation (R := k) s l)) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let U := M.nativeRankOneCoordinateOpen s
  let F := fixedOriginalNativeMap i j
  let e := fixedOriginalNativeCoordinateChartIso i j s
  let hVU := fixedOriginalNativeMap_chartContainment i j s
  have hr : F.resLE U V hVU = e.hom := by
    apply (cancel_mono U.ι).mp
    rw [Scheme.Hom.resLE_comp_ι, fixedOriginalNativeMap_onChart]
    rfl
  have ha := F.resLE_app_top hVU
  change (F.resLE U V hVU).appTop = U.topIso.hom ≫ F.appLE U V hVU ≫ V.topIso.inv at ha
  rw [hr] at ha
  have happ : F.appLE U V hVU = U.topIso.inv ≫ e.hom.appTop ≫ V.topIso.hom := by
    calc
      _ = U.topIso.inv ≫ (U.topIso.hom ≫ F.appLE U V hVU ≫ V.topIso.inv) ≫
          V.topIso.hom := by simp only [Category.assoc, Iso.inv_hom_id_assoc,
            Iso.inv_hom_id, Category.comp_id]
      _ = _ := by rw [← ha]
  have hval := ConcreteCategory.congr_hom happ (M.nativeRankOneHyperplaneLocalEquation s l)
  exact hval.trans (fixedOriginalNativeCoordinateChartIso_hyperplane_hom i j s l)

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_chartContainment
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_chartContainment
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartSectionsAlgEquiv_coordinate
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalCoordinateChartSectionsAlgEquiv_coordinate
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_hyperplane_inv
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_hyperplane_inv
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_hyperplane_hom
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_hyperplane_hom
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplane
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_hyperplane
