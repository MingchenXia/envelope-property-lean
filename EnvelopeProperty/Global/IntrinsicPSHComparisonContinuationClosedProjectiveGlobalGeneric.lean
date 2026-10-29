import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveGlobalMap
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeBaseScalars
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeArbitraryFieldProperness
import EnvelopeProperty.ProperPruferGenericExtension

/-!
# The actual global original/native map is over the original field and surjective

All generic, coefficient and structural matching is proved from the original
closed projective embedding and its genuine fixed native model.
Route: owned `closed-projective-global-generic-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual point's structural stalk map is the literal whole structural constant germ. -/
theorem pointStructureMap_wholeConstants {A : CommRingCat.{u}} {Y : Scheme.{u}}
    (p : Y ⟶ Spec A) (y : Y) :
    Y.fromSpecStalk y ≫ p =
      Spec.map ((Scheme.ΓSpecIso A).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial) := by
  apply (cancel_mono (Spec A).toSpecΓ).mp
  calc
    (Y.fromSpecStalk y ≫ p) ≫ (Spec A).toSpecΓ =
        (Y.fromSpecStalk y ≫ Y.toSpecΓ) ≫ Spec.map p.appTop := by
      rw [Category.assoc, Category.assoc, Scheme.toSpecΓ_naturality]
    _ = Spec.map (p.appTop ≫ Y.presheaf.germ ⊤ y trivial) := by
      rw [Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    _ = Spec.map ((Scheme.ΓSpecIso A).inv ≫ p.appTop ≫
        Y.presheaf.germ ⊤ y trivial) ≫ (Spec A).toSpecΓ := by
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
      simp only [Iso.hom_inv_id_assoc]

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- The actual native field comparison preserves original and native WHOLE structural constants. -/
theorem fixedOriginalNativeFieldEquiv_wholeConstants (c : k) :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let Φ := M.nativeRankOneFunctionFieldEquiv (fun _ => j)
      (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j j d)
    Φ (X.germToFunctionField ⊤ (((Scheme.ΓSpecIso (.of k)).inv ≫
        (i ≫ projectiveSpaceStructure k n).appTop) c)) =
      M.nativeRankOneScheme.germToFunctionField ⊤ (M.nativeRankOneBaseConstants c) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let p := i ≫ projectiveSpaceStructure k n
  let M := originalRankOneCoordinateModel i j
  have hX : X.germToFunctionField ⊤
      (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) c) = algebraMap k X.functionField c := by
    let _ := p.sectionsAlgebra ⊤
    have h := (p.sectionsFunctionFieldAlgHom ⊤).commutes c
    change X.germToFunctionField ⊤
      (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ ⊤ le_top) c) =
        algebraMap k X.functionField c at h
    have happ : p.appLE ⊤ ⊤ le_top = p.appTop := by
      simp [Scheme.Hom.appLE]
    rw [happ] at h
    exact h
  rw [hX]
  exact M.nativeRankOneFunctionFieldEquiv_baseConstants _ _ c

/-- The ONE glued global map retains its actual fixed-reference generic Scheme triangle. -/
theorem fixedOriginalNativeMap_genericTriangle :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    X.fromSpecStalk (genericPoint X) ≫ fixedOriginalNativeMap i j =
      Spec.map (CommRingCat.ofHom (M.nativeRankOneFunctionFieldEquiv (fun _ => j)
        (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j j d)).symm.toRingHom) ≫
      M.nativeRankOneScheme.fromSpecStalk (genericPoint M.nativeRankOneScheme) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange
  let dV := V.isOpen.dense (by simpa using (inferInstance : Nonempty V))
  rw [← DenseOpenGenericFieldLift.lift_inclusion V dV, Category.assoc,
    fixedOriginalNativeMap_onChart]
  exact fixedOriginalNativeCoordinateChartIso_genericTriangle i j j

/-- The actual global morphism preserves the SAME original field structure, proved internally. -/
theorem fixedOriginalNativeMap_structure :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    fixedOriginalNativeMap i j ≫ (originalRankOneCoordinateModel i j).nativeRankOneStructure =
      i ≫ projectiveSpaceStructure k n := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let Φ := M.nativeRankOneFunctionFieldEquiv (fun _ => j)
    (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j j d)
  let _ := isDominant_fromSpecFunctionField (X := X)
  apply AlgebraicGeometry.ext_of_isDominant (X.fromSpecStalk (genericPoint X))
  rw [← Category.assoc, fixedOriginalNativeMap_genericTriangle, Category.assoc,
    pointStructureMap_wholeConstants M.nativeRankOneStructure,
    pointStructureMap_wholeConstants (i ≫ projectiveSpaceStructure k n), ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change Φ.symm (M.nativeRankOneScheme.germToFunctionField ⊤
      (M.nativeRankOneBaseConstants c)) =
    X.germToFunctionField ⊤ (((Scheme.ΓSpecIso (.of k)).inv ≫
      (i ≫ projectiveSpaceStructure k n).appTop) c)
  rw [← fixedOriginalNativeFieldEquiv_wholeConstants i j c]
  exact Φ.symm_apply_apply _

/-- The actual global original/native Scheme map is genuinely dominant. -/
theorem fixedOriginalNativeMap_isDominant :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    IsDominant (fixedOriginalNativeMap i j) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let Φ := M.nativeRankOneFunctionFieldEquiv (fun _ => j)
    (fun d => fixedOriginalCoordinateModel_pivot_ne_zero i j j d)
  let _ := isDominant_fromSpecFunctionField (X := M.nativeRankOneScheme)
  have hspec : IsIso (Spec.map (CommRingCat.ofHom Φ.symm.toRingHom)) := by
    change IsIso (Spec.map Φ.toCommRingCatIso.inv)
    infer_instance
  have hdom : IsDominant (X.fromSpecStalk (genericPoint X) ≫ fixedOriginalNativeMap i j) := by
    rw [fixedOriginalNativeMap_genericTriangle]
    infer_instance
  exact IsDominant.of_comp (X.fromSpecStalk (genericPoint X)) (fixedOriginalNativeMap i j)

/-- Actual original projectivity and the proved over-base identity make the global map proper. -/
theorem fixedOriginalNativeMap_isProper :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    IsProper (fixedOriginalNativeMap i j) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let _ := M.nativeRankOneStructure_isProper_arbitraryField
  have h : IsProper (fixedOriginalNativeMap i j ≫ M.nativeRankOneStructure) := by
    rw [fixedOriginalNativeMap_structure]
    infer_instance
  exact IsProper.of_comp _ M.nativeRankOneStructure

/-- Properness and actual generic dominance give surjectivity onto the WHOLE native scheme. -/
theorem fixedOriginalNativeMap_surjective :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    Surjective (fixedOriginalNativeMap i j) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let _ := fixedOriginalNativeMap_isProper i j
  let _ := fixedOriginalNativeMap_isDominant i j
  apply surjective_of_isDominant_of_isClosed_range
  exact (fixedOriginalNativeMap i j).isClosedMap.isClosed_range

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.pointStructureMap_wholeConstants
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.pointStructureMap_wholeConstants
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeFieldEquiv_wholeConstants
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeFieldEquiv_wholeConstants
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_genericTriangle
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_genericTriangle
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_structure
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_structure
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_isDominant
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_isDominant
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_isProper
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_isProper
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_surjective
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeMap_surjective
