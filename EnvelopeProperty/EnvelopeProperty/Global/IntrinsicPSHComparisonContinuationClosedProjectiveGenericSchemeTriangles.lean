import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationClosedProjectiveChartGenericGerms
import EnvelopeProperty.AlgGeom.DenseOpenGenericFieldLift

/-!
# Actual generic Scheme triangles of the same fixed original/native charts

The native dense-open lift and its proved dominance are reused. Whole
geometric generic-germ compatibility is consumed to prove actual Scheme-map
triangles. The final original consumer supplies all matching internally.
Route: owned `closed-projective-generic-scheme-triangles-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open DeJongAlterations DeJongAlterations.Geometry DeJongAlterations.Geometry.Segre
  DeJongAlterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The EXISTING genuine dense-open lift's ENTIRE section map is the literal original generic germ. -/
theorem denseOpenGenericLift_sections {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (dU : Dense (U : Set X)) :
    U.topIso.inv ≫ (DenseOpenGenericFieldLift.lift U dU).appTop =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv := by
  let l := DenseOpenGenericFieldLift.lift U dU
  have h : (⊤ : (Spec X.functionField).Opens) ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := by
    intro z _
    have hη : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
        simpa using (inferInstance : Nonempty U))
    exact (Scheme.range_fromSpecStalk.le ⟨z, rfl⟩).mem_open U.isOpen hη
  have hi : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    apply X.presheaf.congr_map
    exact Subsingleton.elim _ _
  have hl : l.appLE ⊤ ⊤ le_top = l.appTop := by simp [Scheme.Hom.appLE]
  have hc := Scheme.Hom.appLE_comp_appLE l U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_top
  rw [hi, hl] at hc
  have heq {T Z : Scheme.{u}} (q q' : T ⟶ Z) (w : q = q')
      (A : Z.Opens) (B : T.Opens) (h₁ : B ≤ q ⁻¹ᵁ A) (h₂ : B ≤ q' ⁻¹ᵁ A) :
      q.appLE A B h₁ = q'.appLE A B h₂ := by
    cases w
    rfl
  exact (hc.trans (heq _ _ (DenseOpenGenericFieldLift.lift_inclusion U dU) _ _ _ _)).trans
    (originalGenericPoint_appLE (X := X) U h)

/-- TRUE geometric germ compatibility yields equality of the ENTIRE actual generic Scheme maps. -/
theorem denseOpenGenericLift_compare {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (U : X.Opens) [Nonempty U] (V : Y.Opens) [Nonempty V]
    (dU : Dense (U : Set X)) (dV : Dense (V : Set Y)) (hV : IsAffineOpen V)
    (e : U.toScheme ≅ V.toScheme) (Φ : X.functionField ≃+* Y.functionField)
    (hcompat : ∀ a : Γ(X, U),
      Y.germToFunctionField V ((U.topIso.inv ≫ e.inv.appTop ≫ V.topIso.hom) a) =
        Φ (X.germToFunctionField U a)) :
    DenseOpenGenericFieldLift.lift U dU ≫ e.hom ≫ V.ι =
      Spec.map (CommRingCat.ofHom Φ.symm.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y) := by
  let gx := DenseOpenGenericFieldLift.lift U dU
  let gy := DenseOpenGenericFieldLift.lift V dV
  let φ : Y.functionField ⟶ X.functionField := CommRingCat.ofHom Φ.symm.toRingHom
  let P : Γ(X, U) ≅ Γ(Y, V) :=
    U.topIso.symm ≪≫ Scheme.Γ.mapIso e.symm.op ≪≫ V.topIso
  have hreverse (b : Γ(Y, V)) :
      X.germToFunctionField U (P.inv b) = Φ.symm (Y.germToFunctionField V b) := by
    apply Φ.injective
    rw [RingEquiv.apply_symm_apply]
    have hh := hcompat (P.inv b)
    change Y.germToFunctionField V (P.hom (P.inv b)) =
      Φ (X.germToFunctionField U (P.inv b)) at hh
    rw [P.inv_hom_id_apply] at hh
    exact hh.symm
  have hQ : P.inv ≫ X.germToFunctionField U = Y.germToFunctionField V ≫ φ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact hreverse b
  have hx := denseOpenGenericLift_sections (X := X) U dU
  have hy := denseOpenGenericLift_sections (X := Y) V dV
  have hx' : gx.appTop = U.topIso.hom ≫ X.germToFunctionField U ≫
      (Scheme.ΓSpecIso X.functionField).inv := by
    apply (cancel_epi U.topIso.inv).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hx
  have hn : (Scheme.ΓSpecIso Y.functionField).inv ≫ (Spec.map φ).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = φ := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hR : V.topIso.inv ≫ gy.appTop ≫ (Spec.map φ).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = Y.germToFunctionField V ≫ φ := by
    calc
      _ = Y.germToFunctionField V ≫ ((Scheme.ΓSpecIso Y.functionField).inv ≫
          (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso X.functionField).hom) := by
        simpa only [Category.assoc] using congrArg
          (fun t : Γ(Y, V) ⟶ Γ(Spec Y.functionField, ⊤) =>
            t ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso X.functionField).hom) hy
      _ = _ := congrArg (fun t => Y.germToFunctionField V ≫ t) hn
  have hL : V.topIso.inv ≫ (gx ≫ e.hom).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = P.inv ≫ X.germToFunctionField U := by
    change V.topIso.inv ≫ (gx ≫ e.hom).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom =
        (V.topIso.inv ≫ e.hom.appTop ≫ U.topIso.hom) ≫ X.germToFunctionField U
    rw [Scheme.Hom.comp_appTop, hx']
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have happ : (gx ≫ e.hom).appTop = (Spec.map φ ≫ gy).appTop := by
    apply (cancel_epi V.topIso.inv).mp
    apply (cancel_mono (Scheme.ΓSpecIso X.functionField).hom).mp
    calc
      _ = P.inv ≫ X.germToFunctionField U := by simpa only [Category.assoc] using hL
      _ = Y.germToFunctionField V ≫ φ := hQ
      _ = _ := by simpa only [Scheme.Hom.comp_appTop, Category.assoc] using hR.symm
  have hm : gx ≫ e.hom = Spec.map φ ≫ gy := by
    let : IsAffine V.toScheme := hV
    apply (cancel_mono V.toScheme.toSpecΓ).mp
    rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, happ]
  calc
    gx ≫ e.hom ≫ V.ι = (Spec.map φ ≫ gy) ≫ V.ι := by rw [← Category.assoc, hm]
    _ = Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y) := by
      rw [Category.assoc, DenseOpenGenericFieldLift.lift_inclusion]

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]
variable (s : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange)]

/-- EVERY actual original/native chart scheme map has the SAME fixed-reference WHOLE generic Scheme triangle. -/
theorem fixedOriginalNativeCoordinateChartIso_genericTriangle :
    letI := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
    let M := originalRankOneCoordinateModel i j
    let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
    let U := M.nativeRankOneCoordinateOpen s
    let dV := V.isOpen.dense (by simpa using (inferInstance : Nonempty V))
    DenseOpenGenericFieldLift.lift V dV ≫ (fixedOriginalNativeCoordinateChartIso i j s).hom ≫ U.ι =
      Spec.map (CommRingCat.ofHom (M.nativeRankOneFunctionFieldEquiv (fun _ => j)
        (fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j j c)).symm.toRingHom) ≫
        M.nativeRankOneScheme.fromSpecStalk (genericPoint M.nativeRankOneScheme) := by
  let _ := (i ≫ projectiveSpaceStructure k n).stalkAlgebra (genericPoint X)
  let M := originalRankOneCoordinateModel i j
  let V := i ⁻¹ᵁ (coordinateChartInclusion (R := k) s).opensRange
  let U := M.nativeRankOneCoordinateOpen s
  let b : M.ChartIndex := fun _ => s
  let bj : M.ChartIndex := fun _ => j
  let hb := fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j s c
  let hj := fun c => fixedOriginalCoordinateModel_pivot_ne_zero i j j c
  let : Nonempty U := M.nativeRankOneCoordinateOpen_nonempty b hb
  let dV := V.isOpen.dense (by simpa using (inferInstance : Nonempty V))
  let dU := U.isOpen.dense (by simpa using (inferInstance : Nonempty U))
  let e := fixedOriginalNativeCoordinateChartIso i j s
  let Φ := M.nativeRankOneFunctionFieldEquiv bj hj
  apply denseOpenGenericLift_compare (X := X) (Y := M.nativeRankOneScheme)
    V U dV dU (M.nativeRankOneCoordinateOpen_isAffine s) e Φ
  intro a
  simpa only [MultiModel.nativeRankOneGenericGerm] using
    fixedOriginalNativeCoordinateChartIso_genericGerm i j s a

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.denseOpenGenericLift_sections
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.denseOpenGenericLift_sections
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.denseOpenGenericLift_compare
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.denseOpenGenericLift_compare
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_genericTriangle
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.fixedOriginalNativeCoordinateChartIso_genericTriangle
