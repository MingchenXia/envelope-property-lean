import EnvelopeProperty.AlgGeom.SpecifiedFieldGenericMap
import EnvelopeProperty.Berkovich.SchemeRelativeValuedPoints

/-! # Actual specified-field native generic points retain ALL original section values -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SpecifiedFieldGenericValuedPoints
variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

/-- The native whole original scheme point from the SAME actual specified-field spectrum point. -/
def point (v : Spectrum L) : SchemeValuedPoint X :=
  SchemeValuedPoint.map (SpecifiedFieldSchemeNormalization.genericMap X L)
    (SchemeValuedPoint.spectrumHomeomorph.symm v)

/-- The actual whole original point is the original generic point. -/
theorem point_underlying (v : Spectrum L) : (point X L v).point = genericPoint X :=
  SpecifiedFieldSchemeNormalization.genericMap_apply X L _

/-- The same original valued generic point lies in EVERY original nonempty open. -/
theorem point_mem (v : Spectrum L) (U : X.Opens) [Nonempty U] :
    (point X L v).point ∈ U := by
  rw [point_underlying]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

/-- The construction is continuous for the native actual whole scheme section topology. -/
theorem continuous_point : Continuous (point X L) :=
  (SchemeValuedPoint.continuous_map (SpecifiedFieldSchemeNormalization.genericMap X L)).comp
    SchemeValuedPoint.spectrumHomeomorph.symm.continuous

private theorem affine_eval_whole {F : Type u} [Field F] (v : Spectrum F)
    (U : (Spec (.of F)).Opens) (hU : U = ⊤)
    (hvU : (SchemeValuedPoint.spectrumHomeomorph.symm v).point ∈ U) (s : Γ(Spec (.of F), U)) :
    SchemeValuedPoint.eval (SchemeValuedPoint.spectrumHomeomorph.symm v) U hvU s =
      v.val ((Scheme.ΓSpecIso (.of F)).hom
        ((Spec (.of F)).presheaf.map (homOfLE hU.ge).op s)) := by
  let y := SchemeValuedPoint.spectrumHomeomorph.symm v
  have hr := SchemeValuedPoint.eval_restrict y U ⊤ hU.ge trivial s
  have hv := SchemeValuedPoint.spectrumHomeomorph_val_apply y
    ((Scheme.ΓSpecIso (.of F)).hom ((Spec (.of F)).presheaf.map (homOfLE hU.ge).op s))
  rw [Homeomorph.apply_symm_apply] at hv
  have hi : (Scheme.ΓSpecIso (.of F)).inv
      ((Scheme.ΓSpecIso (.of F)).hom ((Spec (.of F)).presheaf.map (homOfLE hU.ge).op s)) =
      (Spec (.of F)).presheaf.map (homOfLE hU.ge).op s := by
    exact (Scheme.ΓSpecIso (.of F)).commRingCatIsoToRingEquiv.symm_apply_apply _
  rw [hi] at hv
  exact hr.symm.trans hv.symm

/-- EVERY actual original section value equals the SAME specified image of its original generic germ. -/
theorem point_eval (v : Spectrum L) (U : X.Opens) [Nonempty U] (s : Γ(X, U)) :
    SchemeValuedPoint.eval (point X L v) U (point_mem X L v U) s =
      v.val (algebraMap X.functionField L (X.germToFunctionField U s)) := by
  let g := SpecifiedFieldSchemeNormalization.genericMap X L
  let y := SchemeValuedPoint.spectrumHomeomorph.symm v
  have hh : g y.point ∈ U := by
    rw [SpecifiedFieldSchemeNormalization.genericMap_apply]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have he := SchemeValuedPoint.eval_map g y U hh s
  have ha := affine_eval_whole v (g ⁻¹ᵁ U)
    (SpecifiedFieldSchemeNormalization.genericMap_preimage X L U) hh (g.app U s)
  have hc := congrArg (fun q : Γ(X, U) ⟶ .of L => q s)
    (SpecifiedFieldSchemeNormalization.genericSectionIso_coefficients X L U)
  exact he.trans (ha.trans (congrArg v.val hc))

end EnvelopeProperty.Berkovich.SpecifiedFieldGenericValuedPoints
