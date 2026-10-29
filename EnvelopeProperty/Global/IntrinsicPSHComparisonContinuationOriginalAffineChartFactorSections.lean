import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationOriginalProjectiveGenericFactors

/-!
# Whole native section maps from actual affine chart triangles

The abstract section pullback identity is proved once for actual affine
chart triangles. Its original projective consumer uses the genuinely
constructed original generic factor and triangle, without a matching premise.
Route: owned `original-affine-chart-factor-sections-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Alterations Alterations.Geometry Alterations.Geometry.Segre
  Alterations.Geometry.ProjectiveIdeal
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGenericCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual affine-chart factorization gives the ENTIRE native section-map triangle. -/
theorem actualAffineChartFactor_sections {A B : CommRingCat.{u}}
    {Y : Scheme.{u}} (f : Spec A ⟶ Y) [IsOpenImmersion f]
    (l : Spec B ⟶ Spec A) (q : Spec B ⟶ Y) (hfac : l ≫ f = q)
    (hQ : (⊤ : (Spec B).Opens) ≤ q ⁻¹ᵁ f.opensRange) :
    (Scheme.ΓSpecIso A).inv ≫ l.appTop =
      CommRingCat.ofHom (OpenImmersionGenericCoordinates.sectionRingEquiv f).toRingHom ≫
        q.appLE f.opensRange ⊤ hQ := by
  let h : (⊤ : (Spec A).Opens) ≤ f ⁻¹ᵁ f.opensRange := by
    intro x _; exact ⟨x, rfl⟩
  have heq {T Z : Scheme.{u}} (q q' : T ⟶ Z) (w : q = q')
      (U : Z.Opens) (V : T.Opens) (h₁ : V ≤ q ⁻¹ᵁ U) (h₂ : V ≤ q' ⁻¹ᵁ U) :
      q.appLE U V h₁ = q'.appLE U V h₂ := by
    cases w
    rfl
  have hc := Scheme.Hom.appLE_comp_appLE l f f.opensRange ⊤ ⊤ h le_top
  have ht : l.appLE ⊤ ⊤ le_top = l.appTop := by simp [Scheme.Hom.appLE]
  rw [ht] at hc
  have hcomp : f.appLE f.opensRange ⊤ h ≫ l.appTop = q.appLE f.opensRange ⊤ hQ :=
    hc.trans (heq _ _ hfac _ _ _ _)
  let e := CommRingCat.ofHom (OpenImmersionGenericCoordinates.sectionRingEquiv f).toRingHom
  have hchart : e ≫ f.appLE f.opensRange ⊤ h = (Scheme.ΓSpecIso A).inv := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact OpenImmersionGenericCoordinates.appLE_sectionRingEquiv f a
  calc
    (Scheme.ΓSpecIso A).inv ≫ l.appTop =
        (e ≫ f.appLE f.opensRange ⊤ h) ≫ l.appTop := congrArg (fun t => t ≫ l.appTop) hchart.symm
    _ = e ≫ q.appLE f.opensRange ⊤ hQ := by rw [Category.assoc, hcomp]

/-- The original generic-point composite has its literal WHOLE pullback for EVERY original target and open. -/
theorem originalGenericPoint_comp_appLE {X Y : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ Y) (U : Y.Opens) [Nonempty (i ⁻¹ᵁ U)]
    (h : (⊤ : (Spec X.functionField).Opens) ≤
      (X.fromSpecStalk (genericPoint X) ≫ i) ⁻¹ᵁ U) :
    (X.fromSpecStalk (genericPoint X) ≫ i).appLE U ⊤ h =
      i.app U ≫ X.germToFunctionField (i ⁻¹ᵁ U) ≫
        (Scheme.ΓSpecIso X.functionField).inv := by
  have hcomp := Scheme.Hom.comp_appLE (X.fromSpecStalk (genericPoint X)) i U ⊤ h
  have h' : (⊤ : (Spec X.functionField).Opens) ≤
      X.fromSpecStalk (genericPoint X) ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    intro x hx
    have hx' := h hx
    change (X.fromSpecStalk (genericPoint X) ≫ i) x ∈ U at hx'
    change i (X.fromSpecStalk (genericPoint X) x) ∈ U
    rw [Scheme.Hom.comp_apply] at hx'
    exact hx'
  have hgerm := originalGenericPoint_appLE (X := X) (i ⁻¹ᵁ U) h' 
  exact hcomp.trans (congrArg
    (fun t : Γ(X, i ⁻¹ᵁ U) ⟶ Γ(Spec X.functionField, ⊤) => i.app U ≫ t) hgerm)

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k] {n : ℕ}
variable (i : X ⟶ projectiveSpace k n) (j : Fin (n + 1))
  [Nonempty (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange)]

/-- The ACTUAL internally produced original factor retains its literal WHOLE section/germ triangle. -/
theorem originalProjectiveGenericChartFactor_sectionsTriangle :
    (Scheme.ΓSpecIso (.of (CoordinateRing k j))).inv ≫
      (originalProjectiveGenericChartFactor i j).appTop =
    CommRingCat.ofHom (OpenImmersionGenericCoordinates.sectionRingEquiv
      (coordinateChartInclusion (R := k) j)).toRingHom ≫
      i.app (coordinateChartInclusion (R := k) j).opensRange ≫
      X.germToFunctionField
        (i ⁻¹ᵁ (coordinateChartInclusion (R := k) j).opensRange) ≫
      (Scheme.ΓSpecIso X.functionField).inv := by
  let f := coordinateChartInclusion (R := k) j
  have hG : (⊤ : (Spec X.functionField).Opens) ≤
      (X.fromSpecStalk (genericPoint X) ≫ i) ⁻¹ᵁ f.opensRange := by
    intro x _
    have hη : genericPoint X ∈ i ⁻¹ᵁ f.opensRange :=
      ((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ f.opensRange).isOpen).mpr (by
        simpa using (inferInstance : Nonempty (i ⁻¹ᵁ f.opensRange)))
    have hs : X.fromSpecStalk (genericPoint X) x ⤳ genericPoint X :=
      Scheme.range_fromSpecStalk.le ⟨x, rfl⟩
    exact hs.mem_open (i ⁻¹ᵁ f.opensRange).isOpen hη
  have hh := actualAffineChartFactor_sections (A := .of (CoordinateRing k j))
    (B := X.functionField) f (originalProjectiveGenericChartFactor i j)
    (X.fromSpecStalk (genericPoint X) ≫ i) (originalProjectiveGenericChartFactor_fac i j) hG
  have hg := originalGenericPoint_comp_appLE i f.opensRange hG
  exact hh.trans (congrArg
    (fun t : Γ(projectiveSpace k n, f.opensRange) ⟶ Γ(Spec X.functionField, ⊤) =>
      CommRingCat.ofHom (OpenImmersionGenericCoordinates.sectionRingEquiv f).toRingHom ≫ t) hg)

end EnvelopeProperty.ClosedProjectiveGenericCoefficients

#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.actualAffineChartFactor_sections
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.actualAffineChartFactor_sections
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalGenericPoint_comp_appLE
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalGenericPoint_comp_appLE
#check @EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor_sectionsTriangle
#print axioms EnvelopeProperty.ClosedProjectiveGenericCoefficients.originalProjectiveGenericChartFactor_sectionsTriangle
