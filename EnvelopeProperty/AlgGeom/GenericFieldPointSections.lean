import EnvelopeProperty.AlgGeom.GenericOpenValuativeLift
import EnvelopeProperty.AlgGeom.Canonical.GenericLineSections

/-! # The SAME original generic field point retains EVERY original rational coefficient -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EnvelopeProperty.GenericOpenValuativeLift
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R F : Type u} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of R)) (W : (Spec (.of R)).Opens) [Nonempty W] [IsIso (p ∣_ W)]

/-- EVERY actual point of the SAME original prescribed generic field spectrum maps
to the SAME original scheme generic point. -/
theorem genericFieldPoint_apply (x : Spec (.of F)) :
    genericFieldPoint (F := F) p W x = genericPoint Y := by
  change Y.fromSpecStalk (genericPoint Y)
    (Spec.map (CommRingCat.ofHom
      (GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W).toRingHom) x) = _
  have hx : Spec.map (CommRingCat.ofHom
      (GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W).toRingHom) x =
      IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
  rw [hx, Scheme.fromSpecStalk_closedPoint]

/-- EVERY nonempty original open pulls back to the WHOLE SAME generic field spectrum. -/
theorem genericFieldPoint_preimage (U : Y.Opens) [Nonempty U] :
    genericFieldPoint (F := F) p W ⁻¹ᵁ U = ⊤ := by
  ext x
  change genericFieldPoint (F := F) p W x ∈ U ↔ True
  rw [genericFieldPoint_apply]
  exact iff_true_intro (CanonicalGeometry.genericPoint_mem_nonempty_open U)

/-- EVERY original section on EVERY nonempty original open has EXACTLY its SAME
original rational coefficient under the SAME genuine prescribed-field point. -/
theorem genericFieldPoint_appLE_top (U : Y.Opens) [Nonempty U] :
    let htop : (⊤ : (Spec (.of F)).Opens) ≤ genericFieldPoint (F := F) p W ⁻¹ᵁ U := by
      rw [genericFieldPoint_preimage p W U]
    (genericFieldPoint (F := F) p W).appLE U ⊤ htop ≫ (Scheme.ΓSpecIso (.of F)).hom =
      Y.germToFunctionField U ≫ CommRingCat.ofHom
        (GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W).toRingHom := by
  let q := Y.fromSpecStalk (genericPoint Y)
  let j := Spec.map (CommRingCat.ofHom
    (GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W).toRingHom)
  have hq : (⊤ : (Spec Y.functionField).Opens) ≤ q ⁻¹ᵁ U := by
    intro x _
    change Y.fromSpecStalk (genericPoint Y) x ∈ U
    change PrimeSpectrum Y.functionField at x
    have hx : x = IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
    rw [hx, Scheme.fromSpecStalk_closedPoint]
    exact CanonicalGeometry.genericPoint_mem_nonempty_open U
  have hqapp : q.appLE U ⊤ hq = Y.germToFunctionField U ≫ (Scheme.ΓSpecIso Y.functionField).inv := by
    dsimp only [q]
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app
      (CanonicalGeometry.genericPoint_mem_nonempty_open U)]
    simp only [Category.assoc]
    rw [← Functor.map_comp]
    have hmaps : (homOfLE (le_top : q ⁻¹ᵁ U ≤ ⊤)).op ≫ (homOfLE hq).op =
        𝟙 (op (⊤ : (Spec Y.functionField).Opens)) := Subsingleton.elim _ _
    rw [hmaps, CategoryTheory.Functor.map_id, Category.comp_id]
  have hj : j.appLE ⊤ ⊤ (by simp) = j.appTop := by
    rw [Scheme.Hom.appLE]
    change j.appTop ≫ (Spec (.of F)).presheaf.map (𝟙 (op (⊤ : (Spec (.of F)).Opens))) = j.appTop
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hc := Scheme.Hom.appLE_comp_appLE j q U ⊤ ⊤ hq (by simp)
  rw [hj, hqapp] at hc
  change (j ≫ q).appLE U ⊤ _ ≫ (Scheme.ΓSpecIso (.of F)).hom = _
  rw [← hc]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

end EnvelopeProperty.GenericOpenValuativeLift
