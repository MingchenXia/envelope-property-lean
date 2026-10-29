import EnvelopeProperty.Berkovich.SchemeIntegralNormalization

/-! # The ACTUAL specified extension-field generic morphism of the original integral scheme -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SpecifiedFieldSchemeNormalization
variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

private def extensionMap : X.functionField ⟶ CommRingCat.of L :=
  CommRingCat.ofHom (algebraMap X.functionField L)

/-- The SAME original generic-stalk morphism with the ACTUAL specified extension field. -/
def genericMap : Spec (.of L) ⟶ X :=
  Spec.map (extensionMap X L) ≫
    IntegralSchemeNormalization.genericMap X

/-- EVERY point of the ACTUAL specified original field maps to the SAME original generic point. -/
theorem genericMap_apply (z : Spec (.of L)) : genericMap X L z = genericPoint X :=
  IntegralSchemeNormalization.genericMap_apply X _

/-- Actual single-point inverse images derive quasi-compactness, without a supplied scheme hypothesis. -/
theorem genericMap_quasiCompact : QuasiCompact (genericMap X L) where
  isCompact_preimage U _ _ := (Set.toFinite ((genericMap X L) ⁻¹' U)).isCompact

/-- Actual affine field map and original generic-map separation derive quasi-separatedness. -/
theorem genericMap_quasiSeparated : QuasiSeparated (genericMap X L) := by
  let : QuasiSeparated (IntegralSchemeNormalization.genericMap X) :=
    IntegralSchemeNormalization.genericMap_quasiSeparated X
  unfold genericMap
  infer_instance

private local instance : QuasiCompact (genericMap X L) := genericMap_quasiCompact X L
private local instance : QuasiSeparated (genericMap X L) := genericMap_quasiSeparated X L

/-- Every original nonempty open has the entire SAME specified field spectrum as its actual preimage. -/
theorem genericMap_preimage (U : X.Opens) [Nonempty U] : (genericMap X L) ⁻¹ᵁ U = ⊤ := by
  ext z
  change genericMap X L z ∈ U ↔ True
  rw [genericMap_apply, iff_true]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

private def preimageTopSectionIso {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (U : Z.Opens) (h : f ⁻¹ᵁ U = ⊤) : Γ(Y, f ⁻¹ᵁ U) ≅ Γ(Y, ⊤) where
  hom := Y.presheaf.map (homOfLE h.ge).op
  inv := Y.presheaf.map (homOfLE le_top).op
  hom_inv_id := by
    rw [← Functor.map_comp]
    exact Y.presheaf.map_id _
  inv_hom_id := by
    rw [← Functor.map_comp]
    exact Y.presheaf.map_id _

private theorem fromSpecStalk_appLE {Y : Scheme.{u}} (x : Y) (U : Y.Opens)
    (hx : x ∈ U) (h : (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ≤
      (Y.fromSpecStalk x) ⁻¹ᵁ U) :
    (Y.fromSpecStalk x).appLE U ⊤ h =
      Y.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).inv := by
  dsimp only [Scheme.Hom.appLE]
  rw [Scheme.fromSpecStalk_app hx]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp]
  have he : (homOfLE (le_top : (Y.fromSpecStalk x) ⁻¹ᵁ U ≤ ⊤)).op ≫
      (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [he, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem specFieldSection_naturality {R S : CommRingCat.{u}} (q : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map q).appTop ≫ (Scheme.ΓSpecIso S).hom = q := by
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The entire ACTUAL generic-preimage section ring is the SAME specified extension field. -/
def genericSectionIso (U : X.Opens) [Nonempty U] :
    Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) ≅ CommRingCat.of L :=
  preimageTopSectionIso (genericMap X L) U (genericMap_preimage X L U) ≪≫
    Scheme.ΓSpecIso (.of L)

/-- The WHOLE actual coefficient square is exactly the original generic germ
followed by the SAME  specified field embedding. -/
theorem genericSectionIso_coefficients (U : X.Opens) [Nonempty U] :
    (genericMap X L).app U ≫ (genericSectionIso X L U).hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
  let a := Spec.map (extensionMap X L)
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have htop : (⊤ : (Spec X.functionField).Opens) ≤
      (IntegralSchemeNormalization.genericMap X) ⁻¹ᵁ U :=
    (IntegralSchemeNormalization.genericMap_preimage X U).ge
  have h2 : (⊤ : (Spec (.of L)).Opens) ≤ a ⁻¹ᵁ ⊤ := by intro z _; trivial
  have hg : (IntegralSchemeNormalization.genericMap X).appLE U ⊤ htop =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv :=
    fromSpecStalk_appLE (genericPoint X) U hx htop
  change (genericMap X L).appLE U ⊤ _ ≫ (Scheme.ΓSpecIso (.of L)).hom = _
  have hc := Scheme.Hom.appLE_comp_appLE a (IntegralSchemeNormalization.genericMap X)
    U ⊤ ⊤ htop h2
  have hc' := congrArg (fun q : Γ(X, U) ⟶ Γ(Spec (.of L), ⊤) =>
    q ≫ (Scheme.ΓSpecIso (.of L)).hom) hc
  refine hc'.symm.trans ?_
  rw [hg]
  change ((X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv) ≫
    a.appTop) ≫ (Scheme.ΓSpecIso (.of L)).hom = X.germToFunctionField U ≫ extensionMap X L
  have hn := specFieldSection_naturality (R := X.functionField) (S := CommRingCat.of L)
    (extensionMap X L)
  have hn' := congrArg (fun q : X.functionField ⟶ CommRingCat.of L =>
    X.germToFunctionField U ≫ q) hn
  simpa only [Category.assoc, a] using hn'

end EnvelopeProperty.SpecifiedFieldSchemeNormalization
