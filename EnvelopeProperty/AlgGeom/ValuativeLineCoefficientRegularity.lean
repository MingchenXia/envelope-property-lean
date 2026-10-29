import EnvelopeProperty.AlgGeom.ValuativeLineCoefficients
import EnvelopeProperty.AlgGeom.GenericFieldPointSections

/-! # EVERY SAME original rational line coefficient is regular on the original unit lift -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EnvelopeProperty.ValuativeLineCoefficientRegularity
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalAffineOpenTopApp {X : Scheme.{u}} (U : X.affineOpens) (a : Γ(X, U.1)) :
    ModularCurves.affineOpenTopSection U a =
      (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom a := by
  rw [ModularCurves.affineOpenTopSection, Scheme.Opens.ι_appIso, Scheme.Opens.ι_appLE]
  change (X.presheaf.map (eqToHom U.1.ι_image_top).op).hom a = _
  apply ConcreteCategory.congr_hom
  apply X.presheaf.congr_map
  exact Subsingleton.elim _ _

private theorem originalAppLETop {X Y : Scheme.{u}} (g : X ⟶ Y) :
    g.appLE ⊤ ⊤ (by simp) = g.appTop := by
  rw [Scheme.Hom.appLE]
  change g.appTop ≫ X.presheaf.map (𝟙 (op ⊤)) = g.appTop
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem originalAppLECongr {Y Z : Scheme.{u}} (f g : Y ⟶ Z) (h : f = g)
    (U : Z.Opens) (V : Y.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

variable {R F V : Type u} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    [CommRing V] [IsLocalRing V] [Algebra V F]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) (W : (Spec (.of R)).Opens) [Nonempty W] [IsIso (p ∣_ W)]

omit [IsLocalRing V] in
private theorem originalLiftCoefficientSquare
    (l : Spec (.of V) ⟶ X)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap V F)) ≫ l =
      GenericOpenValuativeLift.genericFieldPoint (F := F) p W)
    (U : X.affineOpens) [Nonempty U.1] (t : Spec (.of V) ⟶ U.1.toScheme)
    (ht : t ≫ U.1.ι = l) (a : Γ(X, U.1)) :
    algebraMap V F ((Scheme.ΓSpecIso (.of V)).hom.hom
      (t.appTop.hom (ModularCurves.affineOpenTopSection U a))) =
        GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W
          (X.germToFunctionField U.1 a) := by
  let m := Spec.map (CommRingCat.ofHom (algebraMap V F))
  let α := U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge
  have hpre : (⊤ : (Spec (.of V)).Opens) ≤ l ⁻¹ᵁ U.1 := by
    intro x _
    change l x ∈ U.1
    rw [← ht, Scheme.Hom.comp_apply]
    exact (t x).property
  have h1 : α ≫ t.appTop = l.appLE U.1 ⊤ hpre := by
    have h := Scheme.Hom.appLE_comp_appLE t U.1.ι U.1 ⊤ ⊤ U.1.ι_preimage_self.ge (by simp)
    rw [originalAppLETop] at h
    exact h.trans (originalAppLECongr _ _ ht U.1 ⊤ _ hpre)
  have h2 : l.appLE U.1 ⊤ hpre ≫ m.appTop =
      (GenericOpenValuativeLift.genericFieldPoint (F := F) p W).appLE U.1 ⊤
        (by rw [GenericOpenValuativeLift.genericFieldPoint_preimage p W U.1]) := by
    have h := Scheme.Hom.appLE_comp_appLE m l U.1 ⊤ ⊤ hpre (by simp)
    rw [originalAppLETop] at h
    exact h.trans (originalAppLECongr _ _ hl U.1 ⊤ _ _)
  have hring : α ≫ t.appTop ≫ (Scheme.ΓSpecIso (.of V)).hom ≫
      CommRingCat.ofHom (algebraMap V F) = X.germToFunctionField U.1 ≫
        CommRingCat.ofHom (GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W).toRingHom := by
    calc
      _ = α ≫ t.appTop ≫ m.appTop ≫ (Scheme.ΓSpecIso (.of F)).hom := by
        rw [Scheme.ΓSpecIso_naturality]
      _ = (l.appLE U.1 ⊤ hpre ≫ m.appTop) ≫ (Scheme.ΓSpecIso (.of F)).hom := by
        rw [← Category.assoc α t.appTop, h1]
        rw [Category.assoc]
      _ = _ := by
        rw [h2]
        exact GenericOpenValuativeLift.genericFieldPoint_appLE_top p W U.1
  have h := congrArg (fun q : Γ(X, U.1) ⟶ CommRingCat.of F => q.hom a) hring
  change algebraMap V F ((Scheme.ΓSpecIso (.of V)).hom.hom (t.appTop.hom (α.hom a))) = _ at h
  rw [← originalAffineOpenTopApp] at h
  exact h

/-- EVERY original global line section's SAME normalized prescribed rational coefficient
belongs to the SAME original local ring along its genuine generic-compatible unit lift.
The original affine frame, whole coefficient square and denominator unit are DERIVED. -/
theorem fractionCoefficient_mem_range_of_unit_lift
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (δ : Scheme.Modules.unitObj X ⟶ L)
    (hd : δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1) ≠ 0)
    (l : Spec (.of V) ⟶ X)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap V F)) ≫ l =
      GenericOpenValuativeLift.genericFieldPoint (F := F) p W)
    [IsIso ((Scheme.Modules.pullbackUnitIso l).inv ≫ (Scheme.Modules.pullback l).map δ)]
    (s : Γ(L, ⊤)) :
    GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W
      (CanonicalGeometry.sectionRatio L hL
        (δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) hd ⊤ s) ∈
      Set.range (algebraMap V F) := by
  obtain ⟨U, e, t, hx, ht, hunit⟩ :=
    ValuativeLineCoefficients.exists_affineFrame_unit_coefficient L hL δ l
  let : Nonempty U.1 := ⟨⟨l (IsLocalRing.closedPoint V), hx⟩⟩
  let d := δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1)
  let cS := ModularCurves.localTrivializationCoefficient L U e s
  let cD := ModularCurves.localTrivializationCoefficient L U e d
  let aV := (Scheme.ΓSpecIso (.of V)).hom.hom (t.appTop.hom (ModularCurves.affineOpenTopSection U cS))
  let bV := (Scheme.ΓSpecIso (.of V)).hom.hom (t.appTop.hom (ModularCurves.affineOpenTopSection U cD))
  have ha := originalLiftCoefficientSquare p W l hl U t ht cS
  have hb := originalLiftCoefficientSquare p W l hl U t ht cD
  have hr : GenericOpenFunctionField.specFractionFieldEquiv (F := F) p W
      (CanonicalGeometry.sectionRatio L hL d hd ⊤ s) = algebraMap V F aV / algebraMap V F bV := by
    rw [CanonicalGeometry.sectionRatio_localTrivializationCoefficient L hL d hd U e s, map_div₀]
    exact congrArg₂ (fun a b : F => a / b) ha.symm hb.symm
  have hu : IsUnit bV := hunit
  have hn : algebraMap V F bV ≠ 0 := (hu.map (algebraMap V F)).ne_zero
  obtain ⟨u, huval⟩ := hu
  have hprod : bV * (↑u⁻¹ : V) = 1 := by rw [← huval]; simp
  refine ⟨aV * (↑u⁻¹ : V), ?_⟩
  rw [hr]
  apply (eq_div_iff hn).mpr
  rw [map_mul]
  calc
    algebraMap V F aV * algebraMap V F (↑u⁻¹ : V) * algebraMap V F bV =
        algebraMap V F aV * algebraMap V F (bV * (↑u⁻¹ : V)) := by rw [map_mul]; ring
    _ = algebraMap V F aV := by rw [hprod, map_one, mul_one]

end EnvelopeProperty.ValuativeLineCoefficientRegularity
