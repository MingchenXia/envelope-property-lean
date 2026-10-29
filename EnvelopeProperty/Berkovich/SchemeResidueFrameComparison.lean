import EnvelopeProperty.Berkovich.SchemeFramedSectionPullback

/-! # One genuine original unit comparing entire residue frames -/
open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeResidueFrameComparison
open SchemeFramedSectionPullback

private def globalTransitionUnit {A : Type u} [CommRing A]
    {P : (Spec (.of A)).Modules} (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A))) :
    Γ(Spec (.of A), ⊤)ˣ :=
  Classical.choose (Scheme.Modules.unitIso_eq_globalUnit (e₀.symm ≪≫ e₁))

private theorem globalTransitionUnit_spec {A : Type u} [CommRing A]
    {P : (Spec (.of A)).Modules} (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A))) :
    e₀.symm ≪≫ e₁ = ModularCurves.unitAutomorphismOfTopUnit (globalTransitionUnit e₀ e₁) :=
  Classical.choose_spec (Scheme.Modules.unitIso_eq_globalUnit (e₀.symm ≪≫ e₁))

/-- The one actual original unit derived from the two entire original frames. -/
def transitionUnit {A : Type u} [CommRing A]
    {P : (Spec (.of A)).Modules} (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A))) : Aˣ :=
  Units.map (Scheme.ΓSpecIso (.of A)).hom.hom (globalTransitionUnit e₀ e₁)

/-- The derived original unit compares EVERY original whole section's coefficients. -/
theorem transitionUnit_coefficient {A : Type u} [CommRing A]
    {P : (Spec (.of A)).Modules} (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A)))
    (s : Γ(P, ⊤)) :
    (Scheme.ΓSpecIso (.of A)).hom (e₁.hom.app ⊤ s) =
      (transitionUnit e₀ e₁ : A) * (Scheme.ΓSpecIso (.of A)).hom (e₀.hom.app ⊤ s) := by
  have hi := congrArg (fun E => e₀ ≪≫ E) (globalTransitionUnit_spec e₀ e₁)
  simp only [Iso.self_symm_id_assoc] at hi
  have hh := congrArg (fun E => E.hom.app ⊤ s) hi
  change e₁.hom.app ⊤ s =
    (ModularCurves.unitAutomorphismOfTopUnit (globalTransitionUnit e₀ e₁)).hom.app ⊤
      (e₀.hom.app ⊤ s) at hh
  have hc : (show Γ(Spec (.of A), ⊤) from e₁.hom.app ⊤ s) =
      (show Γ(Spec (.of A), ⊤) from e₀.hom.app ⊤ s) *
        (globalTransitionUnit e₀ e₁ : Γ(Spec (.of A), ⊤)) := by
    refine hh.trans ?_
    change (ModularCurves.unitEndomorphismOfTopSection
      (globalTransitionUnit e₀ e₁ : Γ(Spec (.of A), ⊤))).val.app (op ⊤) (e₀.hom.app ⊤ s) = _
    erw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
    simp only [homOfLE_refl, op_id]
    erw [CategoryTheory.Functor.map_id]
    rfl
  have ha := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom hc
  exact ha.trans (((Scheme.ΓSpecIso (.of A)).hom.hom.map_mul
    (show Γ(Spec (.of A), ⊤) from e₀.hom.app ⊤ s)
    (globalTransitionUnit e₀ e₁ : Γ(Spec (.of A), ⊤))).trans (mul_comm _ _))

/-- A genuine original transition unit has strictly positive value under every actual valuation. -/
theorem transitionUnit_value_pos {A : Type u} [CommRing A]
    {P : (Spec (.of A)).Modules} (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A)))
    (ν : Valuation A ℝ≥0) : 0 < ν (transitionUnit e₀ e₁ : A) := by
  apply pos_iff_ne_zero.mpr
  intro h₀
  have hu := congrArg ν (transitionUnit e₀ e₁).val_inv
  rw [map_mul, map_one, h₀, zero_mul] at hu
  exact zero_ne_one hu

/-- The SAME derived positive factor compares all actual coefficient values. -/
theorem transitionUnit_coefficient_value {A : Type u} [CommRing A]
    {P : (Spec (.of A)).Modules} (e₀ e₁ : P ≅ Scheme.Modules.unitObj (Spec (.of A)))
    (ν : Valuation A ℝ≥0) (s : Γ(P, ⊤)) :
    ν ((Scheme.ΓSpecIso (.of A)).hom (e₁.hom.app ⊤ s)) =
      ν (transitionUnit e₀ e₁ : A) * ν ((Scheme.ΓSpecIso (.of A)).hom (e₀.hom.app ⊤ s)) := by
  rw [transitionUnit_coefficient, map_mul]

/-- The exact same unit compares native coefficients of EVERY original whole section. -/
theorem residueFrameCoefficient_change {Y : Scheme.{u}} (y : SchemeValuedPoint Y)
    (N : Y.Modules)
    (e₀ e₁ : (Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).obj N ≅
      Scheme.Modules.unitObj (Spec (.of (Y.residueField y.point)))) (σ : Γ(N, ⊤)) :
    residueFrameCoefficient y N e₁ σ =
      ((· * ·) : Y.residueField y.point → Y.residueField y.point → Y.residueField y.point)
        (transitionUnit e₀ e₁).val (residueFrameCoefficient y N e₀ σ) :=
  transitionUnit_coefficient e₀ e₁ (Scheme.Modules.affinePullbackUnitTop (Y.fromSpecResidueField y.point) N σ)

/-- Actual native coefficient values differ by one internally derived positive factor, including zero. -/
theorem residueFrameCoefficient_value_change {Y : Scheme.{u}} (y : SchemeValuedPoint Y)
    (N : Y.Modules)
    (e₀ e₁ : (Scheme.Modules.pullback (Y.fromSpecResidueField y.point)).obj N ≅
      Scheme.Modules.unitObj (Spec (.of (Y.residueField y.point)))) (σ : Γ(N, ⊤)) :
    y.residueVal (residueFrameCoefficient y N e₁ σ) =
      y.residueVal (transitionUnit e₀ e₁).val *
        y.residueVal (residueFrameCoefficient y N e₀ σ) := by
  exact transitionUnit_coefficient_value e₀ e₁ y.residueVal
    (Scheme.Modules.affinePullbackUnitTop (Y.fromSpecResidueField y.point) N σ)

end EnvelopeProperty.Berkovich.SchemeResidueFrameComparison
