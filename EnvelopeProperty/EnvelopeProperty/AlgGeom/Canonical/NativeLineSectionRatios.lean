import EnvelopeProperty.AlgGeom.Canonical.LineSectionRatios
import ModularCurves.ForMathlib.SchemeModuleBaseCechTrivialFlat
import ModularCurves.EllipticCurve.PoleSheaf

/-! # SAME intrinsic rational coefficients in EVERY original native restriction frame -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EnvelopeProperty.CanonicalGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem normalizedSemilinearOriginalFrame
    {R F M : Type*} [CommRing R] [Field F] [AddCommGroup M] [Module R M]
    (ρ : R →+* F) (T : M →ₛₗ[ρ] F) (e : M ≃ₗ[R] R)
    (d : M) (hd : T d = 1) (s : M) :
    ρ (e d) ≠ 0 ∧ T s = ρ (e s) / ρ (e d) := by
  have hrep (m : M) : m = e m • e.symm 1 := by
    apply e.injective
    simp only [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  have hformula (m : M) : T m = ρ (e m) * T (e.symm 1) := by
    calc
      T m = T (e m • e.symm 1) := congrArg T (hrep m)
      _ = ρ (e m) * T (e.symm 1) := T.map_smulₛₗ _ _
  have hprod : ρ (e d) * T (e.symm 1) = 1 := (hformula d).symm.trans hd
  have hne : ρ (e d) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact zero_ne_one hprod
  refine ⟨hne, (eq_div_iff hne).mpr ?_⟩
  rw [hformula]
  calc
    ρ (e s) * T (e.symm 1) * ρ (e d) =
        ρ (e s) * (ρ (e d) * T (e.symm 1)) := by ring
    _ = ρ (e s) := by rw [hprod, mul_one]

variable {X : Scheme.{u}}

/-- The true ENTIRE original section-module frame of an actual native open restriction frame. -/
def nativeLocalFrameCoefficient (L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) :
    Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (Scheme.Modules.sectionsIsoUnitSectionsOfRestrictIso L U e).toLinearEquiv

/-- EVERY original global section has EXACTLY the native original local-trivialization
coefficient, through the SAME entire original section-module equivalence. -/
theorem nativeLocalFrameCoefficient_global (L : X.Modules) (U : X.affineOpens)
    (e : L.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (s : Γ(L, ⊤)) :
    nativeLocalFrameCoefficient L U.1 e (L.presheaf.map U.1.leTop.op s) =
      ModularCurves.localTrivializationCoefficient L U e s := by
  change U.1.topIso.hom
      (e.hom.app ⊤ ((L.restrictAppIso U.1.ι ⊤).inv
        (L.presheaf.map (eqToHom U.1.ι_image_top).op
          (L.presheaf.map U.1.leTop.op s)))) = _
  unfold ModularCurves.localTrivializationCoefficient ModularCurves.localTrivializationTopSection
    ModularCurves.localTrivializationRestriction
  apply (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).1
  rw [Iso.hom_inv_id_apply]
  rw [← ModularCurves.affineOpenTopSection_eq_topIso_inv,
    ModularCurves.affineOpenTopSection_ambientSection]
  have hi : U.1.leTop = homOfLE (le_top : U.1 ≤ (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [hi]
  rfl

variable [IsIntegral X]

/-- The SAME original normalizing section has nonzero original native frame coefficient
in the SAME original function field; no generic-frame comparison data are supplied. -/
theorem nativeLocalFrameCoefficient_generator_ne_zero (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (d : Γ(L, ⊤)) (hd : d ≠ 0)
    (U : X.Opens) [Nonempty U]
    (e : L.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) :
    X.germToFunctionField U
      (nativeLocalFrameCoefficient L U e (L.presheaf.map U.leTop.op d)) ≠ 0 :=
  (normalizedSemilinearOriginalFrame (X.germToFunctionField U).hom
    (sectionRatio L hL d hd U) (nativeLocalFrameCoefficient L U e)
    (L.presheaf.map U.leTop.op d) (sectionRatio_generator L hL d hd U) 0).1

/-- EVERY original native restriction frame computes the SAME intrinsic rational coefficient
of EVERY original local section, with the SAME original generator denominator. -/
theorem sectionRatio_nativeFrame_formula (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (d : Γ(L, ⊤)) (hd : d ≠ 0)
    (U : X.Opens) [Nonempty U]
    (e : L.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme) (s : Γ(L, U)) :
    sectionRatio L hL d hd U s =
      X.germToFunctionField U (nativeLocalFrameCoefficient L U e s) /
        X.germToFunctionField U
          (nativeLocalFrameCoefficient L U e (L.presheaf.map U.leTop.op d)) :=
  (normalizedSemilinearOriginalFrame (X.germToFunctionField U).hom
    (sectionRatio L hL d hd U) (nativeLocalFrameCoefficient L U e)
    (L.presheaf.map U.leTop.op d) (sectionRatio_generator L hL d hd U) s).2

/-- The ENTIRE original normalized rational coefficient of EVERY original global section
is the quotient of the SAME two native original affine local-trivialization coefficients. -/
theorem sectionRatio_localTrivializationCoefficient (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (d : Γ(L, ⊤)) (hd : d ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme) (s : Γ(L, ⊤)) :
    sectionRatio L hL d hd ⊤ s =
      X.germToFunctionField U.1 (ModularCurves.localTrivializationCoefficient L U e s) /
        X.germToFunctionField U.1 (ModularCurves.localTrivializationCoefficient L U e d) := by
  have h := sectionRatio_nativeFrame_formula L hL d hd U.1 e
    (L.presheaf.map U.1.leTop.op s)
  rw [nativeLocalFrameCoefficient_global, nativeLocalFrameCoefficient_global] at h
  exact (sectionRatio_restrict L hL d hd (le_top : U.1 ≤ ⊤) s).symm.trans h

end EnvelopeProperty.CanonicalGeometry
