/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierRatioPullback
import EnvelopeProperty.Local.PLIdealNoncentralSheaves
import EnvelopeProperty.Local.PLIdealParameterSeparation
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist

/-! # Actual original projective twists on the same vertical ratio model

The genuine original projective twist, pulled back to the same blowup and
then tensored with its actual vertical ratio, is an invertible module sheaf.
Its whole noncentral restriction is the original projective twist pullback.
No normalization, metric, coherent ratio action or nefness is asserted here.
-/

open scoped Classical Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual nonnegative projective twist on the original closed subscheme. -/
def nativeTwistLineSheaf (j : Fin (M + 1)) (n : ℕ) : X.NativeScheme.Modules :=
  (Scheme.Modules.pullback X.nativeInclusion).obj
    (MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) j n)

/-- The genuine original projective twist is an actual invertible module sheaf. -/
theorem nativeTwistLineSheaf_isInvertible (j : Fin (M + 1)) (n : ℕ) :
    Scheme.Modules.IsInvertible (X.nativeTwistLineSheaf j n) :=
  (MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := k) j n).pullback _

/-- The whole original simultaneous model maps to the original actual X. -/
def simultaneousOriginalProjection (I L : X.NativeProductModel.IdealSheafData) :
    X.simultaneousIdealBlowup I L ⟶ X.NativeScheme :=
  X.simultaneousIdealBlowupProjection I L ≫ X.nativeProductModelIso.hom ≫ pullback.fst _ _

/-- The actual original twist tensor the actual original vertical ratio. -/
def simultaneousTwistedRatioModelSheaf
    (I L : X.NativeProductModel.IdealSheafData) (j : Fin (M + 1)) (n : ℕ) :
    (X.simultaneousIdealBlowup I L).Modules :=
  Scheme.Modules.tensorObj
    ((Scheme.Modules.pullback (X.simultaneousOriginalProjection I L)).obj
      (X.nativeTwistLineSheaf j n))
    (X.simultaneousRatioModelSheaf I L)

/-- Both original factors prove genuine invertibility on the SAME blowup. -/
theorem simultaneousTwistedRatioModelSheaf_isInvertible
    (I L : X.NativeProductModel.IdealSheafData) (j : Fin (M + 1)) (n : ℕ) :
    Scheme.Modules.IsInvertible (X.simultaneousTwistedRatioModelSheaf I L j n) :=
  ((X.nativeTwistLineSheaf_isInvertible j n).pullback _).tensorObj
    (X.simultaneousRatioModelSheaf_isInvertible I L)

/-- The entire noncentral restriction of this actual model sheaf is the
original twist pullback along the literal original open-to-X composite. -/
def simultaneousTwistedRatioParameterIso
    (I L : HomogeneousIdeal (ProjectiveGrading k[X] M))
    (j : Fin (M + 1)) (n A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ L.toIdeal) :
    (Scheme.Modules.pullback (X.simultaneousNoncentralOpen
      (X.nativeProductIdeal I) (X.nativeProductIdeal L)).ι).obj
        (X.simultaneousTwistedRatioModelSheaf
          (X.nativeProductIdeal I) (X.nativeProductIdeal L) j n) ≅
      (Scheme.Modules.pullback ((X.simultaneousNoncentralOpen
        (X.nativeProductIdeal I) (X.nativeProductIdeal L)).ι ≫
          X.simultaneousOriginalProjection (X.nativeProductIdeal I) (X.nativeProductIdeal L))).obj
        (X.nativeTwistLineSheaf j n) :=
  Scheme.Modules.canonicalTensorPullbackIso _ _ _ ≪≫
    Scheme.Modules.tensorObjCongr (Iso.refl _)
      (X.simultaneousRatioModuleParameterIso I L A B hA hB) ≪≫
    Scheme.Modules.tensorObjUnitIso _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app _

/-- Actual whole noncentral pullback detects morphisms into the original
twisted ratio line sheaf on that SAME simultaneous blowup. -/
theorem simultaneousTwistedRatioModel_hom_eq_of_parameter_pullback_eq
    (I L : X.NativeProductModel.IdealSheafData) (j : Fin (M + 1)) (n : ℕ)
    {P : (X.simultaneousIdealBlowup I L).Modules}
    (a b : P ⟶ X.simultaneousTwistedRatioModelSheaf I L j n)
    (h : (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).map a =
      (Scheme.Modules.pullback (X.simultaneousNoncentralOpen I L).ι).map b) :
    a = b :=
  X.simultaneousModel_hom_eq_of_parameter_pullback_eq I L
    (X.simultaneousTwistedRatioModelSheaf_isInvertible I L j n) a b h

variable {X} in
/-- Original PL data alone gives genuine invertible original twisted
ratio sheaves on the SAME finite vertical model, with the WHOLE original
noncentral twist identification and the original intrinsic ideal-log formula. -/
theorem IsPL.exists_twistedRatioLine_models {φ : X.an → ℝ} (hφ : X.IsPL φ)
    (j : Fin (M + 1)) (n : ℕ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I L : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ L.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X ^ B) ∈ L.toIdeal) ∧
      let I' := X.nativeProductIdeal I
      let L' := X.nativeProductIdeal L
      ∃ (hfin : ∀ w : X.an,
        RelativeSchemeValuedPoint.modelIdealLog I' gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog L' gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥),
      Nonempty (ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I L)) ∧
      IsIso (X.simultaneousIdealBlowupProjection I' L' ∣_
        (X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]))) ∧
      Scheme.Modules.IsInvertible (X.simultaneousTwistedRatioModelSheaf I' L' j n) ∧
      Nonempty ((Scheme.Modules.pullback (X.simultaneousNoncentralOpen I' L').ι).obj
        (X.simultaneousTwistedRatioModelSheaf I' L' j n) ≅
          (Scheme.Modules.pullback ((X.simultaneousNoncentralOpen I' L').ι ≫
            X.simultaneousOriginalProjection I' L')).obj (X.nativeTwistLineSheaf j n)) ∧
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog
          (I'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) -
        RelativeSchemeValuedPoint.modelIdealLog
          (L'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, L, hfgI, hfgL, hAI, hBL, hfin, hMod, hIso, _hratio, _htriv, hlog⟩ :=
    hφ.exists_noncentralInvertibleRatio_models
  obtain ⟨A, hA, hAmem⟩ := hAI
  obtain ⟨B, hB, hBmem⟩ := hBL
  exact ⟨r, hr, C, I, L, hfgI, hfgL, ⟨A, hA, hAmem⟩, ⟨B, hB, hBmem⟩,
    hfin, hMod, hIso, X.simultaneousTwistedRatioModelSheaf_isInvertible _ _ j n,
    ⟨X.simultaneousTwistedRatioParameterIso I L j n A B hAmem hBmem⟩, hlog⟩

end EnvelopeProperty.ProjSubvariety
