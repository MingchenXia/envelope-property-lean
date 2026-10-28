import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalGaussCurveLineOrders
import EnvelopeProperty.Local.PLGaussCentralLineNormalization

/-! # Actual two-frame coefficients compute every true-center model norm -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical NNReal
universe u
namespace EnvelopeProperty.NumericalGaussCurveLineNorms
open Scheme.Modules SchemeLineSectionEvaluation
open Berkovich Berkovich.RelativeSchemeValuedPoint

private def genericScalar (Y : Scheme.{u}) [IsIntegral Y] (f : Y.functionField) :
    Γ(Spec (Y.residueField (genericPoint Y)), ⊤) :=
  (Scheme.ΓSpecIso (Y.residueField (genericPoint Y))).inv.hom (Y.residue (genericPoint Y) f)

private def pointScalar {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y) (hp : p = genericPoint Y) (f : Y.functionField) :
    Γ(Spec (CommRingCat.of (Y.residueField p)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField p))).inv.hom
    (SchemeValuedPoint.genericResidueEquiv Y p hp f)

private theorem genericSectionAt_scalar {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (p : Y) (hp : p = genericPoint Y) (f : Y.functionField)
    (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)) :
    GaussCentralLineNormalization.genericSectionAt L p hp (genericScalar Y f • ρ) =
      pointScalar p hp f • GaussCentralLineNormalization.genericSectionAt L p hp ρ := by
  subst p
  rfl

private theorem genericSectionAt_localGenerator {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (V : Y.Opens) [Nonempty V]
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L)
    (p : Y) (hp : p = genericPoint Y) (hpV : p ∈ V) :
    GaussCentralLineNormalization.genericSectionAt L p hp
        (CentralGenericLineSectionLift.genericSection L V δ) =
      GaussCentralLineNormalization.localSectionAt L V δ p hpV := by
  subst p
  rfl

private theorem modelNorm_scalar {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}} [IsIntegral Y]
    {base : Y ⟶ Spec (CommRingCat.of R)} [IsProper base]
    (hb : ∀ a, v a ≤ 1) (y : RelativeSchemeValuedPoint v base)
    (hy : y.1.point = genericPoint Y) (L : Y.Modules) (hL : IsInvertible L)
    (f : Y.functionField)
    (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)) :
    modelLineNorm hb y hL
        (GaussCentralLineNormalization.genericSectionAt L y.1.point hy (genericScalar Y f • ρ)) =
      y.1.genericValuation hy f * modelLineNorm hb y hL
        (GaussCentralLineNormalization.genericSectionAt L y.1.point hy ρ) := by
  have hs := congrArg (fun s : Γ(genericLineModule y L, ⊤) => modelLineNorm hb y hL s)
    (genericSectionAt_scalar L y.1.point hy f ρ)
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y.1.point))).hom.hom
      (pointScalar y.1.point hy f) = SchemeValuedPoint.genericResidueEquiv Y y.1.point hy f :=
    (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField y.1.point))).commRingCatIsoToRingEquiv.apply_symm_apply _
  exact hs.trans ((modelLineNorm_smul hb y hL _ _).trans
    (congrArg (fun a => y.1.residueVal a * modelLineNorm hb y hL
      (GaussCentralLineNormalization.genericSectionAt L y.1.point hy ρ)) hc))

/-- The same internally constructed coefficient computes the norm of the original
rational section at EVERY generic-support native point with the actual true center. -/
theorem exists_twoFrame_modelNorm {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    {base : Y ⟶ Spec (CommRingCat.of R)} [IsProper base]
    (hb : ∀ a, v a ≤ 1) (i : C ⟶ Y) (L : Y.Modules) (hL : IsInvertible L)
    (U : Y.Opens) (hηU : i (genericPoint C) ∈ U)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ] (x : C) :
    letI : Nonempty U := ⟨⟨i (genericPoint C),hηU⟩⟩
    ∃ (V : Y.Opens) (hpV : i x ∈ V) (hηV : i (genericPoint C) ∈ V)
      (ε : unitObj V.toScheme ⟶ (pullback V.ι).obj L) (_hε : IsIso ε)
      (W : Y.Opens) (_hWU : W ≤ U) (_hWV : W ≤ V) (hηW : i (genericPoint C) ∈ W)
      (r : Γ(Y,W)ˣ) (u : (Y.presheaf.stalk (i (genericPoint C)))ˣ)
      (f : Y.functionField) (b : C.functionField),
      (u : Y.presheaf.stalk (i (genericPoint C))) =
        Y.presheaf.germ W (i (genericPoint C)) hηW (r : Γ(Y,W)) ∧
      f = @Scheme.germToFunctionField Y _ W ⟨⟨i (genericPoint C),hηW⟩⟩ (r : Γ(Y,W)) ∧
      f = algebraMap (Y.presheaf.stalk (i (genericPoint C))) Y.functionField u ∧
      b = i.stalkMap (genericPoint C) (u : Y.presheaf.stalk (i (genericPoint C))) ∧
      f ≠ 0 ∧ b ≠ 0 ∧
      (letI : Nonempty V := ⟨⟨i x,hpV⟩⟩
       CentralGenericLineSectionLift.genericSection L U δ =
         (Scheme.ΓSpecIso (Y.residueField (genericPoint Y))).inv.hom
           (Y.residue (genericPoint Y) f) • CentralGenericLineSectionLift.genericSection L V ε) ∧
      CentralGenericLineSectionLift.closedGenericSection i L U hηU δ =
        (Scheme.ΓSpecIso (C.residueField (genericPoint C))).inv.hom
          (C.residue (genericPoint C) b) •
            CentralGenericLineSectionLift.closedGenericSection i L V hηV ε ∧
      ∀ (y : RelativeSchemeValuedPoint v base) (hy : y.1.point = genericPoint Y),
        center hb y = i x →
          modelLineNorm hb y hL (GaussCentralLineNormalization.genericSectionAt L y.1.point hy
            (CentralGenericLineSectionLift.genericSection L U δ)) = y.1.genericValuation hy f := by
  let : Nonempty U := ⟨⟨i (genericPoint C),hηU⟩⟩
  obtain ⟨V,hpV,hηV,ε,hε,W,hWU,hWV,hηW,r,u,f,b,-,hu,hf,hb',hfu,hf0,hb0,hρ,hσ⟩ :=
    NumericalGaussCurveLineOrders.exists_twoFrame_coefficients i L hL U hηU δ x
  let : Nonempty V := ⟨⟨i x,hpV⟩⟩
  let : IsIso ε := hε
  refine ⟨V,hpV,hηV,ε,hε,W,hWU,hWV,hηW,r,u,f,b,hu,hf,hfu,hb',hf0,hb0,hρ,hσ,?_⟩
  intro y hy hc
  have hcV : center hb y ∈ V := hc ▸ hpV
  have hlocal := genericSectionAt_localGenerator L V ε y.1.point hy
    (support_mem_of_center_mem hb y V hcV)
  have hone : modelLineNorm hb y hL
      (GaussCentralLineNormalization.genericSectionAt L y.1.point hy
        (CentralGenericLineSectionLift.genericSection L V ε)) = 1 :=
    (congrArg (fun s : Γ(genericLineModule y L, ⊤) => modelLineNorm hb y hL s) hlocal).trans
      (GaussCentralLineNormalization.modelLineNorm_localGenerator hb y L hL V hcV ε)
  have hρy := congrArg (fun s => GaussCentralLineNormalization.genericSectionAt L y.1.point hy s) hρ
  exact (congrArg (fun s : Γ(genericLineModule y L, ⊤) => modelLineNorm hb y hL s) hρy).trans
    ((modelNorm_scalar hb y hy L hL f _).trans
      ((congrArg (fun a : ℝ≥0 => y.1.genericValuation hy f * a) hone).trans (mul_one _)))

end EnvelopeProperty.NumericalGaussCurveLineNorms
