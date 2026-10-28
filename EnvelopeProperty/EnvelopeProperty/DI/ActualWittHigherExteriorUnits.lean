import EnvelopeProperty.DI.ActualWittExteriorCartier
import EnvelopeProperty.DI.CechHigherExteriorUnitProducts

/-! # Original raw units for the actual higher leading representative

The already proved native exterior map is retained. This source only transports
its value from the native source wedge back to the ORIGINAL presheaf wedge unit
needed by the actual normalized higher map.
-/

noncomputable section
namespace EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Cartier DeligneIllusie
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {Xtilde : Scheme.{u}} (f : Xtilde ⟶ Spec (.of (WittTwo.Ring p κ)))
  (n : ℕ) [SmoothOfRelativeDimension n f]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  RelativeEtaleCartierDomain.coefficientAlgebra

private abbrev X := WittTwoSpecialFibreOpens.specialFibre p κ f
private abbrev f₀ : X p κ f ⟶ Spec (.of κ) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p κ))) f
private abbrev U₀ (U : Xtilde.Opens) := WittTwoSpecialFibreOpens.residueOpen p κ f U
private abbrev Y := SchemeRelativeFrobenius.twist p (f₀ p κ f)
private abbrev g : Y p κ f ⟶ Spec (.of κ) :=
  pullback.snd (f₀ p κ f) (SchemeRelativeFrobenius.baseMap (k := κ) p)
private abbrev W (U : Xtilde.Opens) :=
  RelativeTwistedAffineBasis.twistedOpen (f₀ p κ f) p (U₀ p κ f U)
private abbrev fibreSections (U : Xtilde.Opens) : CommRingCat :=
  (X p κ f).presheaf.obj (op (U₀ p κ f U))

variable {U : Xtilde.Opens} (hU : IsAffineOpen U)
  (v : Fin n → Γ(X p κ f,U₀ p κ f U))
  (hv : letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
    (MvPolynomial.aeval (R := κ) v).toRingHom.Etale)

local notation "δ" => RelativeTwistedAffineSections.coefficientSectionMap
  (f₀ p κ f) p (U₀ p κ f U)
local notation "σ" => RelativeTwistedAffineCharts.sectionsIso (f₀ p κ f) p
  (U₀ p κ f U) (WittTwoSpecialFibreOpens.residueOpen_affine p κ f hU)
local notation "B" => fibreSections p κ f U
local notation "T" => RelativeFrobenius.twist (algebraMap κ B) p
local notation "c" => RelativeFrobenius.coefficientMap (algebraMap κ B) p
local notation "P" => CanonicalGeometry.cotangentPresheaf (g p κ f)

private def nativeCotangent (m : CommRingCat.KaehlerDifferential (δ)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
    KaehlerDifferential κ (T) := by
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
  exact RelativeGlobalExteriorExchange.cotangentSemilinear (δ) (c) (σ)
    (RelativeTwistedAffineSections.sectionsIso_coefficient (f₀ p κ f) p
      (U₀ p κ f U) (WittTwoSpecialFibreOpens.residueOpen_affine p κ f hU)) m

omit [PerfectRing κ p] [SmoothOfRelativeDimension n f] in
private theorem domainIso_rawUnit (q : ℕ) (m : Fin q → CommRingCat.KaehlerDifferential (δ)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
    (GeometricLocalCartier.domainIso (f₀ p κ f) p
      (WittTwoSpecialFibreOpens.residueOpen_affine p κ f hU) n v hv q).hom.hom
      (CanonicalGeometry.exteriorSheafSection P q (W p κ f U) m) =
        exteriorPower.ιMulti (T) q (fun i => nativeCotangent p κ f hU (m i)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
  let hU₀ := WittTwoSpecialFibreOpens.residueOpen_affine p κ f hU
  let z := exteriorPower.ιMulti Γ(Y p κ f,W p κ f U) q m
  change (GeometricLocalCartier.rawDomainIso (f₀ p κ f) p hU₀ q).hom.hom
      ((GeometricLocalCartier.twistedUnitIso (f₀ p κ f) p hU₀ n v hv q).inv.hom
        ((GeometricLocalCartier.twistedUnitIso (f₀ p κ f) p hU₀ n v hv q).hom.hom z)) = _
  rw [Iso.hom_inv_id_apply]
  exact GeometricLocalCartier.rawDomainIso_wedge (f₀ p κ f) p hU₀ q m

variable
  (F : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    WittTwoLiftDifference.Lift p κ Γ(Xtilde,U))
  (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    ∀ t, algebraMap Γ(Xtilde,U)
      (WittTwoSmoothDifferentials.ResidueAlgebra p κ Γ(Xtilde,U)) (F t) =
        WittTwoRelativeLift.residueFrobenius p κ Γ(Xtilde,U) t)

/-- Every ORIGINAL raw source wedge is the SAME native source wedge under the
original unit ISO. The frozen actual-Witt sourceWedge theorem then supplies its
native one-form values and original target unit, without copying that formula. -/
theorem model_rawUnit (q : ℕ) (m : Fin q → CommRingCat.KaehlerDifferential (δ)) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
    (ActualWittExteriorCartier.exteriorSections p κ f n hU v hv F hF q).hom
        (CanonicalGeometry.exteriorSheafSection P q (W p κ f U) m) =
      (ActualWittExteriorCartier.exteriorSections p κ f n hU v hv F hF q).hom
        ((GeometricLocalCartier.domainIso (f₀ p κ f) p
          (WittTwoSpecialFibreOpens.residueOpen_affine p κ f hU) n v hv q).inv.hom
            (exteriorPower.ιMulti (T) q (fun i => nativeCotangent p κ f hU (m i)))) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
  let ω : Fin q → KaehlerDifferential κ (T) := fun i => nativeCotangent p κ f hU (m i)
  let D := GeometricLocalCartier.domainIso (f₀ p κ f) p
    (WittTwoSpecialFibreOpens.residueOpen_affine p κ f hU) n v hv q
  have hd := domainIso_rawUnit p κ f n hU v hv q m
  have hi : D.inv.hom (exteriorPower.ιMulti (T) q ω) =
      CanonicalGeometry.exteriorSheafSection P q (W p κ f U) m := by
    calc
      _ = D.inv.hom (D.hom.hom
          (CanonicalGeometry.exteriorSheafSection P q (W p κ f U) m)) :=
        congrArg D.inv.hom hd.symm
      _ = _ := Iso.hom_inv_id_apply D _
  exact congrArg (ActualWittExteriorCartier.exteriorSections p κ f n hU v hv F hF q).hom hi.symm

private def nativeImage (m : CommRingCat.KaehlerDifferential (δ)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
    KaehlerDifferential κ B := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
  let e := WittTwoGeometricDifferential.sectionEquiv p κ f hU
  exact exteriorPower.oneEquiv B (KaehlerDifferential κ B)
    (WittTwoNativeTwistRestriction.oneFormAlongEquiv p κ e F hF
      (nativeCotangent p κ f hU m))

/-- Literal original target units of the SAME original native divided forms. -/
theorem model_rawUnit_value (q : ℕ) (m : Fin q → CommRingCat.KaehlerDifferential (δ)) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
    (ActualWittExteriorCartier.exteriorSections p κ f n hU v hv F hF q).hom
        (CanonicalGeometry.exteriorSheafSection P q (W p κ f U) m) =
      CechHigherExteriorUnitProducts.targetUnit (f₀ p κ f) p (U₀ p κ f U) q
        (exteriorPower.ιMulti B q (fun i => nativeImage p κ f n hU F hF (m i))) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
  have h₁ := model_rawUnit p κ f n hU v hv F hF q m
  have h₂ := ActualWittExteriorCartier.exteriorSections_sourceWedge p κ f n hU v hv F hF q
    (fun i => nativeCotangent p κ f hU (m i))
  simp only [EtaleAffineSectionDifferential.unitEquiv_apply] at h₂
  dsimp only [CechHigherExteriorUnitProducts.targetUnit, nativeImage]
  run_tac do
    let currentNames : Array Lean.Name := #[
      `EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation.X,
      `EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation.f₀,
      `EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation.U₀,
      `EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation.Y,
      `EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation.g,
      `EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation.W,
      `EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation.fibreSections]
    let providerNames : Array Lean.Name := #[
      `EnvelopeProperty.DI.ActualWittExteriorCartier.X,
      `EnvelopeProperty.DI.ActualWittExteriorCartier.f₀,
      `EnvelopeProperty.DI.ActualWittExteriorCartier.U₀,
      `EnvelopeProperty.DI.ActualWittExteriorCartier.W,
      `EnvelopeProperty.DI.ActualWittExteriorCartier.g]
    let ids := ((currentNames.map (Lean.mkPrivateNameCore `EnvelopeProperty.DI.ActualWittHigherExteriorUnits)) ++
      (providerNames.map (Lean.mkPrivateNameCore `EnvelopeProperty.DI.ActualWittExteriorCartier))).map Lean.mkIdent
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only [$[$ids:ident],*] at *))
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut e1 : Option Lean.Expr := none
    let mut e2 : Option Lean.Expr := none
    for d in (← Lean.getLCtx) do
      let sn := d.userName.eraseMacroScopes.toString
      if sn == "h₁" then e1 := some (Lean.mkFVar d.fvarId)
      if sn == "h₂" then e2 := some (Lean.mkFVar d.fvarId)
    let some firstEquation := e1 | throwError "missing original first equation"
    let some secondEquation := e2 | throwError "missing original second equation"
    let t1 ← Lean.Meta.whnf (← Lean.Meta.inferType firstEquation)
    let t2 ← Lean.Meta.whnf (← Lean.Meta.inferType secondEquation)
    let .const nm levels := t1.getAppFn | throwError "first equation not Eq"
    unless nm == ``Eq do throwError "first equation not Eq"
    let a1 := t1.getAppArgs
    let a2 := t2.getAppArgs
    unless a1.size == 3 && a2.size == 3 do throwError "invalid original equation arity"
    let proof := Lean.mkAppN (Lean.mkConst ``Eq.trans levels)
      #[a1[0]!, a1[1]!, a1[2]!, a2[2]!, firstEquation, secondEquation]
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []


/-- The SAME actual exterior map has the actual ordered last-entry product on
EVERY original source wedge, with its original degree transport. -/
theorem model_rawUnit_product (q : ℕ)
    (m : Fin (q+1) → CommRingCat.KaehlerDifferential (δ)) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
    letI := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
    (ActualWittExteriorCartier.exteriorSections p κ f n hU v hv F hF (q+1)).hom
        (CanonicalGeometry.exteriorSheafSection P (q+1) (W p κ f U) m) =
      CechWholeSectionLeibniz.degreeCast (f₀ p κ f) p (Nat.add_comm 1 q) (W p κ f U)
        (DeligneIllusieCechCupProduct.formWedge (f₀ p κ f) p q 1 (W p κ f U)
          ((ActualWittExteriorCartier.exteriorSections p κ f n hU v hv F hF q).hom
            (CanonicalGeometry.exteriorSheafSection P q (W p κ f U) (Fin.init m)))
          ((ActualWittExteriorCartier.exteriorSections p κ f n hU v hv F hF 1).hom
            (CanonicalGeometry.exteriorSheafSection P 1 (W p κ f U)
              (fun _ => m (Fin.last q))))) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := WittTwoSpecialFibreEtaleBasis.smoothOfRelativeDimension p κ f n
  let := CanonicalGeometry.cotangentOpenAlgebra (f₀ p κ f) (U₀ p κ f U)
  rw [model_rawUnit_value, model_rawUnit_value, model_rawUnit_value]
  exact (CechHigherExteriorUnitProducts.targetUnit_init_last (f₀ p κ f) p (U₀ p κ f U)
    q (fun i => nativeImage p κ f n hU F hF (m i))).symm

end EnvelopeProperty.DI.ActualWittHigherExteriorEvaluation
