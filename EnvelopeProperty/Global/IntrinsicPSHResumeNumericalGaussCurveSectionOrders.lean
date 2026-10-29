import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalGaussCurveLineNorms
import EnvelopeProperty.AlgGeom.CurveGenericSectionOrders
import EnvelopeProperty.AlgGeom.SchemeLineFramePullbackCoherence

/-! # Actual central frame coefficients of the original generic section -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical NNReal
universe u
namespace EnvelopeProperty.NumericalGaussCurveSectionOrders
open Scheme.Modules SchemeLineSectionEvaluation
open Berkovich

private theorem generic_mem {C : Scheme.{u}} [IsIntegral C]
    (U : C.Opens) [Nonempty U] : genericPoint C ∈ U :=
  ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

private def genericFactor {C : Scheme.{u}} [IsIntegral C]
    (U : C.Opens) [Nonempty U] :
    Spec (CommRingCat.of (C.residueField (genericPoint C))) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (C.fromSpecResidueField (genericPoint C)) (by
    rw [U.range_ι]
    rintro _ ⟨z,rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact generic_mem U)

private theorem genericFactor_comp {C : Scheme.{u}} [IsIntegral C]
    (U : C.Opens) [Nonempty U] :
    genericFactor U ≫ U.ι = C.fromSpecResidueField (genericPoint C) :=
  IsOpenImmersion.lift_fac _ _ _

private def curveFrame {C : Scheme.{u}} [IsIntegral C]
    (L : C.Modules) (U : C.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    CurveGenericSectionOrders.genericFibreModule L ≅
      unitObj (Spec (CommRingCat.of (C.residueField (genericPoint C)))) :=
  frameViaFactor (genericFactor U) U.ι (C.fromSpecResidueField (genericPoint C))
    (genericFactor_comp U) e

private theorem genericCoefficient_eq {C : Scheme.{u}} [IsIntegral C]
    (L : C.Modules)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj L, ⊤))
    (U : C.Opens) [Nonempty U] (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    CurveGenericSectionOrders.genericCoefficient L σ U e =
      (SchemeValuedPoint.genericResidueEquiv C (genericPoint C) rfl).symm
        ((Scheme.ΓSpecIso (CommRingCat.of (C.residueField (genericPoint C)))).hom.hom
          (((curveFrame L U e).hom.val.app (op ⊤)).hom σ)) := by
  rfl

private def closedFactor {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (V : Y.Opens) (hη : i (genericPoint C) ∈ V) :
    Spec (CommRingCat.of (C.residueField (genericPoint C))) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (C.fromSpecResidueField (genericPoint C) ≫ i) (by
    rw [V.range_ι]
    rintro _ ⟨z,rfl⟩
    change i (C.fromSpecResidueField (genericPoint C) z) ∈ V
    rw [Scheme.fromSpecResidueField_apply]
    exact hη)

private theorem closedFactor_comp {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (V : Y.Opens) (hη : i (genericPoint C) ∈ V) :
    closedFactor i V hη ≫ V.ι = C.fromSpecResidueField (genericPoint C) ≫ i :=
  IsOpenImmersion.lift_fac _ _ _

private def closedFrame {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (V : Y.Opens) (hη : i (genericPoint C) ∈ V)
    (e : (pullback V.ι).obj L ≅ unitObj V.toScheme) :
    CurveGenericSectionOrders.genericFibreModule ((pullback i).obj L) ≅
      unitObj (Spec (CommRingCat.of (C.residueField (genericPoint C)))) :=
  (pullbackComp (C.fromSpecResidueField (genericPoint C)) i).app L ≪≫
    frameViaFactor (closedFactor i V hη) V.ι (C.fromSpecResidueField (genericPoint C) ≫ i)
      (closedFactor_comp i V hη) e

private theorem curveFrame_pullback {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (V : Y.Opens) (hη : i (genericPoint C) ∈ V)
    (e : (pullback V.ι).obj L ≅ unitObj V.toScheme) :
    letI : Nonempty (i ⁻¹ᵁ V) := ⟨⟨genericPoint C,hη⟩⟩
    curveFrame ((pullback i).obj L) (i ⁻¹ᵁ V) (localPullbackFrame i V e) =
      closedFrame i L V hη e := by
  let : Nonempty (i ⁻¹ᵁ V) := ⟨⟨genericPoint C,hη⟩⟩
  let q := genericFactor (i ⁻¹ᵁ V)
  let p := C.fromSpecResidueField (genericPoint C)
  have hq : q ≫ (i ⁻¹ᵁ V).ι = p := genericFactor_comp _
  have hfactor : q ≫ (i ∣_ V) = closedFactor i V hη := by
    apply (cancel_mono V.ι).mp
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun a => q ≫ a) (morphismRestrict_ι i V)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ i) hq)))).trans
      (closedFactor_comp i V hη).symm
  have hs := frameViaFactor_pullbackComp q (i ⁻¹ᵁ V).ι p hq i
    (frameViaFactor (i ∣_ V) V.ι ((i ⁻¹ᵁ V).ι ≫ i) (morphismRestrict_ι i V) e)
  have ht := frameViaFactor_comp q (i ∣_ V) V.ι ((i ⁻¹ᵁ V).ι ≫ i)
    (morphismRestrict_ι i V) (p ≫ i) (by rw [← Category.assoc,hq]) e
  change frameViaFactor q (i ⁻¹ᵁ V).ι p hq
    ((pullbackComp (i ⁻¹ᵁ V).ι i).app L ≪≫
      frameViaFactor (i ∣_ V) V.ι ((i ⁻¹ᵁ V).ι ≫ i) (morphismRestrict_ι i V) e) = _
  rw [hs,ht]
  change (pullbackComp p i).app L ≪≫ frameViaFactor (q ≫ (i ∣_ V)) V.ι (p ≫ i) _ e = _
  simp only [hfactor]
  rfl

private theorem factorSection_comp_frame_one {A B C D : Scheme.{u}}
    (p : A ⟶ B) (i : B ⟶ D) (q : A ⟶ C) (b : C ⟶ D)
    (hq : q ≫ b = p ≫ i) {L : D.Modules}
    (δ : unitObj C ⟶ (pullback b).obj L) [IsIso δ] :
    ((((pullbackComp p i).app L ≪≫
      frameViaFactor q b (p ≫ i) hq (asIso δ).symm).hom.val.app (op ⊤)).hom
        (sectionAtOne (pullbackSectionHom q δ ≫
          (frameFactorIso q b (p ≫ i) hq L).hom ≫ ((pullbackComp p i).app L).inv))) =
      (show Γ(A, ⊤) from 1) := by
  let E := (pullbackUnitIso q).symm ≪≫ (pullback q).mapIso (asIso δ) ≪≫
    frameFactorIso q b (p ≫ i) hq L ≪≫ ((pullbackComp p i).app L).symm
  change (E.inv.val.app (op ⊤)).hom
    ((E.hom.val.app (op ⊤)).hom (show Γ(A, ⊤) from 1)) = _
  exact Scheme.Modules.iso_hom_inv_app_applyT E (op ⊤) _

private theorem closedGenerator_frame_one {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (V : Y.Opens) (hη : i (genericPoint C) ∈ V)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ] :
    (((closedFrame i L V hη (asIso δ).symm).hom.val.app (op ⊤)).hom
      (CentralGenericLineSectionLift.closedGenericSection i L V hη δ)) =
        (show Γ(Spec (CommRingCat.of (C.residueField (genericPoint C))), ⊤) from 1) := by
  exact factorSection_comp_frame_one (C.fromSpecResidueField (genericPoint C)) i
    (closedFactor i V hη) V.ι (closedFactor_comp i V hη) δ

/-- The original central generic section of an actual original ambient local
frame has coefficient one in the SAME actual central pullback frame. -/
theorem genericCoefficient_closedGenerator {C Y : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ Y) (L : Y.Modules) (V : Y.Opens) (hη : i (genericPoint C) ∈ V)
    (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L) [IsIso δ] :
    letI : Nonempty (i ⁻¹ᵁ V) := ⟨⟨genericPoint C,hη⟩⟩
    CurveGenericSectionOrders.genericCoefficient ((pullback i).obj L)
      (CentralGenericLineSectionLift.closedGenericSection i L V hη δ) (i ⁻¹ᵁ V)
        (localPullbackFrame i V (asIso δ).symm) = 1 := by
  let : Nonempty (i ⁻¹ᵁ V) := ⟨⟨genericPoint C,hη⟩⟩
  have hframe := curveFrame_pullback i L V hη (asIso δ).symm
  have hvalue := congrArg (fun E : CurveGenericSectionOrders.genericFibreModule ((pullback i).obj L) ≅
      unitObj (Spec (CommRingCat.of (C.residueField (genericPoint C)))) =>
        ((E.hom.val.app (op ⊤)).hom (CentralGenericLineSectionLift.closedGenericSection i L V hη δ))) hframe
  have hone := hvalue.trans (closedGenerator_frame_one i L V hη δ)
  exact (genericCoefficient_eq _ _ _ _).trans
    ((congrArg (fun a => (SchemeValuedPoint.genericResidueEquiv C (genericPoint C) rfl).symm
      ((Scheme.ΓSpecIso (CommRingCat.of (C.residueField (genericPoint C)))).hom.hom a)) hone).trans
        (by simp only [map_one]))

private theorem scalarSection_eq {C : Scheme.{u}} [IsIntegral C]
    (L : C.Modules) (b : C.functionField)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj L, ⊤)) :
    CurveGenericSectionOrders.scalarSection L b σ =
      (Scheme.ΓSpecIso (C.residueField (genericPoint C))).inv.hom
        (C.residue (genericPoint C) b) • σ := by
  rfl

private theorem genericCoefficient_zero {C : Scheme.{u}} [IsIntegral C]
    (L : C.Modules) (U : C.Opens) [Nonempty U]
    (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    CurveGenericSectionOrders.genericCoefficient L 0 U e = 0 := by
  have hz := ((curveFrame L U e).hom.val.app (op ⊤)).hom.map_zero
  exact (genericCoefficient_eq L 0 U e).trans
    ((congrArg (fun a => (SchemeValuedPoint.genericResidueEquiv C (genericPoint C) rfl).symm
      ((Scheme.ΓSpecIso (CommRingCat.of (C.residueField (genericPoint C)))).hom.hom a)) hz).trans
        ((congrArg (SchemeValuedPoint.genericResidueEquiv C (genericPoint C) rfl).symm
          ((Scheme.ΓSpecIso (CommRingCat.of (C.residueField (genericPoint C)))).hom.hom.map_zero)).trans
            (RingEquiv.map_zero _)))

/-- The actual SAME central generic section has coefficient b and native order
ord(b); all internally generated two-frame data and every true-center norm remain. -/
theorem exists_twoFrame_intrinsicOrder {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    [IsLocallyNoetherian C]
    {base : Y ⟶ Spec (CommRingCat.of R)} [IsProper base]
    (hb : ∀ a, v a ≤ 1) (i : C ⟶ Y) (L : Y.Modules) (hL : IsInvertible L)
    (U : Y.Opens) (hηU : i (genericPoint C) ∈ U)
    (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj L) [IsIso δ] (x : C) :
    letI : Nonempty U := ⟨⟨i (genericPoint C),hηU⟩⟩
    CentralGenericLineSectionLift.closedGenericSection i L U hηU δ ≠ 0 ∧
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
      (letI : Nonempty (i ⁻¹ᵁ V) := ⟨⟨x,hpV⟩⟩
       letI : IsIso ε := _hε
       CurveGenericSectionOrders.genericCoefficient ((pullback i).obj L)
         (CentralGenericLineSectionLift.closedGenericSection i L U hηU δ) (i ⁻¹ᵁ V)
           (localPullbackFrame i V (asIso ε).symm) = b) ∧
      CurveGenericSectionOrders.order ((pullback i).obj L) (hL.pullback i)
        (CentralGenericLineSectionLift.closedGenericSection i L U hηU δ) x = C.ord b x ∧
      ∀ (y : RelativeSchemeValuedPoint v base) (hy : y.1.point = genericPoint Y),
        RelativeSchemeValuedPoint.center hb y = i x →
          RelativeSchemeValuedPoint.modelLineNorm hb y hL
            (GaussCentralLineNormalization.genericSectionAt L y.1.point hy
              (CentralGenericLineSectionLift.genericSection L U δ)) = y.1.genericValuation hy f := by
  let : Nonempty U := ⟨⟨i (genericPoint C),hηU⟩⟩
  let : Nonempty (i ⁻¹ᵁ U) := ⟨⟨genericPoint C,hηU⟩⟩
  have hσ0 : CentralGenericLineSectionLift.closedGenericSection i L U hηU δ ≠ 0 := by
    intro hzero
    have hone := genericCoefficient_closedGenerator i L U hηU δ
    rw [hzero,genericCoefficient_zero] at hone
    exact zero_ne_one hone
  obtain ⟨V,hpV,hηV,ε,hε,W,hWU,hWV,hηW,r,u,f,b,hu,hf,hfu,hb',hf0,hb0,hρ,hσ,hNorm⟩ :=
    NumericalGaussCurveLineNorms.exists_twoFrame_modelNorm (base := base) hb i L hL U hηU δ x
  let : IsIso ε := hε
  let : Nonempty (i ⁻¹ᵁ V) := ⟨⟨x,hpV⟩⟩
  have hscalar : CentralGenericLineSectionLift.closedGenericSection i L U hηU δ =
      CurveGenericSectionOrders.scalarSection ((pullback i).obj L) b
        (CentralGenericLineSectionLift.closedGenericSection i L V hηV ε) :=
    hσ.trans (scalarSection_eq _ _ _).symm
  have hcoeff : CurveGenericSectionOrders.genericCoefficient ((pullback i).obj L)
      (CentralGenericLineSectionLift.closedGenericSection i L U hηU δ) (i ⁻¹ᵁ V)
        (localPullbackFrame i V (asIso ε).symm) = b := by
    rw [hscalar,CurveGenericSectionOrders.genericCoefficient_scalarSection,
      genericCoefficient_closedGenerator i L V hηV ε,mul_one]
  have horder := CurveGenericSectionOrders.order_eq_frameCoefficient ((pullback i).obj L)
    (hL.pullback i) (CentralGenericLineSectionLift.closedGenericSection i L U hηU δ) hσ0
      (i ⁻¹ᵁ V) x hpV (localPullbackFrame i V (asIso ε).symm)
  refine ⟨hσ0,V,hpV,hηV,ε,hε,W,hWU,hWV,hηW,r,u,f,b,
    hu,hf,hfu,hb',hf0,hb0,hρ,hσ,hcoeff,?_,hNorm⟩
  exact horder.trans (congrArg (fun a : C.functionField => C.ord a x) hcoeff)

end EnvelopeProperty.NumericalGaussCurveSectionOrders
