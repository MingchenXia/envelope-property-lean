import EnvelopeProperty.Vanishing.NadelGlobalNormalization
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingJoinedNormalization

/-! # Actual WHOLE mixed model and native whole normalization algebra

All geometric comparison inputs of the private functorial helper are consumed
only from the genuine original section/SNC producer. The final public producer
will obtain them internally, rather than assuming chart matching or a desired
normalization isomorphism.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedModel
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching NadelMixedKummer
open NadelGlobalNormalization
private theorem ringEquiv_triangle {M E C D : Type u} [Semiring M] [Semiring E] [Semiring C] [Semiring D]
    (e₁ : M ≃+* E) (e₂ : C ≃+* E) (e₃ : C ≃+* D) (x : M) (b : E) (a : C) (d : D)
    (h₁ : e₁ x = b) (h₂ : e₂ a = b) (h₃ : e₃ a = d) : e₃ (e₂.symm (e₁ x)) = d := by
  rw [h₁, ← h₂, e₂.symm_apply_apply, h₃]

private theorem specIso_triangle {A M C : CommRingCat.{u}} (e : M ≅ C) (α : A ⟶ C) (β : A ⟶ M)
    (h : β ≫ e.hom = α) : Spec.map e.inv ≫ Spec.map α = Spec.map β := by
  rw [← Spec.map_comp, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def specIsoData {A M C : CommRingCat.{u}} (e : M ≅ C) (α : A ⟶ C) (β : A ⟶ M)
    (h : β ≫ e.hom = α) : {i : Spec M ≅ Spec C // i.hom ≫ Spec.map α = Spec.map β} :=
  ⟨Scheme.Spec.mapIso e.symm.op, specIso_triangle e α β h⟩

private theorem specAlgHom_base {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (β : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom β.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact β.commutes r

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶ tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  (y : X) (U : X.affineOpens) (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i).support} → Fin n)
  (j₀ : F.ι → Fin (n + 1))
  (w : Fin (OriginalData.data F n L m σ).length → (Γ(X, U.1))ˣ)

/-- The literal WHOLE ratio coefficient family from the SAME original
branch/auxiliary generators and the actually derived original frame units. -/
def ratioCoefficients : Fin (Fintype.card (Joined.Index F n)) → Γ(X, U.1) :=
  BranchRatios.coefficient (Joined.head F n j₀)
    (Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
    (Joined.auxiliaryGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
    (OriginalData.orderedUnits F n L m σ U w)

/-- The ENTIRE actual mixed ratio algebra, retaining every original root factor. -/
abbrev RatioRing := Ring (Joined.degree F n m) (ratioCoefficients F n L m σ hL hD y U v c j₀ w)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The SAME original native germ algebra, explicit as in the actual whole
native normalization chart; no scalar action is supplied as a hypothesis. -/
local instance coefficientAlgebra [Nonempty U.1] : Algebra Γ(X, U.1) X.functionField :=
  GenericChart.coefficientAlgebra U

/-- The SAME canonical native ring underlying the actual whole generic
tensor commutative ring, as used by the native global normalized chart. -/
local instance actualGenericRing [Nonempty U.1]
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ)) :
    Ring (GenericChart.Ring U (OriginalData.data F n L m σ) e) := Chart.genericRing U _ e

private def rawMap (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support) :
    Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w) →ₐ[Γ(X, U.1)]
      RatioRing F n L m σ hL hD y U v c j₀ w :=
  MultiRatio.rawAlgHom (Joined.degree F n m)
    (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (Joined.head F n j₀)
    (Joined.degree_head F n j₀ m)
    (BranchRatios.coefficient_head _ _ _ _ (Joined.head_head F n j₀)
      (Joined.auxiliaryGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c habsent))
    (BranchRatios.raw_mul_ratio _ _ _ _
      (Joined.branchGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c)
      (Joined.auxiliaryGenerator_head F n (OriginalData.ideals F n L m σ hL hD) j₀ y U v c habsent))

variable [Nonempty U.1]

omit [IsIntegral X] [Nonempty U.1] in
private theorem fromSpec_structure {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) :
    let _ := f.sectionsAlgebra U.1
    U.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U.1))) := by
  let _ := f.sectionsAlgebra U.1
  have hh := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of k))) U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hh
  exact hh.symm

private def modelRingEquiv_of_producedRaw
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    RatioRing F n L m σ hL hD y U v c j₀ w ≃+*
      integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
        (GenericChart.Ring U (OriginalData.data F n L m σ) e) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI : Algebra
      (Ring (Joined.degree F n m) (BranchRatios.rawCoefficient
        (Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (Joined.auxiliaryGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (OriginalData.orderedUnits F n L m σ U w)))
      (Ring (Joined.degree F n m) (BranchRatios.coefficient (Joined.head F n j₀)
        (Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (Joined.auxiliaryGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (OriginalData.orderedUnits F n L m σ U w))) :=
    (rawMap F n L m σ hL hD y U v c j₀ w habsent).toRingHom.toAlgebra
  let enorm := Joined.ratio_normalizationEquiv F n (OriginalData.ideals F n L m σ hL hD)
    j₀ y U v c m (OriginalData.orderedUnits F n L m σ U w) f het hcinj hm htame hG hcomp hyU habsent
  exact enorm.toRingEquiv.trans ((ClosureRelabel.equiv eRaw).symm.trans
    (NadelGlobalNormalization.FunctionField.closureEquiv U (OriginalData.data F n L m σ) e).toRingEquiv)

private theorem modelRingEquiv_rawImage
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) (a : WholeChart.Ring U (OriginalData.data F n L m σ) e) :
      modelRingEquiv_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw
      (rawMap F n L m σ hL hD y U v c j₀ w habsent (eRaw a)) =
        algebraMap (WholeChart.Ring U (OriginalData.data F n L m σ) e)
          (integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
            (GenericChart.Ring U (OriginalData.data F n L m σ) e)) a := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : Algebra
      (Ring (Joined.degree F n m) (BranchRatios.rawCoefficient
        (Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (Joined.auxiliaryGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (OriginalData.orderedUnits F n L m σ U w)))
      (Ring (Joined.degree F n m) (BranchRatios.coefficient (Joined.head F n j₀)
        (Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (Joined.auxiliaryGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (OriginalData.orderedUnits F n L m σ U w))) :=
    (rawMap F n L m σ hL hD y U v c j₀ w habsent).toRingHom.toAlgebra
  let enorm := Joined.ratio_normalizationEquiv F n (OriginalData.ideals F n L m σ hL hD)
    j₀ y U v c m (OriginalData.orderedUnits F n L m σ U w) f het hcinj hm htame hG hcomp hyU habsent
  let einc := ClosureRelabel.equiv eRaw
  let efield := NadelGlobalNormalization.FunctionField.closureEquiv U (OriginalData.data F n L m σ) e
  change efield (einc.symm (enorm (rawMap F n L m σ hL hD y U v c j₀ w habsent (eRaw a)))) = _
  have hn := enorm.commutes (eRaw a)
  change enorm (rawMap F n L m σ hL hD y U v c j₀ w habsent (eRaw a)) = _ at hn
  exact ringEquiv_triangle enorm.toRingEquiv einc efield.toRingEquiv _ _ _ _ hn
    (ClosureRelabel.equiv_algebraMap eRaw a) (efield.commutes a)

private theorem modelRingEquiv_rawCat
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    CommRingCat.ofHom ((rawMap F n L m σ hL hD y U v c j₀ w habsent).toRingHom.comp eRaw.toRingHom) ≫
      (modelRingEquiv_of_producedRaw F n L m σ hL hD y U v c j₀ w
        f het hcinj hm htame hG hcomp hyU habsent e eRaw).toCommRingCatIso.hom =
      CommRingCat.ofHom
        (S := integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
          (GenericChart.Ring U (OriginalData.data F n L m σ) e))
        (algebraMap (WholeChart.Ring U (OriginalData.data F n L m σ) e)
          (integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
            (GenericChart.Ring U (OriginalData.data F n L m σ) e))) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact modelRingEquiv_rawImage F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU habsent e eRaw a

private def modelSpecData_of_producedRaw
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    {i : Spec (.of (RatioRing F n L m σ hL hD y U v c j₀ w)) ≅
      Spec (.of (integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
        (GenericChart.Ring U (OriginalData.data F n L m σ) e))) //
      i.hom ≫ Spec.map (CommRingCat.ofHom
        (S := integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
          (GenericChart.Ring U (OriginalData.data F n L m σ) e))
        (algebraMap (WholeChart.Ring U (OriginalData.data F n L m σ) e)
          (integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
            (GenericChart.Ring U (OriginalData.data F n L m σ) e)))) = Spec.map (CommRingCat.ofHom ((rawMap F n L m σ hL hD y U v c j₀ w habsent).toRingHom.comp eRaw.toRingHom))} := by
  exact specIsoData (modelRingEquiv_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).toCommRingCatIso (CommRingCat.ofHom
        (S := integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
          (GenericChart.Ring U (OriginalData.data F n L m σ) e))
        (algebraMap (WholeChart.Ring U (OriginalData.data F n L m σ) e)
          (integralClosure (WholeChart.Ring U (OriginalData.data F n L m σ) e)
            (GenericChart.Ring U (OriginalData.data F n L m σ) e)))) (CommRingCat.ofHom ((rawMap F n L m σ hL hD y U v c j₀ w habsent).toRingHom.comp eRaw.toRingHom))
    (modelRingEquiv_rawCat F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw)

private def modelSpecIso_of_producedRaw
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    Spec (.of (RatioRing F n L m σ hL hD y U v c j₀ w)) ≅
      (normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).toScheme :=
  (modelSpecData_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).val ≪≫ Chart.imageIso U (OriginalData.data F n L m σ) e

private theorem modelSpecIso_hom
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    (modelSpecIso_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).hom =
      (modelSpecData_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).val.hom ≫
        (Chart.imageIso U (OriginalData.data F n L m σ) e).hom := by rfl

private theorem modelSpecIso_over_raw
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    (modelSpecIso_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).hom ≫
      (normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι ≫ normalizationProjection (OriginalData.data F n L m σ) =
      Spec.map (CommRingCat.ofHom ((rawMap F n L m σ hL hD y U v c j₀ w habsent).toRingHom.comp eRaw.toRingHom)) ≫ RawChart.map U (OriginalData.data F n L m σ) e := by
  rw [modelSpecIso_hom, Category.assoc]
  rw [← Category.assoc (Chart.imageIso U (OriginalData.data F n L m σ) e).hom
      (normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι
      (normalizationProjection (OriginalData.data F n L m σ)),
    Chart.imageIso_inclusion, Chart.map_over_raw, ← Category.assoc,
    (modelSpecData_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).property]

private theorem modelSpecIso_over_original
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    (modelSpecIso_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).hom ≫
      (normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι ≫
        normalizedToOriginal (OriginalData.data F n L m σ) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w))) ≫ U.2.fromSpec := by
  let β := (rawMap F n L m σ hL hD y U v c j₀ w habsent).comp eRaw.toAlgHom
  have hβ : β.toRingHom =
      (rawMap F n L m σ hL hD y U v c j₀ w habsent).toRingHom.comp eRaw.toRingHom := rfl
  have hh := congrArg (fun g => g ≫ projection (OriginalData.data F n L m σ))
    (modelSpecIso_over_raw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw)
  calc
    _ = Spec.map (CommRingCat.ofHom β.toRingHom) ≫
        (RawChart.baseMap U (OriginalData.data F n L m σ) e ≫ U.2.fromSpec) := by
      rw [hβ]
      simpa only [normalizedToOriginal, Category.assoc, RawChart.map_over] using hh
    _ = _ := by
      rw [← Category.assoc]
      exact congrArg (fun g => g ≫ U.2.fromSpec) (specAlgHom_base β)

private theorem modelSpecIso_over_field
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    let _ := f.sectionsAlgebra U.1
    (modelSpecIso_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw).hom ≫
      (normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι ≫
        normalizedToOriginal (OriginalData.data F n L m σ) ≫ f =
      Dimension.SmoothSourceDimension.structureMap (k := k) (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w) := by
  let _ := f.sectionsAlgebra U.1
  have hh := congrArg (fun g => g ≫ f) (modelSpecIso_over_original F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw)
  calc
    _ = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w))) ≫
        (U.2.fromSpec ≫ f) := by simpa only [Category.assoc] using hh
    _ = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U.1))) :=
      congrArg (fun g => Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w))) ≫ g) (fromSpec_structure U f)
    _ = _ := by
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact (IsScalarTower.algebraMap_eq k Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w)).symm

private theorem model_restrict_finite_flat_smooth
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (eRaw : WholeChart.Ring U (OriginalData.data F n L m σ) e ≃ₐ[Γ(X, U.1)]
      Ring (Joined.degree F n m) (OriginalData.rawCoefficients F n L m σ hL hD y U v c w)) :
    IsFinite (normalizedToOriginal (OriginalData.data F n L m σ) ∣_ U.1) ∧
      Flat (normalizedToOriginal (OriginalData.data F n L m σ) ∣_ U.1) ∧
      SmoothOfRelativeDimension n ((normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι ≫
        normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) := by
  let _ := f.sectionsAlgebra U.1
  let i := modelSpecIso_of_producedRaw F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw
  let b := Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w)))
  have hfinite : Module.Finite Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w) :=
    VaryingFinite.finite (Joined.degree F n m) (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
      (fun j => hm (Joined.row F n j))
  have hflat : Module.Flat Γ(X, U.1) (RatioRing F n L m σ hL hD y U v c j₀ w) :=
    VaryingFinite.flat (Joined.degree F n m) (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
      (fun j => hm (Joined.row F n j))
  have : IsFinite b := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  have : Flat b := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  have hi : i.hom ≫ (normalizedToOriginal (OriginalData.data F n L m σ) ∣_ U.1) = b ≫ U.2.isoSpec.inv := by
    apply (cancel_mono U.1.ι).mp
    rw [Category.assoc, morphismRestrict_ι]
    simpa only [IsAffineOpen.fromSpec, Category.assoc] using
      modelSpecIso_over_original F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e eRaw
  refine ⟨?_, ?_, ?_⟩
  · rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite i.hom, hi]
    infer_instance
  · rw [← MorphismProperty.cancel_left_of_respectsIso @Flat i.hom, hi]
    infer_instance
  · rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n) i.hom,
      modelSpecIso_over_field]
    exact Joined.ratio_smoothOfRelativeDimension F n (OriginalData.ideals F n L m σ hL hD)
      j₀ y U v c f het hcinj (Joined.degree F n m) (OriginalData.orderedUnits F n L m σ U w)
      (fun j => hm (Joined.row F n j)) (fun j => htame (Joined.row F n j))

omit [Nonempty U.1] in
/-- The ORIGINAL actual sections, whole joined SNC and empty original rows
INTERNALLY PRODUCE a genuine affine neighbourhood on which the SAME WHOLE
native normalized projection is finite flat and its original field structure
is n-smooth. No chart matching or desired normalization isomorphism is input. -/
theorem exists_geometric_chart_at_closed {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))
    {y : X} (hy : IsClosed ({y} : Set X)) :
    ∃ U : X.affineOpens, y ∈ U.1 ∧
      IsFinite (normalizedToOriginal (OriginalData.data F n L m σ) ∣_ U.1) ∧
      Flat (normalizedToOriginal (OriginalData.data F n L m σ) ∣_ U.1) ∧
      SmoothOfRelativeDimension n ((normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι ≫
        normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) := by
  obtain ⟨j₀, hj₀⟩ := Joined.exists_absent_copies F n (OriginalData.ideals F n L m σ hL hD) hRows y
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, _habsent, w, _hw, ⟨eRaw⟩⟩ :=
    OriginalData.exists_whole_raw_equiv_at_closed F n L m σ hL hD f hG hy
  let : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  have htame (i : F.ι) : IsUnit (m i : Γ(X, U.1)) := by
    let _ := f.sectionsAlgebra U.1
    simpa only [map_natCast] using (hfield i).map (algebraMap k Γ(X, U.1))
  exact ⟨U, hyU, model_restrict_finite_flat_smooth F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU hj₀ e eRaw⟩

omit [Nonempty U.1] in
/-- The actual original Jacobson field geometry extends the PRODUCED whole
finite-flat n-smooth normalization charts from closed points to EVERY original
base point. No cover-existence certificate is assumed. -/
theorem exists_geometric_chart_at_point {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))
    (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      IsFinite (normalizedToOriginal (OriginalData.data F n L m σ) ∣_ U.1) ∧
      Flat (normalizedToOriginal (OriginalData.data F n L m σ) ∣_ U.1) ∧
      SmoothOfRelativeDimension n ((normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι ≫
        normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, _, hxy⟩ := exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ x)
  obtain ⟨U, hyU, hf, hfl, hs⟩ := exists_geometric_chart_at_closed F n L m σ hL hD f hG hRows hm hfield hy
  exact ⟨U, hxy.mem_open U.1.isOpen hyU, hf, hfl, hs⟩

omit [Nonempty U.1] in
/-- The SAME WHOLE native original normalized cover is ACTUALLY finite flat,
and its original field structure is smooth of precisely n. Only actual
original sections, SNC/empty-row data and positive tame original degrees are
inputs; no chart matching, normalization iso, smooth cover or vanishing is input. -/
theorem finite_flat_smooth {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))
 :
    IsFinite (normalizedToOriginal (OriginalData.data F n L m σ)) ∧
      Flat (normalizedToOriginal (OriginalData.data F n L m σ)) ∧
      SmoothOfRelativeDimension n (normalizedToOriginal (OriginalData.data F n L m σ) ≫ f) := by
  classical
  choose V hxV hfinite hflat hsmooth using
    (fun x : X => exists_geometric_chart_at_point F n L m σ hL hD f hG hRows hm hfield x)
  refine ⟨?_, ?_, ?_⟩
  · exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
      (fun x => ⟨(V x).1, hxV x, hfinite x⟩)
  · exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Flat)
      (fun x => ⟨(V x).1, hxV x, hflat x⟩)
  · have hcover : (⨆ x : X, normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ (V x).1) = ⊤ := by
      apply top_le_iff.mp
      intro z _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨normalizedToOriginal (OriginalData.data F n L m σ) z,
        hxV (normalizedToOriginal (OriginalData.data F n L m σ) z)⟩
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n)
      (fun x : X => normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ (V x).1) hcover
    intro x
    simpa only [Category.assoc] using hsmooth x

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedModel
