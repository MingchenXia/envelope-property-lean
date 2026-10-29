import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRatio

/-! # Canonical whole normalized chart with the actual original raw triangle

The actual native normalization-composition proof is reused with the canonical
original rooted equivalence constructed above. All comparison maps are built;
no desired chart or normalization isomorphism is a geometric hypothesis.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots.Model
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching NadelMixedKummer
open NadelGlobalNormalization NadelGlobalAdaptedModel
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

/-- Actual whole normalized chart using the CONSTRUCTED canonical original-root
comparison. No algebra matching or desired geometric isomorphism is input. -/
def canonicalChart
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (hw : ∀ i, WholeChart.coefficients U (OriginalData.data F n L m σ) e i =
      (w i : Γ(X, U.1)) * CyclicSectionSNCUniformFramedCharts.uniformBranches y U v c
        (OriginalData.branchIndex F n L m σ hL hD i) *
        CyclicSectionSNCUniformFramedCharts.uniformBranches y U v c
          (OriginalData.auxiliaryIndex F n L m σ hL hD i)) :
    Spec (.of (RatioRing F n L m σ hL hD y U v c j₀ w)) ≅
      (normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).toScheme :=
  modelSpecIso_of_producedRaw F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU habsent e
    (NadelGlobalAdaptedRoots.rawEquiv F n L m σ hL hD y U v c e w hw)

/-- The canonical whole normalized chart retains the SAME actual original raw
projection, with the CONSTRUCTED canonical original-root map. -/
theorem canonicalChart_over_raw
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U =
      Ideal.span {v (c i)}) (hyU : y ∈ U.1)
    (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
    (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
    (hw : ∀ i, WholeChart.coefficients U (OriginalData.data F n L m σ) e i =
      (w i : Γ(X, U.1)) * CyclicSectionSNCUniformFramedCharts.uniformBranches y U v c
        (OriginalData.branchIndex F n L m σ hL hD i) *
        CyclicSectionSNCUniformFramedCharts.uniformBranches y U v c
          (OriginalData.auxiliaryIndex F n L m σ hL hD i)) :
    (canonicalChart F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e hw).hom ≫
      (normalizedToOriginal (OriginalData.data F n L m σ) ⁻¹ᵁ U.1).ι ≫ normalizationProjection (OriginalData.data F n L m σ) =
      Spec.map (CommRingCat.ofHom (NadelGlobalAdaptedRoots.originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent).toRingHom) ≫ RawChart.map U (OriginalData.data F n L m σ) e :=
  modelSpecIso_over_raw F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU habsent e
    (NadelGlobalAdaptedRoots.rawEquiv F n L m σ hL hD y U v c e w hw)

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots.Model
