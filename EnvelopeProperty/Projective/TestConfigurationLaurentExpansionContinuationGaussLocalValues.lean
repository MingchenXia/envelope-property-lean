import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationTotalGauss

/-! # Actual local coefficient maps on the original TC Gauss morphism

The SAME original geometric projection derives every support preimage and
local appLE ring-map identity. No local comparison or coefficient-value
certificate is an input. Literal finite sums and intrinsic line norms are
subsequent consumers of these actual original maps.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich

/-- Actual restriction followed by whole-source appLE is the SAME whole global map. -/
theorem originalSchemeAppLE_top_global {W S : Scheme.{u}} (g : W ⟶ S)
    (V : S.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) :
    S.presheaf.map (homOfLE le_top).op ≫ g.appLE V ⊤ h = g.appTop := by
  rw [Scheme.Hom.map_appLE]
  change g.appTop ≫ W.presheaf.map (𝟙 (op (⊤ : W.Opens))) = g.appTop
  rw [W.presheaf.map_id, Category.comp_id]

/-- Native evaluation on a genuine whole preimage is its ACTUAL appLE pullback value. -/
theorem originalSchemeValuedPoint_eval_appLE {W S : Scheme.{u}} (g : W ⟶ S)
    (y : SchemeValuedPoint W) (V : S.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) (s : Γ(S, V)) :
    SchemeValuedPoint.eval (SchemeValuedPoint.map g y) V (h trivial) s =
      SchemeValuedPoint.eval y ⊤ trivial (g.appLE V ⊤ h s) := by
  rw [SchemeValuedPoint.eval_map]
  exact (SchemeValuedPoint.eval_restrict y (g ⁻¹ᵁ V) ⊤ h trivial (g.app V s)).symm

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom) (U : X.left.Opens) (hx : x.1.point ∈ U)

include hx in
/-- The SAME original geometric Gauss projection DERIVES the whole preimage
of every actual original support neighborhood, without a preimage input. -/
theorem originalTestConfigurationGaussMorph_preimage :
    originalTestConfigurationGaussMorph C x ⁻¹ᵁ
        (originalTestConfigurationUnitProjection C ⁻¹ᵁ U) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, originalTestConfigurationGaussMorph_projection,
    Scheme.Hom.comp_preimage,
    SchemeValuedPoint.fromSpecResidueField_preimage_eq_top x.1.point U hx,
    Scheme.Hom.preimage_top]

/-- The ACTUAL original local appLE map followed by the actual affine section
isomorphism, with its whole preimage derived from the SAME original geometry. -/
def originalTestConfigurationGaussLocalPullback :
    Γ(C.unitOpen.toScheme, originalTestConfigurationUnitProjection C ⁻¹ᵁ U) →+*
      (X.left.residueField x.1.point)[T;T⁻¹] :=
  (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom.hom.comp
    ((originalTestConfigurationGaussMorph C x).appLE
      (originalTestConfigurationUnitProjection C ⁻¹ᵁ U) ⊤
      (by rw [originalTestConfigurationGaussMorph_preimage C x U hx])).hom

/-- The ENTIRE actual original local coefficient ring map is the SAME genuine
original residue evaluation followed by the actual Laurent constant inclusion. -/
theorem originalTestConfigurationGaussLocalPullback_coefficients :
    (originalTestConfigurationUnitProjection C).app U ≫
        CommRingCat.ofHom (originalTestConfigurationGaussLocalPullback C x U hx) =
      X.left.evaluation U x.1.point hx ≫ CommRingCat.ofHom
        (LaurentPolynomial.C : X.left.residueField x.1.point →+*
          (X.left.residueField x.1.point)[T;T⁻¹]) := by
  let hG : ⊤ ≤ originalTestConfigurationGaussMorph C x ⁻¹ᵁ
      (originalTestConfigurationUnitProjection C ⁻¹ᵁ U) := by
    rw [originalTestConfigurationGaussMorph_preimage C x U hx]
  let hκ : ⊤ ≤ X.left.fromSpecResidueField x.1.point ⁻¹ᵁ U := by
    rw [SchemeValuedPoint.fromSpecResidueField_preimage_eq_top x.1.point U hx]
  let i := Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.C : X.left.residueField x.1.point →+*
      (X.left.residueField x.1.point)[T;T⁻¹]))
  change (originalTestConfigurationUnitProjection C).app U ≫
      (originalTestConfigurationGaussMorph C x).appLE
        (originalTestConfigurationUnitProjection C ⁻¹ᵁ U) ⊤ hG ≫
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom = _
  rw [← Category.assoc, ← Scheme.Hom.comp_appLE]
  simp only [originalTestConfigurationGaussMorph_projection]
  have hcomp := Scheme.Hom.appLE_comp_appLE i (X.left.fromSpecResidueField x.1.point)
    U ⊤ ⊤ hκ le_top
  rw [← hcomp]
  have hi : i.appLE ⊤ ⊤ le_top = i.appTop := by simp [Scheme.Hom.appLE]
  rw [hi, Category.assoc]
  change (X.left.fromSpecResidueField x.1.point).appLE U ⊤ hκ ≫
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : X.left.residueField x.1.point →+*
        (X.left.residueField x.1.point)[T;T⁻¹]))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom = _
  rw [Scheme.ΓSpecIso_naturality, ← Category.assoc]
  exact congrArg (fun a : Γ(X.left, U) ⟶ X.left.residueField x.1.point =>
    a ≫ CommRingCat.ofHom (LaurentPolynomial.C : X.left.residueField x.1.point →+*
      (X.left.residueField x.1.point)[T;T⁻¹]))
    (SchemeValuedPoint.fromSpecResidueField_appLE_top x.1.point U hx hκ)

/-- EVERY actual original local coefficient has its literal actual residue value. -/
theorem originalTestConfigurationGaussLocalPullback_coefficient_apply (a : Γ(X.left, U)) :
    originalTestConfigurationGaussLocalPullback C x U hx
        ((originalTestConfigurationUnitProjection C).app U a) =
      LaurentPolynomial.C (X.left.evaluation U x.1.point hx a) :=
  congrArg (fun f : Γ(X.left, U) ⟶
    CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹] => f a)
    (originalTestConfigurationGaussLocalPullback_coefficients C x U hx)

/-- The ORIGINAL global parameter monomial, genuinely restricted to the
original projection preimage of U; no point is used in this section. -/
def originalTestConfigurationLocalParameterPower (n : ℤ) :
    Γ(C.unitOpen.toScheme, originalTestConfigurationUnitProjection C ⁻¹ᵁ U) :=
  C.unitOpen.toScheme.presheaf.map (homOfLE le_top).op
    ((originalTestConfigurationUnitParameter C).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv (LaurentPolynomial.T n)))

/-- EVERY integer original local coordinate power pulls back through the
SAME genuine Gauss morphism to the SAME literal residue Laurent monomial. -/
theorem originalTestConfigurationGaussLocalPullback_parameter_apply (n : ℤ) :
    originalTestConfigurationGaussLocalPullback C x U hx
        (originalTestConfigurationLocalParameterPower C U n) =
      (LaurentPolynomial.T n : (X.left.residueField x.1.point)[T;T⁻¹]) := by
  let g := originalTestConfigurationGaussMorph C x
  let V := originalTestConfigurationUnitProjection C ⁻¹ᵁ U
  let hG : ⊤ ≤ g ⁻¹ᵁ V := by
    rw [originalTestConfigurationGaussMorph_preimage C x U hx]
  let t := (originalTestConfigurationUnitParameter C).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv (LaurentPolynomial.T n))
  have hrest := congrArg
    (fun a : Γ(C.unitOpen.toScheme, ⊤) ⟶
        Γ(Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹]), ⊤) =>
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom (a t))
    (originalSchemeAppLE_top_global g V hG)
  change originalTestConfigurationGaussLocalPullback C x U hx
      (originalTestConfigurationLocalParameterPower C U n) =
    (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      (g.appTop t) at hrest
  have hq : (originalTestConfigurationUnitParameter C).appTop ≫ g.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom =
    (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).hom ≫ CommRingCat.ofHom
      (AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x)) := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop,
      originalTestConfigurationGaussMorph_parameter, Scheme.ΓSpecIso_naturality]
  have ht := congrArg
    (fun a : Γ(Spec (CommRingCat.of k[T;T⁻¹]), ⊤) ⟶
        CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹] =>
      a ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv (LaurentPolynomial.T n))) hq
  change (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).hom
      (g.appTop t) =
    AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x)
      ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv (LaurentPolynomial.T n))) at ht
  have hi : (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).inv (LaurentPolynomial.T n)) =
      (LaurentPolynomial.T n : k[T;T⁻¹]) :=
    (Scheme.ΓSpecIso (CommRingCat.of k[T;T⁻¹])).commRingCatIsoToRingEquiv.apply_symm_apply _
  rw [hi, originalLaurentCoefficientMap_T] at ht
  exact hrest.trans ht

/-- The LITERAL original finite Laurent sum of actual local coefficient
pullbacks times actual original restricted parameter powers. -/
def originalTestConfigurationLocalLaurentSection (F : (Γ(X.left, U))[T;T⁻¹]) :
    Γ(C.unitOpen.toScheme, originalTestConfigurationUnitProjection C ⁻¹ᵁ U) :=
  F.coeff.sum (fun n a => (originalTestConfigurationUnitProjection C).app U a *
    originalTestConfigurationLocalParameterPower C U n)

/-- The actual original local pullback of the LITERAL original finite sum
is its SAME actual coefficientwise residue Laurent polynomial. -/
theorem originalTestConfigurationGaussLocalPullback_laurent
    (F : (Γ(X.left, U))[T;T⁻¹]) :
    originalTestConfigurationGaussLocalPullback C x U hx
        (originalTestConfigurationLocalLaurentSection C U F) =
      AddMonoidAlgebra.mapRingHom ℤ (X.left.evaluation U x.1.point hx).hom F := by
  classical
  have hF : F = ∑ n ∈ F.coeff.support, AddMonoidAlgebra.single n (F.coeff n) := by
    simpa only [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single F).symm
  have hm := congrArg (AddMonoidAlgebra.mapRingHom ℤ
    (X.left.evaluation U x.1.point hx).hom) hF
  simp only [map_sum, LaurentPolynomial.single_eq_C_mul_T] at hm
  rw [hm]
  simp only [originalTestConfigurationLocalLaurentSection, Finsupp.sum,
    map_sum, map_mul, originalTestConfigurationGaussLocalPullback_coefficient_apply,
    originalTestConfigurationGaussLocalPullback_parameter_apply,
    originalLaurentCoefficientMap_C, originalLaurentCoefficientMap_T]

include hx in
/-- The actual original unit-open Gauss point lies in the SAME actual
projection preimage of EVERY original support neighborhood. -/
theorem originalTestConfigurationUnitGaussPoint_mem (r : ℝ≥0) (hr : 0 < r) :
    (originalTestConfigurationUnitGaussPoint C x r hr).point ∈
      originalTestConfigurationUnitProjection C ⁻¹ᵁ U := by
  change originalTestConfigurationUnitProjection C
    (originalTestConfigurationUnitGaussPoint C x r hr).point ∈ U
  have hp := congrArg (fun y : SchemeValuedPoint X.left => y.point)
    (originalTestConfigurationUnitGaussPoint_projection C x r hr)
  change originalTestConfigurationUnitProjection C
    (originalTestConfigurationUnitGaussPoint C x r hr).point = x.1.point at hp
  rw [hp]
  exact hx

/-- The SAME actual original TC Gauss point evaluates EVERY LITERAL local
Laurent sum by its ORIGINAL finite coefficient maximum, including coefficients
whose residue vanishes. No decomposition or norm comparison is a premise. -/
theorem originalTestConfigurationUnitGaussPoint_local_laurent_max
    (r : ℝ≥0) (hr : 0 < r) (F : (Γ(X.left, U))[T;T⁻¹]) :
    SchemeValuedPoint.eval (originalTestConfigurationUnitGaussPoint C x r hr)
        (originalTestConfigurationUnitProjection C ⁻¹ᵁ U)
        (originalTestConfigurationUnitGaussPoint_mem C x U hx r hr)
        (originalTestConfigurationLocalLaurentSection C U F) =
      F.coeff.support.sup (fun n =>
        SchemeValuedPoint.eval x.1 U hx (F.coeff n) * r ^ n) := by
  let g := originalTestConfigurationGaussMorph C x
  let V := originalTestConfigurationUnitProjection C ⁻¹ᵁ U
  let hG : ⊤ ≤ g ⁻¹ᵁ V := by
    rw [originalTestConfigurationGaussMorph_preimage C x U hx]
  change SchemeValuedPoint.eval
      (SchemeValuedPoint.map g (originalNativeLaurentGaussPoint x.1.residueVal r hr))
      V (hG trivial) (originalTestConfigurationLocalLaurentSection C U F) = _
  rw [originalSchemeValuedPoint_eval_appLE g
    (originalNativeLaurentGaussPoint x.1.residueVal r hr) V hG]
  have hs : g.appLE V ⊤ hG (originalTestConfigurationLocalLaurentSection C U F) =
      (Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).inv
        (originalTestConfigurationGaussLocalPullback C x U hx
          (originalTestConfigurationLocalLaurentSection C U F)) := by
    exact ((Scheme.ΓSpecIso (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹])).commRingCatIsoToRingEquiv.symm_apply_apply _).symm
  rw [hs, originalNativeLaurentGaussPoint_eval,
    originalTestConfigurationGaussLocalPullback_laurent]
  have hv := congrArg (fun a : Spectrum ((Γ(X.left, U))[T;T⁻¹]) => a.val F)
    (originalLaurentGauss_comap (X.left.evaluation U x.1.point hx).hom x.1.residueVal r hr)
  change (Spectrum.laurentGauss x.1.residueVal r hr).val
      (AddMonoidAlgebra.mapRingHom ℤ (X.left.evaluation U x.1.point hx).hom F) =
    (Spectrum.laurentGauss (x.1.residueVal.comap (X.left.evaluation U x.1.point hx).hom) r hr).val F at hv
  rw [hv, Spectrum.laurentGauss_val_eq_sup]
  rfl

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
