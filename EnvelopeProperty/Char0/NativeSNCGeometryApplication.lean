import EnvelopeProperty.Char0.NativeSNCCharts
import EnvelopeProperty.Char0.SNCFamilyJacobianCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0.NativeSNCGeometryApplication

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms NativeEtaleCoordinates NativePreferredJacobian
open NativeSchemeJacobian NativeSchemeJacobianGenerator NativeCoefficientComposition
open AnalyticEtaleJacobian HolomorphicGermCoordinateDerivation Ideal
open HironakaHolomorphicJetMonomialSpan
open scoped Topology Classical

/-- The original affine coefficient evaluation, with its actual original complex algebra action. -/
def coefficientAlgHom {B : Type} [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra f
    B →ₐ[ℂ] HolGerm (ComplexModel n) := by
  let := affinePointFieldAlgebra f
  exact { coefficientGerm f n p with commutes' := coefficientGerm_scalar f n p }

/-- An actual principal-open ideal equality extends along EVERY ring map on
which the original denominator is a unit. The target need not itself be a
localization of the source. -/
theorem map_ideal_eq_of_away_eq {B H : Type*} [CommRing B] [CommRing H]
    (γ : B →+* H) (s : B) (hs : IsUnit (γ s)) (I K : Ideal B)
    (heq : I.map (algebraMap B (Localization.Away s)) =
      K.map (algebraMap B (Localization.Away s))) : I.map γ = K.map γ := by
  let β : Localization.Away s →+* H := IsLocalization.Away.lift s hs
  have hβ : β.comp (algebraMap B (Localization.Away s)) = γ :=
    IsLocalization.Away.lift_comp s hs
  have he := congrArg (Ideal.map β) heq
  simpa only [Ideal.map_map, hβ] using he

/-- The ORIGINAL point's actual membership in a principal affine neighborhood
internally makes the SAME original section a unit in its native analytic germ. -/
theorem affineLift_coefficient_isUnit {Y : Scheme}
    (f : Y ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) (U : Y.affineOpens)
    (hpU : schemeComplexPointImage f p ∈ U.1)
    (s : Γ(Y, U.1)) (hps : schemeComplexPointImage f p ∈ Y.basicOpen s) :
    letI : SmoothOfRelativeDimension n (U.2.fromSpec ≫ f) :=
      (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) f)
    IsUnit (coefficientGerm (U.2.fromSpec ≫ f) n (NativeSNCCharts.affineLift f p U hpU) s) := by
  let : SmoothOfRelativeDimension n (U.2.fromSpec ≫ f) :=
    (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) f)
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  rw [coefficientGerm_eval]
  rw [← affineSchemePointEquivOfStructure_apply]
  apply (affineSchemePointImage_mem_basicOpen (U.2.fromSpec ≫ f)
    (NativeSNCCharts.affineLift f p U hpU) s).mp
  rw [← U.2.fromSpec_preimage_basicOpen]
  change U.2.fromSpec (schemeComplexPointImage (U.2.fromSpec ≫ f)
    (NativeSNCCharts.affineLift f p U hpU)) ∈ Y.basicOpen s
  rw [NativeSNCCharts.affineLift_image]
  exact hps

section AffineJacobian
variable {R B : Type} [CommRing R] [CommRing B]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Spec (.of B) ⟶ Spec (.of R)) (n : ℕ)
  [SmoothOfRelativeDimension n (π ≫ f)] (p : SchemeComplexPoint (π ≫ f))

local instance preferredSourceComplexAlgebra :
    Algebra ℂ (SchemeCoordinateAffineRing (π ≫ f) n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ (π ≫ f))
local instance preferredSourceTargetAlgebra :
    Algebra R (SchemeCoordinateAffineRing (π ≫ f) n p) := (sourceAlgebraMap f π n p).toAlgebra

/-- ALL original target coefficient determinants agree with the SAME actual preferred map. -/
theorem original_analyticJacobianIdeal_eq :
    let := affinePointFieldAlgebra (π ≫ f)
    let := (Spec.preimage π).hom.toAlgebra
    analyticSourceJacobianIdeal (R := R) (coefficientAlgHom (π ≫ f) n p) =
      analyticSourceJacobianIdeal (R := R) (schemeCoordinateModelRegularAlgHom (π ≫ f) n p) := by
  let := affinePointFieldAlgebra (π ≫ f)
  let := (Spec.preimage π).hom.toAlgebra
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext w
  unfold analyticSourceJacobian
  congr 1
  funext i j
  apply congrArg (coordinatePartial j)
  change schemeCoordinateModelRegularAlgHom (π ≫ f) n p
      (targetAlgebraMap (π ≫ f) n p ((Spec.preimage π).hom (w i))) =
    schemeCoordinateModelRegularAlgHom (π ≫ f) n p (sourceAlgebraMap f π n p (w i))
  congr 1
  change (Spec.preimage (standardSmoothComplexAffineChart (π ≫ f) n p).val.map).hom
      ((Spec.preimage π).hom (w i)) =
    (Spec.preimage ((standardSmoothComplexAffineChart (π ≫ f) n p).val.map ≫ π)).hom (w i)
  rw [Spec.preimage_comp]
  rfl

/-- The WHOLE original affine algebraic Jacobian ideal extends to the literal default native
Jacobian of the SAME original morphism. The actual source etale coordinate determinant is a
unit internally, so no monomial or analytic ideal certificate is supplied. -/
theorem original_algebraicJacobianIdeal_map_eq_span_preferred
    [SmoothOfRelativeDimension n f]
    [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]
    (t : Fin n → R)
    (ht : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (v : Fin n → B)
    (hv : letI := affinePointFieldAlgebra (π ≫ f)
      (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale) :
    let := affinePointFieldAlgebra (π ≫ f)
    let := (Spec.preimage π).hom.toAlgebra
    (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map
      (coefficientGerm (π ≫ f) n p) = Ideal.span {preferredJacobian f π n p} := by
  let := affinePointFieldAlgebra (π ≫ f)
  let := (Spec.preimage π).hom.toAlgebra
  have hfactor := analyticSourceJacobianIdeal_factor (R := R)
    (coefficientAlgHom (π ≫ f) n p) v hv
  have hunit : IsUnit (Matrix.of fun i j =>
      coordinatePartial j (coefficientAlgHom (π ≫ f) n p (v i))).det := by
    have hu := targetCoordinateJacobian_isUnit (π ≫ f) n p v hv
    rw [targetCoordinateJacobian_eq] at hu
    exact hu
  rw [Ideal.span_singleton_eq_top.mpr hunit, top_mul] at hfactor
  change analyticSourceJacobianIdeal (R := R) (coefficientAlgHom (π ≫ f) n p) =
    (affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis v hv)).map
      (coefficientGerm (π ≫ f) n p) at hfactor
  exact hfactor.symm.trans ((original_analyticJacobianIdeal_eq f π n p).trans
    (jacobianIdeal_eq_span_preferred f π n p t ht))

end AffineJacobian

private theorem affineStructuralAlgebra_eq {Y : Scheme}
    (f : Y ⟶ Spec (.of ℂ)) (U : Y.affineOpens) :
    affinePointFieldAlgebra (U.2.fromSpec ≫ f) = f.sectionsAlgebra U.1 := by
  apply Algebra.algebra_ext
  intro c
  change (Spec.preimage (U.2.fromSpec ≫ f)).hom c = sectionsHom f U.1 c
  rw [fromSpec_comp_eq_specMap_sectionsHom, Spec.preimage_map]
  rfl

private instance affineSmoothDimension {Y : Scheme}
    (f : Y ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f] (U : Y.affineOpens) :
    SmoothOfRelativeDimension n (U.2.fromSpec ≫ f) :=
  (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) f)

/-- ORIGINAL SNC geometry and the ORIGINAL isomorphism locus internally produce one SAME
actual affine point/etale chart for the WHOLE family factor ideals and the WHOLE original-base
Jacobian ideal. The existing actual principal shrinking is extended through a derived germ
unit, rather than assuming that the holomorphic germ ring is itself a source localization. -/
theorem exists_native_snc_family_jacobian {R : Type} [CommRing R] [Algebra ℂ R]
    {Y : Scheme} (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (p : SchemeComplexPoint (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    (J : (Spec (.of R)).IdealSheafData) [IsIso (π ∣_ J.support.compl)]
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (e : F.ι → ℕ)
    (hJ : J.comap π = ∏ i, F.component i ^ e i)
    {κ : Type*} [Fintype κ] (A : κ → Y.IdealSheafData)
    (hAprod : ∏ j, A j = J.comap π)
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale) :
    let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
    ∃ (U : Y.affineOpens) (v : Fin n → Γ(Y, U.1))
      (hv : Etale (toAffineSpace f U.1 v))
      (q : SchemeComplexPoint (U.2.fromSpec ≫ f))
      (ht : letI := affinePointFieldAlgebra (U.2.fromSpec ≫ f)
        (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale),
      schemeComplexPointImage f p ∈ U.1 ∧ q.val ≫ U.2.fromSpec = p.val ∧
      ∃ c : {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = Ideal.span {v (c i)}) ∧
        ∃ a : κ → {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support} → ℕ,
          (∀ j, (A j).ideal U = Ideal.span {∏ i, v (c i) ^ a j i}) ∧
          (∀ j, ((A j).ideal U).map (coefficientGerm (U.2.fromSpec ≫ f) n q) =
            (Ideal.span {∏ i, coordinateGerm (c i) ^ a j i}).map
              (coordinateGermEquiv (U.2.fromSpec ≫ f) n q v ht).toRingHom) ∧
          ∃ d : {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support} → ℕ,
            (letI := f.sectionsAlgebra U.1
             letI : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
             (affineRelativeJacobianIdeal (R := R) (schemeEtaleDifferentialBasis f U v hv)).map
               (coefficientGerm (U.2.fromSpec ≫ f) n q) =
             (Ideal.span {∏ i, coordinateGerm (c i) ^ d i}).map
               (coordinateGermEquiv (U.2.fromSpec ≫ f) n q v ht).toRingHom) := by
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  have hx : IsClosed ({schemeComplexPointImage f p} : Set Y) := by
    let : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hc := (pointEquivClosedPoint f p).property
    change IsClosed ({p.val (IsLocalRing.closedPoint ℂ)} : Set Y) at hc
    have he : p.val default = p.val (IsLocalRing.closedPoint ℂ) :=
      congrArg p.val (Subsingleton.elim _ _)
    simpa only [schemeComplexPointImage, he] using hc
  obtain ⟨W, _, U, v, hpU, hv, c, hcinj, hcomp, _, a, hA, _, _, s, hW, hps, hJac⟩ :=
    exists_snc_family_jacobian_neighbourhood_at_closed π n J F hF e hJ A hAprod z hz hx
  let q := NativeSNCCharts.affineLift f p U hpU
  have ht : letI := affinePointFieldAlgebra (U.2.fromSpec ≫ f)
      (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale := by
    rw [affineStructuralAlgebra_eq]
    exact (etale_toAffineSpace_iff f U.2 v).mp hv
  have hzero (i : {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support}) :
      HolGerm.eval (coefficientGerm (U.2.fromSpec ≫ f) n q (v (c i))) = 0 := by
    rw [coefficientGerm_eval]
    exact NativeSNCCharts.affineLift_value_zero f p U hpU (F.component i.1) i.2 (v (c i))
      (by rw [hcomp i]; exact Ideal.subset_span (Set.mem_singleton _))
  have hs : IsUnit (coefficientGerm (U.2.fromSpec ≫ f) n q s) :=
    affineLift_coefficient_isUnit f n p U hpU s (by simpa only [hW, Scheme.affineBasicOpen] using hps)
  let := f.sectionsAlgebra U.1
  let : Algebra R Γ(Y, U.1) := (sectionsHom π U.1).toAlgebra
  let := isScalarTower_base_resolutionSections (k := ℂ) π U.1
  obtain ⟨d, hd⟩ := hJac
  have hlocal := hd (Localization.Away s)
  let I : Ideal Γ(Y, U.1) := affineRelativeJacobianIdeal (R := R)
    (schemeEtaleDifferentialBasis f U v hv)
  let K : Ideal Γ(Y, U.1) := Ideal.span {∏ i, v (c i) ^ d i}
  have hK : K.map (algebraMap Γ(Y, U.1) (Localization.Away s)) =
      Ideal.span {∏ i, algebraMap Γ(Y, U.1) (Localization.Away s) (v (c i)) ^ d i} := by
    dsimp only [K]
    rw [Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
  have hIK : I.map (coefficientGerm (U.2.fromSpec ≫ f) n q) =
      K.map (coefficientGerm (U.2.fromSpec ≫ f) n q) :=
    map_ideal_eq_of_away_eq _ s hs I K (hlocal.trans hK.symm)
  refine ⟨U, v, hv, q, ht, hpU, NativeSNCCharts.affineLift_fac f p U hpU,
    c, hcinj, hcomp, a, hA, ?_, d, ?_⟩
  · intro j
    rw [hA j]
    exact map_active_monomial_ideal (U.2.fromSpec ≫ f) n q v ht c (a j) hzero
  · exact hIK.trans (map_active_monomial_ideal (U.2.fromSpec ≫ f) n q v ht c d hzero)

end EnvelopeProperty.Char0.NativeSNCGeometryApplication
