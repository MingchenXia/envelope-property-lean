import EnvelopeProperty.Berkovich.SchemeDVRModelPoints
import EnvelopeProperty.AlgGeom.SchemeStalkCoefficients

/-! # Actual prescribed Gauss native points with every original vertical center -/
open scoped NNReal Polynomial
open CategoryTheory AlgebraicGeometry Classical
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- Every ORIGINAL special-fibre point on an actual proper dominant integral
k[t]-model is the TRUE center of an ACTUAL prescribed Gauss native point.
All DVR, coefficient, nonvanishing and normalization data are DERIVED. -/
theorem exists_gaussPoint_center_of_vertical
    (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper f] [IsDominant f]
    (x : X) (hx : Polynomial.X ∈ (f x).asIdeal) :
    ∃ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f,
      center ProjBerk.gaussModelCoefficient_le_one y = x := by
  let B := X.presheaf.stalk x
  let ρ := SchemeStalkCoefficients.coefficientMap f x
  have hρ : Function.Injective ρ := SchemeStalkCoefficients.coefficientMap_injective f x
  have htB : ρ Polynomial.X ≠ 0 := by
    simpa only [map_zero] using hρ.ne (Polynomial.X_ne_zero (R := k))
  have hmB : ρ Polynomial.X ∈ IsLocalRing.maximalIdeal B := by
    change Polynomial.X ∈ (IsLocalRing.maximalIdeal B).comap ρ
    rw [SchemeStalkCoefficients.maximalIdeal_comap_coefficientMap]
    exact hx
  have hnf : ¬IsField B := by
    intro hfield
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield,Ideal.mem_bot] at hmB
    exact htB hmB
  let f₀ : X ⟶ Spec (CommRingCat.of k) := f ≫ Spec.map (CommRingCat.ofHom Polynomial.C)
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType k (Polynomial k)))
  let : LocallyOfFiniteType f₀ := by dsimp only [f₀]; infer_instance
  let _ := f₀.stalkAlgebra x
  let : Algebra.EssFiniteType k B := SchemeStalkCenteredDVR.essFiniteType_stalkAlgebra f₀ x
  obtain ⟨V,hV,hcenter⟩ := EssentiallyFiniteTypeCenteredDVR.exists_centeredDVR k B X.functionField hnf
  let := hV
  let φ : Polynomial k →+* V := (algebraMap B V).comp ρ
  let t : V := φ Polynomial.X
  let : Algebra k V := (φ.comp Polynomial.C).toAlgebra
  let q : Spec (CommRingCat.of V) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap B V)) ≫ X.fromSpecStalk x
  have hqx : q (IsLocalRing.closedPoint V) = x := by
    have hc : (Spec.map (CommRingCat.ofHom (algebraMap B V))) (IsLocalRing.closedPoint V) =
        IsLocalRing.closedPoint B := PrimeSpectrum.ext hcenter
    change (X.fromSpecStalk x) ((Spec.map (CommRingCat.ofHom (algebraMap B V)))
      (IsLocalRing.closedPoint V)) = x
    rw [hc,Scheme.fromSpecStalk_closedPoint]
  have hqt : q ≫ f = Spec.map (CommRingCat.ofHom φ) := by
    change (Spec.map (CommRingCat.ofHom (algebraMap B V)) ≫ X.fromSpecStalk x) ≫ f = _
    rw [Category.assoc,SchemeStalkCoefficients.fromSpecStalk_structureMap,← Spec.map_comp]
    rfl
  have hφ : (Polynomial.aeval t).toRingHom = φ := by
    apply Polynomial.ringHom_ext
    · intro a
      exact Polynomial.aeval_C t a
    · exact Polynomial.aeval_X t
  have htt : t ≠ 0 := by
    intro h
    apply htB
    apply IsFractionRing.injective B X.functionField
    have hh := congrArg (fun a : V => (a : X.functionField)) h
    change algebraMap B X.functionField (ρ Polynomial.X) = 0 at hh
    simpa only [map_zero] using hh
  have htm : t ∈ IsLocalRing.maximalIdeal V := by
    change ρ Polynomial.X ∈ (IsLocalRing.maximalIdeal V).comap (algebraMap B V)
    rw [hcenter]
    exact hmB
  rw [← hφ] at hqt
  obtain ⟨y,hy⟩ := exists_nativeDVRPoint_gauss_center (k := k) q t htt htm hqt
  exact ⟨y,hy.trans hqx⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
