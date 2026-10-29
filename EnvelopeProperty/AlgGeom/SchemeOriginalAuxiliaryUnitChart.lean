import EnvelopeProperty.AlgGeom.SchemeOriginalAdaptedTrait
import Hironaka.Scheme.Smooth.EtaleLocal
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace IsLocalRing Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeOriginalAuxiliaryUnitChart
/-- The literal original polynomial coordinate section of the actual structure map. -/
def polynomialSection {F : Type u} [CommRing F] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of F[X])) : Γ(Y,⊤) :=
  f.appTop ((Scheme.ΓSpecIso (.of F[X])).inv Polynomial.X)

private theorem polynomialSection_value {F V : Type u} [CommRing F] [CommRing V] [IsLocalRing V]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of F[X])) (q : Spec (.of V) ⟶ Y)
    (α : F[X] →+* V) (hq : q ≫ f = Spec.map (CommRingCat.ofHom α)) :
    (Scheme.stalkClosedPointTo q) (Y.presheaf.germ ⊤ (q (closedPoint V)) trivial
      (polynomialSection f)) = α Polynomial.X := by
  have h := RingHom.congr_fun (SchemeLocalResidueCoefficients.stalkClosedPointTo_coefficients f q α hq) Polynomial.X
  change (Scheme.stalkClosedPointTo q) (Y.presheaf.germ ⊤ (q (closedPoint V)) trivial
      (polynomialSection f)) = _ at h
  exact h

private theorem exists_whole_unit_factorization {Y : Scheme.{u}} [IsIntegral Y]
    {V : Type u} [CommRing V] [IsLocalRing V] (q : Spec (.of V) ⟶ Y)
    (hbij : Function.Bijective (Scheme.stalkClosedPointTo q).hom)
    (τ π : Γ(Y,⊤)) (v : Vˣ) (e : ℕ)
    (hfactor : (Scheme.stalkClosedPointTo q) (Y.presheaf.germ ⊤ (q (closedPoint V)) trivial τ) =
      v * (Scheme.stalkClosedPointTo q) (Y.presheaf.germ ⊤ (q (closedPoint V)) trivial π) ^ e) :
    ∃ (U : Y.affineOpens) (_hxU : q (closedPoint V) ∈ U.1) (w : Γ(Y,U.1)),
      IsUnit w ∧
      Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op τ =
        w * (Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op π) ^ e := by
  let x := q (closedPoint V)
  let φ := RingEquiv.ofBijective (Scheme.stalkClosedPointTo q).hom hbij
  let u : (Y.presheaf.stalk x)ˣ := Units.map φ.symm.toMonoidHom v
  have hu : φ (u : Y.presheaf.stalk x) = v := φ.apply_symm_apply v
  have hg : Y.presheaf.germ ⊤ x trivial τ =
      (u : Y.presheaf.stalk x) * (Y.presheaf.germ ⊤ x trivial π) ^ e := by
    apply φ.injective
    rw [map_mul,map_pow,hu]
    exact hfactor
  obtain ⟨W,hW,hxW,-⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Y.Opens) from trivial)
  let a : Fin 2 → Y.presheaf.stalk x := ![(u : Y.presheaf.stalk x),(↑u⁻¹ : Y.presheaf.stalk x)]
  obtain ⟨U,hxU,-,w,hw⟩ := exists_affineOpen_germ_eq ⟨W,hW⟩ hxW a
  have hw0 : Y.presheaf.germ U.1 x hxU (w 0) = u := by simpa [a] using hw 0
  have hw1 : Y.presheaf.germ U.1 x hxU (w 1) = (↑u⁻¹ : Y.presheaf.stalk x) := by simpa [a] using hw 1
  have hinv : w 0 * w 1 = 1 := by
    apply germ_injective_of_isIntegral Y x hxU
    rw [map_mul,map_one,hw0,hw1]
    exact Units.mul_inv u
  refine ⟨U,hxU,w 0,isUnit_iff_exists_inv.mpr ⟨w 1,hinv⟩,?_⟩
  apply germ_injective_of_isIntegral Y x hxU
  rw [Y.presheaf.germ_res_apply,map_mul,map_pow,hw0,Y.presheaf.germ_res_apply]
  exact hg

private theorem polynomialSection_aeval_value {F V : Type u} [CommRing F] [CommRing V]
    [IsLocalRing V] [Algebra F V] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of F[X]))
    (q : Spec (.of V) ⟶ Y) (π : V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval π).toRingHom)) :
    (Scheme.stalkClosedPointTo q) (Y.presheaf.germ ⊤ (q (closedPoint V)) trivial
      (polynomialSection f)) = π := by
  have h := polynomialSection_value f q (Polynomial.aeval π).toRingHom hq
  change (Scheme.stalkClosedPointTo q) (Y.presheaf.germ ⊤ (q (closedPoint V)) trivial
      (polynomialSection f)) = (Polynomial.aeval π) Polynomial.X at h
  rw [Polynomial.aeval_X] at h
  exact h

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (V : Subalgebra k X.functionField)
    [IsDiscreteValuationRing V] [IsFractionRing V X.functionField]
    (f : X ⟶ Spec (.of (Polynomial k))) [IsProper f]
    (q : Spec (.of V) ⟶ X) (t : V)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
    [Algebra.EssFiniteType k V]
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ q =
      X.fromSpecStalk (genericPoint X))
    {ι : Type u} [Finite ι] (u : ι → V)
    (hu : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
      letI := (SchemeLocalResidueCoefficients.residueAlgHom
        (SchemeRelativeResidueSliceFinite.originalBaseMap f) q
        (SchemeRelativeResidueSliceFinite.originalBaseMap_trait V f q t hq)).toAlgebra;
      IsTranscendenceBasis (X.residueField (q (closedPoint V))) (residue V ∘ u))
    (hEV : (IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))).toSubalgebra ≤ V)
    (hL : letI := SchemePointClosureCurve.residueAlgebra (q (closedPoint V)) (SchemeRelativeResidueSliceFinite.originalBaseMap f);
      Algebra.trdeg k (X.residueField (q (closedPoint V))) = 1)
local notation "E" => IntermediateField.adjoin k (Set.range fun i => (u i : X.functionField))
local notation "N" => SchemeCoefficientSliceNormalization.model V f q t hq E hEV
local notation "ℓ" => SchemeCoefficientSliceNormalization.centerLift V f q t hq E hEV
local notation "c" => ℓ (closedPoint V)
private local instance normalized_integral : IsIntegral N :=
  SchemeCoefficientSliceNormalization.model_isIntegral V f q t hq E hEV



local notation "fN" => SchemeCoefficientSliceNormalization.structureMap V f q t hq E hEV

include hgen hu hL in
/-- The SAME original t has a genuine WHOLE unit-power equation on a smaller
actual adapted etale chart, using the SAME auxiliary scalar uniformizer and original e. -/
theorem exists_whole_unit_chart [CharZero k] (ht0 : t ≠ 0) (ht : t ∈ maximalIdeal V) :
    letI := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
    ∃ (A : Scheme.{u}) (j : A ⟶ N) (g : A ⟶ Spec (.of (MvPolynomial (Fin 2) E)))
      (qA : Spec (.of V) ⟶ A) (π : V) (v : Vˣ) (e : ℕ),
      IsAffine A ∧ IsOpenImmersion j ∧ Etale g ∧ qA ≫ j = ℓ ∧ Irreducible π ∧
      qA ≫ g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E =
        Spec.map (CommRingCat.ofHom (Polynomial.aeval π).toRingHom) ∧
      ((N).fromSpecResidueField c).ker.comap j = (coordinateSubspace E 2 1).comap g ∧
      0 < e ∧ t = v * π ^ e ∧ Ring.ord V t = e ∧
      ∃ (U : A.affineOpens) (_hxU : qA (closedPoint V) ∈ U.1) (w : Γ(A,U.1)),
        IsUnit w ∧ Etale (U.1.ι ≫ g) ∧
        SmoothOfRelativeDimension 1 (U.1.ι ≫ g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E) ∧
        A.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op (polynomialSection (j ≫ fN)) =
          w * (A.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
            (polynomialSection (g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E))) ^ e ∧
        ∃ qU : Spec (.of V) ⟶ U.1, qU ≫ U.1.ι = qA := by
  let := (SchemePolynomialCoefficientSlice.coefficientMap V E hEV).toAlgebra
  obtain ⟨A,j,g,qA,π,v,e,hA,hj,hg,hs,hproj,hbij,hπ,haux,hres,he,hfactor,hord⟩ :=
    SchemeOriginalAdaptedTrait.exists_original_uniformizer_trait V f q t hq hgen u hu hEV hL ht0 ht
  let := hj
  let := hg
  let : SmoothOfRelativeDimension 1 (g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E) := hs
  let : Nonempty A := ⟨qA (closedPoint V)⟩
  let : IsIntegral A := isIntegral_of_isOpenImmersion j
  let τ := polynomialSection (j ≫ fN)
  let p := polynomialSection (g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E)
  have htmap : qA ≫ (j ≫ fN) = Spec.map
      (CommRingCat.ofHom (SchemePolynomialCoefficientSlice.polynomialMap V t E hEV)) := by
    rw [← Category.assoc,hproj]
    exact SchemeCoefficientSliceNormalization.centerLift_structure V f q t hq E hEV
  have hτ : (Scheme.stalkClosedPointTo qA) (A.presheaf.germ ⊤ (qA (closedPoint V)) trivial τ) = t := by
    have h := polynomialSection_value (j ≫ fN) qA _ htmap
    simpa only [SchemePolynomialCoefficientSlice.polynomialMap,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X] using h
  have hp : (Scheme.stalkClosedPointTo qA) (A.presheaf.germ ⊤ (qA (closedPoint V)) trivial p) = π :=
    polynomialSection_aeval_value (g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E) qA π haux
  have hlocal : (Scheme.stalkClosedPointTo qA) (A.presheaf.germ ⊤ (qA (closedPoint V)) trivial τ) =
      v * (Scheme.stalkClosedPointTo qA) (A.presheaf.germ ⊤ (qA (closedPoint V)) trivial p) ^ e := by
    rw [hτ,hp]
    exact hfactor
  obtain ⟨U,hxU,w,hw,hwhole⟩ := exists_whole_unit_factorization qA hbij τ p v e hlocal
  have hsU : SmoothOfRelativeDimension 1
      (U.1.ι ≫ g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E) := by
    exact (inferInstance : SmoothOfRelativeDimension (0+1)
      (U.1.ι ≫ (g ≫ SchemeNormalizedAuxiliaryParameter.parameterMap E)))
  refine ⟨A,j,g,qA,π,v,e,hA,hj,hg,hproj,hπ,haux,hres,he,hfactor,hord,U,hxU,w,hw,
    inferInstance,hsU,hwhole,?_⟩
  have hc : qA (closedPoint V) ∈ Set.range U.1.ι := ⟨⟨qA (closedPoint V),hxU⟩,rfl⟩
  exact ⟨SchemeOriginalAdaptedTrait.lift U.1.ι qA hc,
    SchemeOriginalAdaptedTrait.lift_projection U.1.ι qA hc⟩

end EnvelopeProperty.SchemeOriginalAuxiliaryUnitChart
