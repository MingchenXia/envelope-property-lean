import EnvelopeProperty.Berkovich.LaurentGaussCoefficientNaturality
import EnvelopeProperty.Berkovich.SchemeResidueCompletion

/-! # Actual original completed-point coefficients and whole Laurent Gauss projections -/
open scoped Polynomial LaurentPolynomial NNReal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemePointLaurentGauss

variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (x : RelativeSchemeValuedPoint v f)

abbrev PointField := SchemeValuedPoint.H x.1

/-- The actual original field-valued point derives its entire coefficient map. -/
def coefficientMap : R →+* PointField f x :=
  (Scheme.Spec.preimage (SchemeValuedPoint.fieldPoint x.1 ≫ f)).unop.hom

/-- The WHOLE original coefficient triangle of the SAME completed point field. -/
theorem coefficientMap_spec : Spec.map (CommRingCat.ofHom (coefficientMap f x)) =
    SchemeValuedPoint.fieldPoint x.1 ≫ f := Scheme.Spec.map_preimage _

/-- Every original prescribed base value is retained in the actual point field. -/
theorem coefficientMap_val (a : R) :
    NormedField.valuation (K := PointField f x) (coefficientMap f x a) = v a := by
  have he : SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (coefficientMap f x)))
      (SchemeValuedPoint.basePoint (NormedField.valuation (K := PointField f x))) =
      SchemeValuedPoint.basePoint v := by
    rw [coefficientMap_spec, SchemeValuedPoint.map_comp,
      SchemeValuedPoint.map_norm_basePoint_fieldPoint]
    exact x.2
  have hv := congrArg (fun y => (SchemeValuedPoint.spectrumHomeomorph y).val a) he
  simpa only [SchemeValuedPoint.spectrumHomeomorph_map, SchemeValuedPoint.basePoint,
    Homeomorph.apply_symm_apply, Spectrum.comap_val_apply, Spectrum.ofValuation_val] using hv

/-- The genuine positive-radius Laurent Gauss point of the SAME original completed field. -/
def point (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint (Spec (.of (PointField f x)[T;T⁻¹])) :=
  SchemeValuedPoint.spectrumHomeomorph.symm
    (Spectrum.laurentGauss (NormedField.valuation (K := PointField f x)) r hr)

/-- The entire original projection through the original completed field point. -/
def originalProjection : Spec (.of (PointField f x)[T;T⁻¹]) ⟶ X :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PointField f x →+* (PointField f x)[T;T⁻¹])) ≫
    SchemeValuedPoint.fieldPoint x.1

/-- The entire actual Laurent coefficient projection retains the original parameter. -/
def parameterProjection : Spec (.of (PointField f x)[T;T⁻¹]) ⟶ Spec (.of R[T;T⁻¹]) :=
  Spec.map (CommRingCat.ofHom (Spectrum.laurentCoefficientHom (coefficientMap f x)))

/-- The WHOLE original Gauss projection to X recovers the SAME original native point. -/
theorem originalProjection_point (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (originalProjection f x) (point f x r hr) = x.1 := by
  have he : SchemeValuedPoint.map
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PointField f x →+* (PointField f x)[T;T⁻¹])))
      (point f x r hr) = SchemeValuedPoint.basePoint (NormedField.valuation (K := PointField f x)) := by
    apply SchemeValuedPoint.spectrumHomeomorph.injective
    rw [SchemeValuedPoint.spectrumHomeomorph_map]
    simp only [point, SchemeValuedPoint.basePoint, Homeomorph.apply_symm_apply]
    apply Spectrum.ext_val
    intro a
    exact Spectrum.laurentGauss_val_C _ r hr a
  rw [originalProjection, SchemeValuedPoint.map_comp, he]
  exact SchemeValuedPoint.map_norm_basePoint_fieldPoint x.1

/-- The whole original Laurent parameter point is the actual original base Gauss point. -/
theorem parameterProjection_point (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (parameterProjection f x) (point f x r hr) =
      SchemeValuedPoint.spectrumHomeomorph.symm (Spectrum.laurentGauss v r hr) := by
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  rw [parameterProjection, SchemeValuedPoint.spectrumHomeomorph_map]
  simp only [point, Homeomorph.apply_symm_apply]
  exact Spectrum.laurentGauss_comap_coefficients _ _ _ (coefficientMap_val f x) r hr

/-- The actual whole original ordinary polynomial parameter projection. -/
def ordinaryParameterProjection : Spec (.of (PointField f x)[T;T⁻¹]) ⟶ Spec (.of R[X]) :=
  parameterProjection f x ≫
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹]))

/-- The WHOLE ordinary parameter point is the actual original polynomial Gauss point. -/
theorem ordinaryParameterProjection_point (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (ordinaryParameterProjection f x) (point f x r hr) =
      SchemeValuedPoint.spectrumHomeomorph.symm (Spectrum.gauss (Spectrum.ofValuation v) r) := by
  rw [ordinaryParameterProjection, SchemeValuedPoint.map_comp, parameterProjection_point]
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map]
  simp only [Homeomorph.apply_symm_apply]
  apply Spectrum.ext_val
  intro p
  exact Spectrum.laurentGauss_val_toLaurent v r hr p

/-- The original Laurent completed-point spectrum with its actual original base structure. -/
abbrev sourceOver : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    ((LaurentPolynomial.C : PointField f x →+* (PointField f x)[T;T⁻¹]).comp (coefficientMap f x))))

/-- The entire original X projection retains its actual original base triangle. -/
def originalOverMap : sourceOver f x ⟶ Over.mk f :=
  Over.homMk (originalProjection f x) (by
    change (Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.C : PointField f x →+* (PointField f x)[T;T⁻¹])) ≫
        SchemeValuedPoint.fieldPoint x.1) ≫ f = _
    rw [Category.assoc, ← coefficientMap_spec, ← Spec.map_comp]
    rfl)

/-- The entire actual Laurent parameter projection retains the same base triangle. -/
def parameterOverMap : sourceOver f x ⟶ ProjBerk.nativeMultiplicativeGroup R :=
  Over.homMk (parameterProjection f x) (by
    change Spec.map (CommRingCat.ofHom (Spectrum.laurentCoefficientHom (coefficientMap f x))) ≫
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* R[T;T⁻¹])) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Spectrum.laurentCoefficientHom_C (coefficientMap f x) a)

/-- Actual Cartesian pairing gives the WHOLE original product family, not a supplied product map. -/
def productMap : sourceOver f x ⟶ Over.mk f ⊗ ProjBerk.nativeMultiplicativeGroup R :=
  lift (originalOverMap f x) (parameterOverMap f x)

@[reassoc (attr := simp)]
theorem productMap_fst : productMap f x ≫ fst (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R) =
    originalOverMap f x := lift_fst _ _

@[reassoc (attr := simp)]
theorem productMap_snd : productMap f x ≫ snd (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R) =
    parameterOverMap f x := lift_snd _ _

/-- The actual Laurent Gauss source point prescribes exactly the original base valuation. -/
def relativeSourcePoint (r : ℝ≥0) (hr : 0 < r) : RelativeSchemeValuedPoint v (sourceOver f x).hom :=
  ⟨point f x r hr, by
    change SchemeValuedPoint.map (sourceOver f x).hom (point f x r hr) = SchemeValuedPoint.basePoint v
    have hw := (originalOverMap f x).w
    change originalProjection f x ≫ f = (sourceOver f x).hom at hw
    rw [← hw, SchemeValuedPoint.map_comp, originalProjection_point]
    exact x.2⟩

/-- The genuine original Cartesian product valued point, with the entire actual base prescribed. -/
def productPoint (r : ℝ≥0) (hr : 0 < r) :
    RelativeSchemeValuedPoint v (Over.mk f ⊗ ProjBerk.nativeMultiplicativeGroup R).hom :=
  RelativeSchemeValuedPoint.map (productMap f x).left (productMap f x).w
    (relativeSourcePoint f x r hr)

/-- The whole original first projection of the constructed native product point equals x. -/
theorem productPoint_fst (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (fst (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R)).left
      (productPoint f x r hr).1 = x.1 := by
  change SchemeValuedPoint.map (fst (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R)).left
    (SchemeValuedPoint.map (productMap f x).left (point f x r hr)) = x.1
  rw [← SchemeValuedPoint.map_comp]
  have he := congrArg Over.Hom.left (productMap_fst f x)
  change (productMap f x).left ≫ (fst (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R)).left =
    originalProjection f x at he
  rw [he, originalProjection_point]

/-- The whole original second projection is exactly the actual Laurent Gauss parameter point. -/
theorem productPoint_snd (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (snd (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R)).left
      (productPoint f x r hr).1 =
        SchemeValuedPoint.spectrumHomeomorph.symm (Spectrum.laurentGauss v r hr) := by
  change SchemeValuedPoint.map (snd (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R)).left
    (SchemeValuedPoint.map (productMap f x).left (point f x r hr)) = _
  rw [← SchemeValuedPoint.map_comp]
  have he := congrArg Over.Hom.left (productMap_snd f x)
  change (productMap f x).left ≫ (snd (Over.mk f) (ProjBerk.nativeMultiplicativeGroup R)).left =
    parameterProjection f x at he
  rw [he]
  exact parameterProjection_point f x r hr

/-- Every actual original section Laurent expansion has its full weighted native-value maximum. -/
theorem section_laurent_value (U : X.Opens) (hx : x.1.point ∈ U)
    (r : ℝ≥0) (hr : 0 < r) (p : Γ(X, U)[T;T⁻¹]) :
    (Spectrum.laurentGauss (NormedField.valuation (K := PointField f x)) r hr).val
      (Spectrum.laurentCoefficientHom (SchemeValuedPoint.sectionToH x.1 U hx) p) =
        p.coeff.support.sup (fun i => SchemeValuedPoint.eval x.1 U hx (p.coeff i) * r ^ i) := by
  let w := (NormedField.valuation (K := PointField f x)).comap (SchemeValuedPoint.sectionToH x.1 U hx)
  have he := Spectrum.laurentGauss_coefficients_eq_sup
    (SchemeValuedPoint.sectionToH x.1 U hx) w (NormedField.valuation (K := PointField f x))
    (fun _ => rfl) r hr p
  refine he.trans ?_
  apply Finset.sup_congr rfl
  intro i _
  congr 1
  exact SchemeValuedPoint.nnnorm_sectionToH x.1 U hx (p.coeff i)

end EnvelopeProperty.Berkovich.SchemePointLaurentGauss
