import EnvelopeProperty.AlgGeom.AffinePullbackChartGermReadback
import EnvelopeProperty.Char0.NativeFormalClosedFibrePoints
import EnvelopeProperty.Char0.NativeSNCCharts

/-! # Original fibre points in the actual coefficient tensor chart -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

namespace EnvelopeProperty.Char0.NativeFormalAffineChartPoints

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Okounkov BingWangEntropy
open AffinePullbackChartGermReadback ClosedFibreLocalRing
open scoped TensorProduct

section Generic

variable {R B S K : Type u} [CommRing R] [CommRing B] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K] {Y : Scheme.{u}}
  (π : Y ⟶ Spec (.of R)) (c : Spec (.of B) ⟶ Y)
  (q : Spec (.of K) ⟶ Spec (.of B))
  (hq : q ≫ (c ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- The original geometric residue triangle gives the original chart point its actual R-action. -/
def chartResiduePoint :
    letI := chartCoefficientAlgebra π c
    B →ₐ[R] K := by
  letI := chartCoefficientAlgebra π c
  exact { (Spec.preimage q).hom with
    commutes' r := by
      have he := congrArg Spec.preimage hq
      rw [Spec.preimage_comp, Spec.preimage_map] at he
      exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom he) r }

/-- The literal original chart evaluation is retained on every original coefficient. -/
theorem chartResiduePoint_apply (b : B) :
    chartResiduePoint π c q hq b = (Spec.preimage q).hom b := rfl

variable (β : S →ₐ[R] K)

/-- The actual field-valued point of the original tensor chart, from the literal tensor point map. -/
def tensorPoint :
    letI := chartCoefficientAlgebra π c
    Spec (.of K) ⟶ Spec (.of (B ⊗[R] S)) := by
  letI := chartCoefficientAlgebra π c
  exact Spec.map (CommRingCat.ofHom
    (pointTensorMap β (chartResiduePoint π c q hq)).toRingHom)

/-- The whole actual tensor coefficient map is the original point tensor map. -/
theorem tensorPoint_preimage :
    letI := chartCoefficientAlgebra π c
    (Spec.preimage (tensorPoint π c q hq β)).hom =
      (pointTensorMap β (chartResiduePoint π c q hq)).toRingHom := by
  let := chartCoefficientAlgebra π c
  exact congrArg CommRingCat.Hom.hom (Spec.preimage_map _)

/-- Every original pure tensor keeps its literal original coefficient value. -/
theorem tensorPoint_tmul (b : B) (s : S) :
    letI := chartCoefficientAlgebra π c
    (Spec.preimage (tensorPoint π c q hq β)).hom (b ⊗ₜ[R] s) =
      (Spec.preimage q).hom b * β s := by
  let := chartCoefficientAlgebra π c
  rw [tensorPoint_preimage]
  rfl

/-- The original affine-point morphism is precisely the first tensor projection. -/
theorem tensorPoint_left :
    letI := chartCoefficientAlgebra π c
    tensorPoint π c q hq β ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S)) = q := by
  let := chartCoefficientAlgebra π c
  have he : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] S) ≫
      CommRingCat.ofHom (pointTensorMap β (chartResiduePoint π c q hq)).toRingHom =
      Spec.preimage q := by
    ext b
    exact pointTensorMap_includeLeft β (chartResiduePoint π c q hq) b
  change Spec.map _ ≫ Spec.map _ = q
  rw [← Spec.map_comp, he, Spec.map_preimage]

/-- Every original base coefficient is retained by the actual second tensor projection. -/
theorem tensorPoint_right :
    letI := chartCoefficientAlgebra π c
    tensorPoint π c q hq β ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[R] B ⊗[R] S)) =
      Spec.map (CommRingCat.ofHom β.toRingHom) := by
  let := chartCoefficientAlgebra π c
  have he : CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[R] B ⊗[R] S) ≫
      CommRingCat.ofHom (pointTensorMap β (chartResiduePoint π c q hq)).toRingHom =
      CommRingCat.ofHom β.toRingHom := by
    ext s
    change chartResiduePoint π c q hq 1 * β s = β s
    rw [map_one, one_mul]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, he]

/-- The actual categorical first projection is the whole original chart point. -/
theorem tensorPoint_chart_fst :
    letI := chartCoefficientAlgebra π c
    (tensorPoint π c q hq β ≫ tensorChartMap (S := S) π c) ≫
      pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap R S))) = q ≫ c := by
  let := chartCoefficientAlgebra π c
  rw [Category.assoc, tensorChartMap_fst, ← Category.assoc, tensorPoint_left]

/-- The actual categorical second projection is the SAME whole original residue map. -/
theorem tensorPoint_chart_snd :
    letI := chartCoefficientAlgebra π c
    (tensorPoint π c q hq β ≫ tensorChartMap (S := S) π c) ≫
      pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom β.toRingHom) := by
  let := chartCoefficientAlgebra π c
  rw [Category.assoc, tensorChartMap_snd, tensorPoint_right]

/-- The actual tensor-chart prime is the kernel of the ENTIRE original tensor point map. -/
theorem tensorPoint_prime :
    letI := chartCoefficientAlgebra π c
    ((tensorPoint π c q hq β) (IsLocalRing.closedPoint K)).asIdeal =
      RingHom.ker (pointTensorMap β (chartResiduePoint π c q hq)).toRingHom := by
  let := chartCoefficientAlgebra π c
  rw [Subsingleton.elim (IsLocalRing.closedPoint K) (⊥ : PrimeSpectrum K)]
  rfl

end Generic

section Native

variable {R B : Type} [CommRing R] [CommRing B]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (m : ℕ) [SmoothOfRelativeDimension m f]
  [IsSeparated f] [QuasiCompact f] (x : SchemeComplexPoint f)
  {Y : Scheme} (π : Y ⟶ Spec (.of R)) (c : Spec (.of B) ⟶ Y)

/-- The base action is the actual original Taylor map at the SAME original base point. -/
@[instance_reducible] def baseTaylorAlgebra : Algebra R (MvPowerSeries (Fin m) ℂ) :=
  (schemeAffineNativeFormal f m x).toAlgebra

/-- The original base residue action is the actual original point evaluation. -/
@[instance_reducible] def baseResidueAlgebra : Algebra R ℂ :=
  (schemeAffineOriginalPoint f x).toAlgebra

/-- The literal constant coefficient is compatible with the actual original Taylor action. -/
def formalResidue :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := baseResidueAlgebra f x
    MvPowerSeries (Fin m) ℂ →ₐ[R] ℂ := by
  letI := baseTaylorAlgebra f m x
  letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  letI := baseResidueAlgebra f x
  exact { MvPowerSeries.constantCoeff with
    commutes' r := schemeAffineNativeFormal_constantCoeff f m x r }

variable (p : SchemeComplexPoint (π ≫ f))
  (hp : schemeComplexPointMap (π ≫ f) f π rfl p = x)
  (q : Spec (.of ℂ) ⟶ Spec (.of B)) (hq : q ≫ c = p.val)

include hp hq

omit [IsSeparated f] [QuasiCompact f] in
/-- The actual original chart factorization internally gives the entire original base triangle. -/
theorem chartPoint_baseTriangle :
    letI := baseResidueAlgebra f x
    q ≫ (c ≫ π) = Spec.map (CommRingCat.ofHom (algebraMap R ℂ)) := by
  let := baseResidueAlgebra f x
  have he : p.val ≫ π = x.val := congrArg Subtype.val hp
  rw [← Category.assoc, hq, he]
  exact (Spec.map_preimage x.val).symm

/-- The canonical tensor-chart lift uses the actual chart point and EVERY actual formal coefficient. -/
def formalTensorPoint :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π c
    Spec (.of ℂ) ⟶ Spec (.of (B ⊗[R] MvPowerSeries (Fin m) ℂ)) := by
  letI := baseTaylorAlgebra f m x
  letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  letI := baseResidueAlgebra f x
  exact tensorPoint π c q (chartPoint_baseTriangle f x π c p hp q hq)
    (formalResidue f m x)

/-- The manufactured actual tensor-chart point is exactly the original formal closed-fibre lift. -/
theorem formalTensorPoint_chart :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π c
    formalTensorPoint f m x π c p hp q hq ≫
      tensorChartMap (S := MvPowerSeries (Fin m) ℂ) π c =
        NativeFormalClosedFibrePoints.pointLift f m x π p hp := by
  let := baseTaylorAlgebra f m x
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let := baseResidueAlgebra f x
  apply pullback.hom_ext
  · exact (tensorPoint_chart_fst π c q (chartPoint_baseTriangle f x π c p hp q hq)
      (formalResidue f m x)).trans
        (hq.trans (NativeFormalClosedFibrePoints.pointLift_fst f m x π p hp).symm)
  · exact (tensorPoint_chart_snd π c q (chartPoint_baseTriangle f x π c p hp q hq)
      (formalResidue f m x)).trans
        (NativeFormalClosedFibrePoints.pointLift_snd f m x π p hp).symm

/-- The actual underlying tensor-chart point maps to the SAME original formal closed-fibre point. -/
theorem formalTensorPoint_chart_apply :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π c
    tensorChartMap (S := MvPowerSeries (Fin m) ℂ) π c
      (formalTensorPoint f m x π c p hp q hq (IsLocalRing.closedPoint ℂ)) =
        NativeFormalClosedFibrePoints.pointLift f m x π p hp (IsLocalRing.closedPoint ℂ) := by
  let := baseTaylorAlgebra f m x
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  exact congrArg (fun k => k (IsLocalRing.closedPoint ℂ))
    (formalTensorPoint_chart f m x π c p hp q hq)

/-- Every actual formal tensor coefficient has the literal original value. -/
theorem formalTensorPoint_tmul (b : B) (s : MvPowerSeries (Fin m) ℂ) :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π c
    (Spec.preimage (formalTensorPoint f m x π c p hp q hq)).hom (b ⊗ₜ[R] s) =
      (Spec.preimage q).hom b * MvPowerSeries.constantCoeff s := by
  let := baseTaylorAlgebra f m x
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let := baseResidueAlgebra f x
  exact tensorPoint_tmul π c q (chartPoint_baseTriangle f x π c p hp q hq)
    (formalResidue f m x) b s

/-- The actual prime uses the whole original chart point and literal constant coefficient. -/
theorem formalTensorPoint_prime :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := baseResidueAlgebra f x
    letI := chartCoefficientAlgebra π c
    (formalTensorPoint f m x π c p hp q hq (IsLocalRing.closedPoint ℂ)).asIdeal =
      RingHom.ker (pointTensorMap (formalResidue f m x)
        (chartResiduePoint π c q (chartPoint_baseTriangle f x π c p hp q hq))).toRingHom := by
  let := baseTaylorAlgebra f m x
  let : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
  let := baseResidueAlgebra f x
  exact tensorPoint_prime π c q (chartPoint_baseTriangle f x π c p hp q hq)
    (formalResidue f m x)

end Native

section AffineCoefficients

variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
  (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens)

/-- The actual original affine-open coefficient action is exactly the original section-map action. -/
theorem affineOpenCoefficientAlgebra_eq :
    chartCoefficientAlgebra π U.2.fromSpec = (sectionsHom π U.1).toAlgebra := by
  apply Algebra.algebra_ext
  intro r
  change (Spec.preimage (U.2.fromSpec ≫ π)).hom r = sectionsHom π U.1 r
  rw [fromSpec_comp_eq_specMap_sectionsHom, Spec.preimage_map]
  rfl

end AffineCoefficients

section AffineOpen

variable {R : Type} [CommRing R]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (m : ℕ) [SmoothOfRelativeDimension m f]
  [IsSeparated f] [QuasiCompact f] (x : SchemeComplexPoint f)
  {Y : Scheme} (π : Y ⟶ Spec (.of R)) (p : SchemeComplexPoint (π ≫ f))
  (hp : schemeComplexPointMap (π ≫ f) f π rfl p = x)
  (U : Y.affineOpens) (hpU : schemeComplexPointImage (π ≫ f) p ∈ U.1)

/-- Every original affine open containing the original point manufactures its actual tensor-chart lift. -/
def affineOpenTensorPoint :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π U.2.fromSpec
    Spec (.of ℂ) ⟶ Spec (.of (Γ(Y, U.1) ⊗[R] MvPowerSeries (Fin m) ℂ)) :=
  formalTensorPoint f m x π U.2.fromSpec p hp
    (NativeSNCCharts.affineLift (π ≫ f) p U hpU).val
    (NativeSNCCharts.affineLift_fac (π ≫ f) p U hpU)

/-- Its actual categorical chart composite is exactly the SAME original formal closed-fibre point. -/
theorem affineOpenTensorPoint_chart :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π U.2.fromSpec
    affineOpenTensorPoint f m x π p hp U hpU ≫
      tensorChartMap (S := MvPowerSeries (Fin m) ℂ) π U.2.fromSpec =
        NativeFormalClosedFibrePoints.pointLift f m x π p hp :=
  formalTensorPoint_chart f m x π U.2.fromSpec p hp
    (NativeSNCCharts.affineLift (π ≫ f) p U hpU).val
    (NativeSNCCharts.affineLift_fac (π ≫ f) p U hpU)

/-- The canonical original affine-open lift supplies the actual tensor-chart point over the original one. -/
theorem affineOpenTensorPoint_chart_apply :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π U.2.fromSpec
    tensorChartMap (S := MvPowerSeries (Fin m) ℂ) π U.2.fromSpec
      (affineOpenTensorPoint f m x π p hp U hpU (IsLocalRing.closedPoint ℂ)) =
        NativeFormalClosedFibrePoints.pointLift f m x π p hp (IsLocalRing.closedPoint ℂ) :=
  formalTensorPoint_chart_apply f m x π U.2.fromSpec p hp
    (NativeSNCCharts.affineLift (π ≫ f) p U hpU).val
    (NativeSNCCharts.affineLift_fac (π ≫ f) p U hpU)

/-- Every whole original section and every formal base series retain their literal coefficient values. -/
theorem affineOpenTensorPoint_tmul (b : Γ(Y, U.1)) (s : MvPowerSeries (Fin m) ℂ) :
    letI := baseTaylorAlgebra f m x
    letI : Module R (MvPowerSeries (Fin m) ℂ) := Algebra.toModule
    letI := chartCoefficientAlgebra π U.2.fromSpec
    (Spec.preimage (affineOpenTensorPoint f m x π p hp U hpU)).hom (b ⊗ₜ[R] s) =
      (Spec.preimage (NativeSNCCharts.affineLift (π ≫ f) p U hpU).val).hom b *
        MvPowerSeries.constantCoeff s :=
  formalTensorPoint_tmul f m x π U.2.fromSpec p hp
    (NativeSNCCharts.affineLift (π ≫ f) p U hpU).val
    (NativeSNCCharts.affineLift_fac (π ≫ f) p U hpU) b s

end AffineOpen

end EnvelopeProperty.Char0.NativeFormalAffineChartPoints
