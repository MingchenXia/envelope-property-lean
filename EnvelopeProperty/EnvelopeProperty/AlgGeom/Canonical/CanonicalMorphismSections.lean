import EnvelopeProperty.AlgGeom.Canonical.ExteriorCotangentMorphism
import EnvelopeProperty.Char0.CanonicalRelativeDeterminant

/-!
# Original section coefficients of the actual canonical morphism

The actual scheme structure-ring map and cotangent component agree with
ordinary relative differentials of these same section algebras.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)

/-- The literal regular-function map of the original morphism, as an algebra
homomorphism for the actual structural section algebras. -/
def schemeMorphismSectionAlgebraHom (U : X.Opens) :
    letI := cotangentOpenAlgebra f U
    letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
    Γ(X, U) →ₐ[K] Γ(Y, g ⁻¹ᵁ U) := by
  letI := cotangentOpenAlgebra f U
  letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
  refine { toRingHom := (g.app U).hom, commutes' := ?_ }
  intro a
  exact congr($(schemeMorphism_constantSquare f g U).hom a)

/-- The actual raw cotangent component equals the ordinary Kähler map on
all original section differentials, not just chosen coordinate vectors. -/
theorem cotangentMorphismSemilinear_eq_kaehlerMap (U : X.Opens)
    (m : letI := cotangentOpenAlgebra f U; KaehlerDifferential K Γ(X, U)) :
    letI := cotangentOpenAlgebra f U
    letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
    letI := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
    letI : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun a ↦
        ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
    cotangentMorphismSemilinear f g (.op U) m =
      KaehlerDifferential.map K K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) m := by
  let := cotangentOpenAlgebra f U
  let := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
  let := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
  let : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
  let L : KaehlerDifferential K Γ(X, U) →ₗ[Γ(X, U)]
      KaehlerDifferential K Γ(Y, g ⁻¹ᵁ U) :=
    { toFun := cotangentMorphismSemilinear f g (.op U)
      map_add' := (cotangentMorphismSemilinear f g (.op U)).map_add
      map_smul' := (cotangentMorphismSemilinear f g (.op U)).map_smulₛₗ }
  have h : L = KaehlerDifferential.map K K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation K Γ(X, U))
    rintro _ ⟨a, rfl⟩
    exact (cotangentPresheafMorphism_d f g U a).trans
      (KaehlerDifferential.map_D K K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) a).symm
  exact LinearMap.congr_fun h m

/-- Actual linear scalar extension of the genuine raw exterior component
on the original section rings. -/
def exteriorCotangentMorphismBaseChange (U : X.Opens) (n : ℕ) :
    letI := cotangentOpenAlgebra f U
    letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
    letI := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
    letI : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun a ↦
        ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
    Γ(Y, g ⁻¹ᵁ U) ⊗[Γ(X, U)] (⋀[Γ(X, U)]^n (KaehlerDifferential K Γ(X, U))) →ₗ[
      Γ(Y, g ⁻¹ᵁ U)] (⋀[Γ(Y, g ⁻¹ᵁ U)]^n (KaehlerDifferential K Γ(Y, g ⁻¹ᵁ U))) := by
  letI := cotangentOpenAlgebra f U
  letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
  letI := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
  letI : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
  let L : (⋀[Γ(X, U)]^n (KaehlerDifferential K Γ(X, U))) →ₗ[Γ(X, U)]
      (⋀[Γ(Y, g ⁻¹ᵁ U)]^n (KaehlerDifferential K Γ(Y, g ⁻¹ᵁ U))) :=
    (exteriorCotangentMorphismComponent f g n (.op U)).hom
  exact L.liftBaseChange Γ(Y, g ⁻¹ᵁ U)

/-- The ENTIRE original section map agrees with the genuine canonical
Kähler differential map for the SAME actual section algebra homomorphism. -/
theorem exteriorCotangentMorphismBaseChange_eq_affineCanonicalDifferentialMap
    (U : X.Opens) (n : ℕ) :
    letI := cotangentOpenAlgebra f U
    letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
    letI := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
    letI : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun a ↦
        ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
    exteriorCotangentMorphismBaseChange f g U n =
      EnvelopeProperty.Char0.affineCanonicalDifferentialMap
        (k := K) (R := Γ(X, U)) (A := Γ(Y, g ⁻¹ᵁ U)) n := by
  let := cotangentOpenAlgebra f U
  let := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
  let := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
  let : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
  apply TensorProduct.AlgebraTensorModule.ext
  intro a z
  let F := TensorProduct.AlgebraTensorModule.curry
    (exteriorCotangentMorphismBaseChange f g U n) a
  let G := TensorProduct.AlgebraTensorModule.curry
    (EnvelopeProperty.Char0.affineCanonicalDifferentialMap
      (k := K) (R := Γ(X, U)) (A := Γ(Y, g ⁻¹ᵁ U)) n) a
  have hFG : F = G := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span Γ(X, U) n (KaehlerDifferential K Γ(X, U)))
    rintro _ ⟨m, rfl⟩
    change exteriorCotangentMorphismBaseChange f g U n
      (a ⊗ₜ[Γ(X, U)] exteriorPower.ιMulti Γ(X, U) n m) = _
    rw [exteriorCotangentMorphismBaseChange, LinearMap.liftBaseChange_tmul]
    refine (congrArg
      (fun z : ⋀[Γ(Y, g ⁻¹ᵁ U)]^n (KaehlerDifferential K Γ(Y, g ⁻¹ᵁ U)) ↦ a • z)
        (exteriorCotangentMorphismComponent_wedge f g n (.op U) m)).trans ?_
    refine Eq.trans ?_
      (EnvelopeProperty.Char0.affineCanonicalDifferentialMap_tmul_wedge
        (k := K) (R := Γ(X, U)) (A := Γ(Y, g ⁻¹ᵁ U)) n a m).symm
    apply congrArg (fun v : Fin n → KaehlerDifferential K Γ(Y, g ⁻¹ᵁ U) ↦
      a • exteriorPower.ιMulti Γ(Y, g ⁻¹ᵁ U) n v)
    funext j
    exact cotangentMorphismSemilinear_eq_kaehlerMap f g U (m j)
  exact LinearMap.congr_fun hFG z

/-- The full original section image is the intrinsic all-original-functions
canonical differential image, without a prescribed image hypothesis. -/
theorem range_exteriorCotangentMorphismBaseChange (U : X.Opens) (n : ℕ) :
    letI := cotangentOpenAlgebra f U
    letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
    letI := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
    letI : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun a ↦
        ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
    LinearMap.range (exteriorCotangentMorphismBaseChange f g U n) =
      EnvelopeProperty.Char0.affineCanonicalDifferentialImage
        (k := K) (R := Γ(X, U)) (A := Γ(Y, g ⁻¹ᵁ U)) n := by
  let := cotangentOpenAlgebra f U
  let := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
  let := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
  let : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
  rw [exteriorCotangentMorphismBaseChange_eq_affineCanonicalDifferentialMap]
  exact EnvelopeProperty.Char0.range_affineCanonicalDifferentialMap n

/-- In genuine source/target bases, the original actual section map has
exactly the genuine relative differential determinant as its coefficient. -/
theorem exteriorCotangentMorphismBaseChange_volumeCoefficient (U : X.Opens) {n : ℕ}
    (bX : letI := cotangentOpenAlgebra f U
      Module.Basis (Fin n) Γ(X, U) (KaehlerDifferential K Γ(X, U)))
    (bY : letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
      Module.Basis (Fin n) Γ(Y, g ⁻¹ᵁ U) (KaehlerDifferential K Γ(Y, g ⁻¹ᵁ U))) :
    letI := cotangentOpenAlgebra f U
    letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
    letI := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
    letI : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun a ↦
        ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
    EnvelopeProperty.Char0.differentialVolumeCoordinate bY
      (exteriorCotangentMorphismBaseChange f g U n
        ((1 : Γ(Y, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U)]
          EnvelopeProperty.Char0.differentialVolumeForm bX)) =
      EnvelopeProperty.Char0.relativeDifferentialDet bX bY := by
  let := cotangentOpenAlgebra f U
  let := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ U)
  let := (schemeMorphismSectionAlgebraHom f g U).toAlgebra
  let : IsScalarTower K Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((schemeMorphismSectionAlgebraHom f g U).commutes a).symm
  rw [exteriorCotangentMorphismBaseChange_eq_affineCanonicalDifferentialMap]
  exact EnvelopeProperty.Char0.differentialVolumeCoordinate_affineCanonicalDifferentialMap_volumeForm bX bY

end
end EnvelopeProperty.CanonicalGeometry
