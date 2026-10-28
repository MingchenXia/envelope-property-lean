import EnvelopeProperty.Global.NativeModelGrading
import EnvelopeProperty.Global.ModelCharts
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import DeJongAlterations.Geometry.ProjIntegral

/-! # The actual native scheme of an original rank-one model

All rings and coordinates below are the original model's literal rings
and coordinates. Higher-rank total-degree Proj is not used as a model.
-/
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

/-- The actual original rank-one algebra's native projective scheme. -/
def nativeRankOneScheme : Scheme.{u} := Proj X.nativeTotalGrading

/-- The actual original coefficient homomorphism into degree zero. -/
def nativeRankOneCoefficients : k →+* X.nativeTotalGrading 0 where
  toFun a := ⟨algebraMap k X.S a, by
    change (algebraMap k (MvPolynomial (Fin 1) K) a).IsHomogeneous 0
    rw [MvPolynomial.algebraMap_apply]
    exact MvPolynomial.isHomogeneous_C _ _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The structure map uses the SAME original coefficient field and inclusion. -/
def nativeRankOneStructure : X.nativeRankOneScheme ⟶ Spec (.of k) :=
  Proj.toSpecZero X.nativeTotalGrading ≫ Spec.map (CommRingCat.ofHom X.nativeRankOneCoefficients)

/-- Every SAME original coordinate lies in the actual degree-one piece. -/
theorem nativeRankOneCoordinate_mem (i : Fin (X.M 0 + 1)) :
    X.coordElem ⟨0, i⟩ ∈ X.nativeTotalGrading 1 := by
  change (X.coordElem ⟨0, i⟩ : MvPolynomial (Fin 1) K).IsHomogeneous 1
  rw [X.coe_coordElem]
  exact MvPolynomial.isHomogeneous_monomial _ (by simp)

/-- The native homogeneous localization at the SAME original coordinate. -/
abbrev nativeRankOneChartRing (i : Fin (X.M 0 + 1)) :=
  HomogeneousLocalization.Away X.nativeTotalGrading (X.coordElem ⟨0, i⟩)

/-- The actual basic open of the SAME original coordinate. -/
def nativeRankOneCoordinateOpen (i : Fin (X.M 0 + 1)) : X.nativeRankOneScheme.Opens :=
  ProjectiveSpectrum.basicOpen X.nativeTotalGrading (X.coordElem ⟨0, i⟩)

/-- The actual native Proj chart is the spectrum of its actual homogeneous localization. -/
def nativeRankOneHomogeneousChartIso (i : Fin (X.M 0 + 1)) :
    (X.nativeRankOneCoordinateOpen i).toScheme ≅
      Spec (.of (X.nativeRankOneChartRing i)) :=
  Proj.basicOpenIsoSpec X.nativeTotalGrading (X.coordElem ⟨0, i⟩)
    (X.nativeRankOneCoordinate_mem i) (by decide : 0 < (1 : ℕ))

/-- Every actual original coordinate open is genuinely affine. -/
theorem nativeRankOneCoordinateOpen_isAffine (i : Fin (X.M 0 + 1)) :
    IsAffineOpen (X.nativeRankOneCoordinateOpen i) :=
  IsAffine.of_isIso (X.nativeRankOneHomogeneousChartIso i).hom

/-- An original nonzero coordinate is a literal nonzero element of the original algebra. -/
theorem nativeRankOneCoordinate_ne_zero (i : Fin (X.M 0 + 1))
    (hi : X.coord 0 i ≠ 0) : X.coordElem ⟨0, i⟩ ≠ 0 := by
  intro h
  have hv := congrArg (fun p : X.S => (p : MvPolynomial (Fin 1) K)) h
  exact hi (MvPolynomial.monomial_eq_zero.mp hv)

/-- The actual native irrelevant ideal is nonzero by the original coordinate axiom. -/
theorem nativeRankOne_irrelevant_ne_bot :
    HomogeneousIdeal.irrelevant X.nativeTotalGrading ≠ ⊥ := by
  obtain ⟨i, hi⟩ := X.exists_coord_ne_zero 0
  intro h
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem X.nativeTotalGrading
    (by decide : 0 < (1 : ℕ)) (X.nativeRankOneCoordinate_mem i)
  rw [h] at hm
  exact X.nativeRankOneCoordinate_ne_zero i hi hm

/-- The SAME original rank-one algebra defines a genuine integral native projective scheme. -/
instance nativeRankOneScheme_isIntegral : IsIntegral X.nativeRankOneScheme :=
  DeJongAlterations.Geometry.ProjIntegral.isIntegral_proj _ X.nativeRankOne_irrelevant_ne_bot

end EnvelopeProperty.MultiModel
