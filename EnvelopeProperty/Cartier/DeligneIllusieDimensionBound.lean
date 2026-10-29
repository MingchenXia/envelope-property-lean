import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionDifferential
import EnvelopeProperty.AlgGeom.Canonical.CotangentSmoothLocallyFree
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverDetection
import EnvelopeProperty.Cartier.SchemeRelativeFrobeniusBasisDifferential
import EnvelopeProperty.Cartier.DeligneIllusieCechGoodTruncation
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Deligne Illusie Dimension Bound

Actual smooth dimension bounds for the original geometric exterior sheaves. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u

namespace EnvelopeProperty.Cartier.DeligneIllusieDimensionBound

private theorem exterior_subsingleton {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] {n q : ℕ}
    (b : Module.Basis (Fin n) R M) (hq : n < q) : Subsingleton (⋀[R]^q M) := by
  classical
  let : IsEmpty (Set.powersetCard (Fin n) q) := ⟨fun s => by
    have hc := Finset.card_le_univ s.val
    have hs : s.val.card = q := s.property
    simp only [Fintype.card_fin] at hc
    omega⟩
  refine ⟨fun x y => (b.exteriorPower q).repr.injective ?_⟩
  ext s
  exact isEmptyElim s

private theorem affine_forms_isZero (k : Type u) [Field k]
    (A : CommRingCat.{u}) [Algebra k A] (n q : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k A] (hq : n < q) :
    IsZero (CanonicalGeometry.exteriorCotangentSheaf
      (CanonicalGeometry.affineStructuralMap k A) q) := by
  let b := CanonicalGeometry.standardSmoothDifferentialBasis k A n
  have hM : IsZero (CanonicalGeometry.affineExteriorCotangentModule k A q) :=
    ModuleCat.isZero_iff_subsingleton.mpr (exterior_subsingleton b hq)
  exact ((tilde.functor A).map_isZero hM).of_iso
    (CanonicalGeometry.affineExteriorCotangentSheafIso k A b q)

private theorem chart_forms_isZero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {V : X.Opens} (hV : IsAffineOpen V) (n q : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((CanonicalGeometry.schemeConstantPresheafMap f).app (op V)).hom)
    (hq : n < q) :
    IsZero ((Scheme.Modules.restrictFunctor hV.fromSpec).obj
      (CanonicalGeometry.exteriorCotangentSheaf f q)) := by
  let A : CommRingCat.{u} := Γ(X, V)
  let φ : CommRingCat.of k ⟶ A := (CanonicalGeometry.schemeConstantPresheafMap f).app (op V)
  let : Algebra k A := φ.hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n k A := hs
  have he : hV.fromSpec ≫ f = CanonicalGeometry.affineStructuralMap k A :=
    CanonicalGeometry.affineChartStructuralMap f hV
  let e := CanonicalGeometry.exteriorCotangentSheafOpenImmersionIso f hV.fromSpec q ≪≫
    eqToIso (congrArg (fun g => CanonicalGeometry.exteriorCotangentSheaf g q) he)
  exact (affine_forms_isZero k A n q hq).of_iso e

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Actual original smooth exterior sheaves vanish above their actual relative dimension.
The free affine bases and the point cover are produced internally from smoothness. -/
theorem exteriorCotangentSheaf_isZero (q : ℕ) (hq : n < q) :
    IsZero (CanonicalGeometry.exteriorCotangentSheaf f q) := by
  let V (x : X) := (CanonicalGeometry.smoothCotangentChart f n x).val
  let hV (x : X) : IsAffineOpen (V x) :=
    (CanonicalGeometry.smoothCotangentChart f n x).property.1
  let Y (x : X) : Scheme.{u} := Spec Γ(X, V x)
  let j (x : X) : Y x ⟶ X := (hV x).fromSpec
  have hcover : ∀ x : X, ∃ (i : X) (y : Y i), j i y = x := by
    intro x
    obtain ⟨y, hy⟩ : x ∈ Set.range (j x) := by
      change x ∈ Set.range (hV x).fromSpec
      rw [(hV x).range_fromSpec]
      exact (CanonicalGeometry.smoothCotangentChart f n x).property.2.1
    exact ⟨x, y, hy⟩
  apply (IsZero.iff_id_eq_zero _).mpr
  apply SchemeModuleOpenCoverDetection.hom_ext Y j hcover
  intro x
  have hz := chart_forms_isZero f (hV x) n q
    (CanonicalGeometry.smoothCotangentChart f n x).property.2.2 hq
  have hp : IsZero ((Scheme.Modules.pullback (j x)).obj
      (CanonicalGeometry.exteriorCotangentSheaf f q)) :=
    hz.of_iso (((Scheme.Modules.restrictFunctorIsoPullback (j x)).app
      (CanonicalGeometry.exteriorCotangentSheaf f q)).symm)
  exact ((Scheme.Modules.pullback (j x)).map_id _).trans
    (((IsZero.iff_id_eq_zero _).mp hp).trans
      ((Scheme.Modules.pullback (j x)).map_zero _ _).symm)

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The original coefficient structural map of the ACTUAL geometric Frobenius pullback. -/
def twistStructure : SchemeRelativeFrobenius.twist p f ⟶ Spec (.of k) :=
  pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)

/-- Actual base change preserves the same smooth relative dimension, even over imperfect k. -/
theorem twistStructure_smooth : SmoothOfRelativeDimension n (twistStructure f p) := by
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback f (SchemeRelativeFrobenius.baseMap (k := k) p)) inferInstance

/-- Original exterior forms on the TRUE geometric twist vanish above the original dimension. -/
theorem twist_exteriorCotangentSheaf_isZero (q : ℕ) (hq : n < q) :
    IsZero (CanonicalGeometry.exteriorCotangentSheaf (twistStructure f p) q) := by
  let := twistStructure_smooth f n p
  exact exteriorCotangentSheaf_isZero (twistStructure f p) n q hq

/-- The actual pushed exterior form module, retaining its original twist-coefficient action, is zero. -/
theorem formModule_isZero (q : ℕ) (hq : n < q) :
    IsZero (SchemeRelativeFrobeniusDeRham.formModule f p q) :=
  (Scheme.Modules.pushforward (SchemeRelativeFrobenius.map p f)).map_isZero
    (exteriorCotangentSheaf_isZero f n q hq)

local notation "E" => SchemeRelativeFrobeniusBasisDifferential.complex f p n

/-- The extension of the SAME original globally constructed complex has actual zero terms above n. -/
theorem complex_extend_isStrictlyLE :
    CochainComplex.IsStrictlyLE ((E).extend ComplexShape.embeddingUpNat) (n : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  cases i with
  | ofNat q =>
    have hq : n < q := Int.ofNat_lt.mp hi
    have hz : IsZero ((E).X q) := by
      change IsZero (SchemeRelativeFrobeniusDeRham.formModule f p q)
      exact formModule_isZero f n p q hq
    exact hz.of_iso ((E).extendXIso ComplexShape.embeddingUpNat (i := q) rfl)
  | negSucc q => omega

/-- The native inclusion from the original good truncation to the same extended complex. -/
def goodTruncationInclusion :
    DeligneIllusieCechGoodTruncation.goodTruncation E p ⟶ (E).extend ComplexShape.embeddingUpNat :=
  CochainComplex.ιTruncLE ((E).extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1)

/-- When the actual smooth dimension is below p, the ORIGINAL inclusion is an actual isomorphism. -/
theorem goodTruncationInclusion_isIso (hp : n < p) : IsIso (goodTruncationInclusion f n p) := by
  let : CochainComplex.IsStrictlyLE ((E).extend ComplexShape.embeddingUpNat) (n : ℤ) :=
    complex_extend_isStrictlyLE f n p
  let : CochainComplex.IsStrictlyLE ((E).extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1) :=
    CochainComplex.isStrictlyLE_of_le (K := (E).extend ComplexShape.embeddingUpNat)
      (n : ℤ) ((p : ℤ) - 1) (by omega)
  change IsIso (CochainComplex.ιTruncLE ((E).extend ComplexShape.embeddingUpNat) ((p : ℤ) - 1))
  infer_instance

/-- In particular, the same original good-truncation inclusion is a quasi-isomorphism. -/
theorem goodTruncationInclusion_quasiIso (hp : n < p) :
    QuasiIso (goodTruncationInclusion f n p) := by
  let := goodTruncationInclusion_isIso f n p hp
  infer_instance

end EnvelopeProperty.Cartier.DeligneIllusieDimensionBound
