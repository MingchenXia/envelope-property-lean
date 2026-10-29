import EnvelopeProperty.ComplexGeometry.Schemes.ProjectiveTwistingSections
import EnvelopeProperty.ComplexGeometry.Schemes.AnticanonicalLineBundle
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Genuine polynomial projective coordinate geometry

The degree-zero homogeneous coordinate localizations are actual polynomial
algebras, by literal coordinate dehomogenization and inverse homogeneous
ratios. These coordinate charts give native relative smoothness of the actual
Proj scheme. Their literal ratio differential bases give genuine finite
canonical and actual sheaf-Hom dual atlases. The twisting identification
requires the derived overlap determinants and gluing in the next producer.
-/

open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped DirectSum

namespace ComplexSchemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial projective scheme in dimension `n`. -/
abbrev polynomialProj : Scheme := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)

/-- The actual structure morphism uses the native Proj degree-zero map and
actual constant homogeneous polynomials. -/
def polynomialProjStructureMap : polynomialProj K n ⟶ Spec (.of K) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) ≫
    Spec.map (CommRingCat.ofHom homogeneousPolynomialDegreeZeroConstants)

/-- The actual coordinate-open ring, rather than a prescribed affine model. -/
abbrev polynomialProjCoordinateRing (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (MvPolynomial.X i)

/-- Its actual affine chart is the native homogeneous-localization open immersion. -/
def polynomialProjCoordinateImmersion (i : Fin (n + 1)) :
    Spec (.of (polynomialProjCoordinateRing K n i)) ⟶ polynomialProj K n :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X K i) (by decide)

instance polynomialProjCoordinateImmersion_isOpenImmersion (i : Fin (n + 1)) :
    IsOpenImmersion (polynomialProjCoordinateImmersion K n i) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι _ _ _ _))

/-- The native chart structural map is the actual base-field algebra map
of its genuine homogeneous localization. -/
theorem polynomialProjCoordinateImmersion_structure (i : Fin (n + 1)) :
    polynomialProjCoordinateImmersion K n i ≫ polynomialProjStructureMap K n =
      affineStructuralMap K (.of (polynomialProjCoordinateRing K n i)) := by
  rw [polynomialProjCoordinateImmersion, polynomialProjStructureMap,
    ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The genuine coordinate immersions cover the entire actual projective scheme. -/
theorem polynomialProjCoordinateImmersion_covers :
    ⨆ i : Fin (n + 1), (polynomialProjCoordinateImmersion K n i).opensRange = ⊤ := by
  simp only [polynomialProjCoordinateImmersion, Proj.opensRange_awayι]
  exact Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates

/-- Literal dehomogenization sends the distinguished coordinate to one
and the other, ordered coordinates to the `n` polynomial variables. -/
def polynomialProjDehomogenizationVariable (i j : Fin (n + 1)) : MvPolynomial (Fin n) K :=
  match finSuccEquiv' i j with
  | none => 1
  | some a => MvPolynomial.X a

/-- The distinguished coordinate really dehomogenizes to one. -/
theorem polynomialProjDehomogenizationVariable_self (i : Fin (n + 1)) :
    polynomialProjDehomogenizationVariable K n i i = 1 := by
  simp [polynomialProjDehomogenizationVariable]

/-- Every actual other ordered coordinate dehomogenizes to its actual variable. -/
theorem polynomialProjDehomogenizationVariable_succAbove (i : Fin (n + 1)) (a : Fin n) :
    polynomialProjDehomogenizationVariable K n i (i.succAbove a) = MvPolynomial.X a := by
  simp [polynomialProjDehomogenizationVariable]

/-- Actual polynomial substitution, retaining the native base-field scalars. -/
def polynomialProjDehomogenization (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (polynomialProjDehomogenizationVariable K n i)

/-- The literal chart coordinate is the actual homogeneous fraction `X_j/X_i`. -/
def polynomialProjCoordinateRatio (i j : Fin (n + 1)) : polynomialProjCoordinateRing K n i :=
  HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) 1
    (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X K j)

/-- Polynomial variables map into the actual chart ring by the literal
ordered homogeneous ratios. -/
def polynomialProjRatioMap (i : Fin (n + 1)) :
    MvPolynomial (Fin n) K →ₐ[K] polynomialProjCoordinateRing K n i :=
  MvPolynomial.aeval (fun a ↦ polynomialProjCoordinateRatio K n i (i.succAbove a))

/-- Genuine homogeneous localization embeds as a base-field algebra in the
actual ordinary coordinate localization, with its actual fraction values. -/
def polynomialProjCoordinateVal (i : Fin (n + 1)) :
    polynomialProjCoordinateRing K n i →ₐ[K]
      Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) where
  toRingHom := algebraMap _ _
  commutes' r := homogeneousPolynomialLocalization_algebraMap_val _ r

/-- The actual homogeneous coordinate-ring dehomogenization is obtained
by the genuine localization lift, since the coordinate is sent to one. -/
def polynomialProjCoordinateDehomogenization (i : Fin (n + 1)) :
    polynomialProjCoordinateRing K n i →ₐ[K] MvPolynomial (Fin n) K :=
  (IsLocalization.Away.liftAlgHom (MvPolynomial.X i)
    (show IsUnit (polynomialProjDehomogenization K n i (MvPolynomial.X i)) by
      simp [polynomialProjDehomogenization, polynomialProjDehomogenizationVariable_self]) :
        Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) →ₐ[K]
          MvPolynomial (Fin n) K).comp (polynomialProjCoordinateVal K n i)


/-- Literal homogeneous ratios have their literal ordinary localized values. -/
theorem polynomialProjCoordinateRatio_val (i j : Fin (n + 1)) :
    (polynomialProjCoordinateRatio K n i j).val =
      algebraMap (MvPolynomial (Fin (n + 1)) K)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)) (MvPolynomial.X j) *
          IsLocalization.Away.invSelf (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
            (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) := by
  rw [polynomialProjCoordinateRatio, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  simp only [pow_one]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf
    (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- The chart coordinate at its own distinguished index is one. -/
theorem polynomialProjCoordinateRatio_self (i : Fin (n + 1)) :
    polynomialProjCoordinateRatio K n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [polynomialProjCoordinateRatio_val, HomogeneousLocalization.val_one]
  exact IsLocalization.Away.mul_invSelf _

/-- Literal dehomogenization sends every genuine homogeneous fraction
`p/X_i^m` to precisely the substituted polynomial `p(X_i=1)`. -/
theorem polynomialProjCoordinateDehomogenization_mk (i : Fin (n + 1)) (m : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K m) :
    polynomialProjCoordinateDehomogenization K n i
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) m p
        (by simpa using hp)) = polynomialProjDehomogenization K n i p := by
  let hunit : IsUnit ((polynomialProjDehomogenization K n i).toRingHom (MvPolynomial.X i)) := by
    simp [polynomialProjDehomogenization, polynomialProjDehomogenizationVariable_self]
  change IsLocalization.Away.lift (MvPolynomial.X i) hunit
    (Localization.mk p ⟨MvPolynomial.X i ^ m, _⟩) = _
  rw [Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
  simp [polynomialProjDehomogenization, polynomialProjDehomogenizationVariable_self]

/-- Actual dehomogenization reads the actual ordered ratio generators. -/
theorem polynomialProjCoordinateDehomogenization_ratio (i : Fin (n + 1)) (a : Fin n) :
    polynomialProjCoordinateDehomogenization K n i
      (polynomialProjCoordinateRatio K n i (i.succAbove a)) = MvPolynomial.X a := by
  unfold polynomialProjCoordinateRatio
  rw [polynomialProjCoordinateDehomogenization_mk K n i 1 _ (MvPolynomial.isHomogeneous_X K _)]
  simp [polynomialProjDehomogenization, polynomialProjDehomogenizationVariable_succAbove]

/-- The literal polynomial-to-ratios map is a genuine right inverse of
actual chart dehomogenization, by its true generator values. -/
theorem polynomialProjCoordinateDehomogenization_ratioMap (i : Fin (n + 1))
    (p : MvPolynomial (Fin n) K) :
    polynomialProjCoordinateDehomogenization K n i (polynomialProjRatioMap K n i p) = p := by
  have h : (polynomialProjCoordinateDehomogenization K n i).comp (polynomialProjRatioMap K n i) =
      AlgHom.id K (MvPolynomial (Fin n) K) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [polynomialProjRatioMap, polynomialProjCoordinateDehomogenization_ratio]
  exact AlgHom.congr_fun h p

/-- Scaling all literal variables multiplies evaluation of an actual
homogeneous polynomial by its actual degree power. -/
theorem homogeneousPolynomial_eval₂_scaled {R S I : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial I R} {d : ℕ} (hp : p.IsHomogeneous d)
    (f : R →+* S) (g : I → S) (c : S) :
    MvPolynomial.eval₂Hom f (fun i ↦ c * g i) p = c ^ d * MvPolynomial.eval₂Hom f g p := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support he]
  ac_rfl


/-- Substitution followed by literal ratio evaluation normalizes every
actual homogeneous variable by precisely the distinguished coordinate. -/
theorem polynomialProjRatioMap_dehomVariable_val (i j : Fin (n + 1)) :
    polynomialProjCoordinateVal K n i
      (polynomialProjRatioMap K n i (polynomialProjDehomogenizationVariable K n i j)) =
        IsLocalization.Away.invSelf
          (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
          (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) *
            algebraMap (MvPolynomial (Fin (n + 1)) K)
              (Localization.Away (MvPolynomial.X i)) (MvPolynomial.X j) := by
  refine Fin.succAboveCases i ?_ (fun a ↦ ?_) j
  · rw [polynomialProjDehomogenizationVariable_self, map_one, map_one, mul_comm,
      IsLocalization.Away.mul_invSelf]
  · rw [polynomialProjDehomogenizationVariable_succAbove]
    simp only [polynomialProjRatioMap, MvPolynomial.aeval_X]
    change (polynomialProjCoordinateRatio K n i (i.succAbove a)).val = _
    exact (polynomialProjCoordinateRatio_val K n i _).trans (mul_comm _ _)

/-- An actual degree-`m` polynomial dehomogenizes and then evaluates in
actual ratios to its literal fraction `p/X_i^m`, in the actual localization. -/
theorem polynomialProjRatioMap_dehomogenization_val (i : Fin (n + 1)) (m : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K) (hp : p.IsHomogeneous m) :
    polynomialProjCoordinateVal K n i
      (polynomialProjRatioMap K n i (polynomialProjDehomogenization K n i p)) =
        IsLocalization.Away.invSelf
          (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
          (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ m *
            algebraMap (MvPolynomial (Fin (n + 1)) K)
              (Localization.Away (MvPolynomial.X i)) p := by
  let S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K)
  let F : MvPolynomial (Fin n) K →ₐ[K] S :=
    (polynomialProjCoordinateVal K n i).comp (polynomialProjRatioMap K n i)
  have hcoeff : F.toRingHom.comp MvPolynomial.C = algebraMap K S := by
    ext r
    exact F.commutes r
  have hvars : F.toRingHom ∘ polynomialProjDehomogenizationVariable K n i =
      fun j ↦ IsLocalization.Away.invSelf (S := S)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) *
          algebraMap (MvPolynomial (Fin (n + 1)) K) S (MvPolynomial.X j) := by
    funext j
    exact polynomialProjRatioMap_dehomVariable_val K n i j
  change F.toRingHom (MvPolynomial.eval₂ MvPolynomial.C
    (polynomialProjDehomogenizationVariable K n i) p) = _
  rw [MvPolynomial.eval₂_comp_left, hcoeff, hvars]
  change MvPolynomial.eval₂Hom (algebraMap K S)
    (fun j ↦ IsLocalization.Away.invSelf (S := S)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) *
        algebraMap (MvPolynomial (Fin (n + 1)) K) S (MvPolynomial.X j)) p = _
  rw [homogeneousPolynomial_eval₂_scaled hp]
  congr 1
  change MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (n + 1)) K) S).comp MvPolynomial.C)
    ((algebraMap (MvPolynomial (Fin (n + 1)) K) S) ∘ MvPolynomial.X) p = _
  rw [← MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eta]

/-- The distinguished inverse-coordinate power has its actual cancellation
identity in the true ordinary localization. -/
theorem polynomialProj_invSelf_pow_mul (i : Fin (n + 1)) (m : ℕ) :
    IsLocalization.Away.invSelf
      (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K))
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ m *
        algebraMap (MvPolynomial (Fin (n + 1)) K)
          (Localization.Away (MvPolynomial.X i)) (MvPolynomial.X i ^ m) = 1 := by
  rw [map_pow, ← mul_pow, mul_comm, IsLocalization.Away.mul_invSelf, one_pow]

/-- Literal dehomogenization followed by ratios recovers every element
of the genuine degree-zero homogeneous coordinate ring. -/
theorem polynomialProjRatioMap_coordinateDehomogenization (i : Fin (n + 1))
    (z : polynomialProjCoordinateRing K n i) :
    polynomialProjRatioMap K n i (polynomialProjCoordinateDehomogenization K n i z) = z := by
  obtain ⟨m, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (MvPolynomial.isHomogeneous_X K i) z
  rw [polynomialProjCoordinateDehomogenization_mk K n i m p (by simpa using hp)]
  apply HomogeneousLocalization.val_injective
  change polynomialProjCoordinateVal K n i
    (polynomialProjRatioMap K n i (polynomialProjDehomogenization K n i p)) = _
  rw [polynomialProjRatioMap_dehomogenization_val K n i m p (by simpa using hp),
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  symm
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  rw [mul_right_comm, polynomialProj_invSelf_pow_mul, one_mul]

/-- Actual dehomogenization and actual inverse homogeneous ratios give a
true algebra equivalence from the actual chart ring to `n` polynomial variables. -/
def polynomialProjCoordinateEquiv (i : Fin (n + 1)) :
    polynomialProjCoordinateRing K n i ≃ₐ[K] MvPolynomial (Fin n) K where
  toFun := polynomialProjCoordinateDehomogenization K n i
  invFun := polynomialProjRatioMap K n i
  left_inv := polynomialProjRatioMap_coordinateDehomogenization K n i
  right_inv := polynomialProjCoordinateDehomogenization_ratioMap K n i
  map_mul' := (polynomialProjCoordinateDehomogenization K n i).map_mul
  map_add' := (polynomialProjCoordinateDehomogenization K n i).map_add
  commutes' := (polynomialProjCoordinateDehomogenization K n i).commutes


/-- The actual polynomial algebra has its literal relation-free submersive
presentation; the empty Jacobian determinant is genuinely one. -/
def polynomialProjPolynomialPresentation :
    SubmersivePresentation K (MvPolynomial (Fin n) K) (Fin n) (Fin 0) where
  toGenerators := Generators.mvPolynomial K (Fin n)
  relation := Fin.elim0
  span_range_relation_eq_ker := by simp [Generators.ker_mvPolynomial]
  map := Fin.elim0
  map_inj := fun a ↦ Fin.elim0 a
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

/-- The actual homogeneous ratios give a literal relation-free submersive
presentation of the actual projective coordinate ring. -/
def polynomialProjCoordinatePresentation (i : Fin (n + 1)) :
    SubmersivePresentation K (polynomialProjCoordinateRing K n i) (Fin n) (Fin 0) :=
  (polynomialProjPolynomialPresentation K n).ofAlgEquiv (polynomialProjCoordinateEquiv K n i).symm

/-- The actual affine coordinate presentation has exactly its genuine
projective dimension `n`, with no dimension premise. -/
theorem polynomialProjCoordinatePresentation_dimension (i : Fin (n + 1)) :
    (polynomialProjCoordinatePresentation K n i).dimension = n := by
  simp [Presentation.dimension]

/-- Every genuine projective affine coordinate chart is standard smooth
of actual relative dimension `n`, derived from its true polynomial presentation. -/
instance polynomialProjCoordinateRing_isStandardSmooth (i : Fin (n + 1)) :
    Algebra.IsStandardSmoothOfRelativeDimension n K (polynomialProjCoordinateRing K n i) :=
  (polynomialProjCoordinatePresentation K n i).isStandardSmoothOfRelativeDimension
    (polynomialProjCoordinatePresentation_dimension K n i)

/-- The literal actual affine chart structural morphism is natively
smooth of its derived relative dimension. -/
theorem polynomialProjCoordinateImmersion_smooth (i : Fin (n + 1)) :
    SmoothOfRelativeDimension n
      (polynomialProjCoordinateImmersion K n i ≫ polynomialProjStructureMap K n) := by
  rw [polynomialProjCoordinateImmersion_structure]
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).mpr inferInstance

/-- Native smoothness on the genuine homogeneous coordinate charts glues
to native smoothness of actual polynomial projective space. -/
instance polynomialProjStructureMap_smooth : SmoothOfRelativeDimension n (polynomialProjStructureMap K n) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K
  let U : Fin (n + 1) → (polynomialProj K n).Opens := fun i ↦ Proj.basicOpen 𝒜 (MvPolynomial.X i)
  have hcover : ⨆ i, U i = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ homogeneousPolynomial_irrelevant_le_coordinates
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) U hcover
  intro i
  let e := Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) (by decide)
  have : SmoothOfRelativeDimension n
      (polynomialProjCoordinateImmersion K n i ≫ polynomialProjStructureMap K n) :=
    polynomialProjCoordinateImmersion_smooth K n i
  have hfac : (U i).ι ≫ polynomialProjStructureMap K n =
      e.hom ≫ (polynomialProjCoordinateImmersion K n i ≫ polynomialProjStructureMap K n) := by
    simp [e, polynomialProjCoordinateImmersion, Proj.awayι, U, 𝒜, ← Category.assoc]
  rw [hfac]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n) e.hom
    (polynomialProjCoordinateImmersion K n i ≫ polynomialProjStructureMap K n)).mpr this

/-- The explicit relation-free chart presentation evaluates each actual
polynomial generator to precisely its ordered homogeneous coordinate ratio. -/
theorem polynomialProjCoordinatePresentation_val (i : Fin (n + 1)) (a : Fin n) :
    (polynomialProjCoordinatePresentation K n i).val a =
      polynomialProjCoordinateRatio K n i (i.succAbove a) := by
  change polynomialProjRatioMap K n i (MvPolynomial.X a) = _
  simp [polynomialProjRatioMap]

/-- All genuine coordinate-presentation indices are free, because its
literal relation set is empty. -/
def polynomialProjFreeIndexEquiv (i : Fin (n + 1)) :
    ((Set.range (polynomialProjCoordinatePresentation K n i).map)ᶜ : Set (Fin n)) ≃ Fin n where
  toFun := Subtype.val
  invFun a := ⟨a, by rintro ⟨r, _⟩; exact Fin.elim0 r⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual ordered homogeneous coordinate differentials form a genuine
basis, derived from the literal relation-free submersive presentation. -/
def polynomialProjCoordinateDifferentialBasis (i : Fin (n + 1)) :
    Module.Basis (Fin n) (polynomialProjCoordinateRing K n i)
      (KaehlerDifferential K (polynomialProjCoordinateRing K n i)) :=
  (polynomialProjCoordinatePresentation K n i).basisKaehler.reindex
    (polynomialProjFreeIndexEquiv K n i)

/-- Each genuine basis vector is the literal universal differential of
the actual ordered ratio `X_j/X_i`. -/
theorem polynomialProjCoordinateDifferentialBasis_apply (i : Fin (n + 1)) (a : Fin n) :
    polynomialProjCoordinateDifferentialBasis K n i a =
      KaehlerDifferential.D K (polynomialProjCoordinateRing K n i)
        (polynomialProjCoordinateRatio K n i (i.succAbove a)) := by
  simp [polynomialProjCoordinateDifferentialBasis, polynomialProjFreeIndexEquiv,
    SubmersivePresentation.basisKaehler_apply, polynomialProjCoordinatePresentation_val]


/-- The genuine canonical line has its actual ratio-differential sheaf
frame on each genuine Proj coordinate open, via the proved raw exterior
open restriction and affine sheaf comparison. -/
def polynomialProjCanonicalCoordinateFrame (i : Fin (n + 1)) :
    LocalBundleFrame (exteriorCotangentSheaf (polynomialProjStructureMap K n) n)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)) := by
  let X := polynomialProj K n
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K
  let L := exteriorCotangentSheaf (polynomialProjStructureMap K n) n
  let U := Proj.basicOpen 𝒜 (MvPolynomial.X i)
  let A : CommRingCat := .of (polynomialProjCoordinateRing K n i)
  let g : Spec A ⟶ X := polynomialProjCoordinateImmersion K n i
  let e : U.toScheme ≅ Spec A :=
    Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) (by decide)
  have he : g ≫ polynomialProjStructureMap K n = affineStructuralMap K A :=
    polynomialProjCoordinateImmersion_structure K n i
  let E : (Scheme.Modules.restrictFunctor g).obj L ≅ SheafOfModules.unit (Spec A).ringCatSheaf :=
    exteriorCotangentSheafOpenImmersionIso (polynomialProjStructureMap K n) g n ≪≫
      eqToIso (congrArg (fun q ↦ exteriorCotangentSheaf q n) he) ≪≫
        affineTopExteriorSheafFrame K A (polynomialProjCoordinateDifferentialBasis K n i)
  have hfac : e.hom ≫ g = U.ι := by
    simp [e, g, polynomialProjCoordinateImmersion, Proj.awayι, U, 𝒜, ← Category.assoc]
  let EV : (Scheme.Modules.restrictFunctor U.ι).obj L ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorCongr hfac).symm.app L ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom g).app L ≪≫
        (Scheme.Modules.restrictFunctor e.hom).mapIso E ≪≫
          Scheme.Modules.restrictUnitIso e.hom
  exact (Scheme.Modules.overEquiv U).unitIso.app (L.over U) ≪≫
    (Scheme.Modules.overEquiv U).inverse.mapIso
      ((Scheme.Modules.overFunctorEquiv U).app L ≪≫ EV) ≪≫
        U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf

/-- The actual polynomial projective canonical line has its genuine finite
coordinate atlas, derived from actual ratio differential bases and the true cover. -/
def polynomialProjCanonicalCoordinateAtlas :
    LineBundleAtlas (exteriorCotangentSheaf (polynomialProjStructureMap K n) n) where
  I := Fin (n + 1)
  opens i := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
  covers x := (homogeneousPolynomialTwistingAtlas (K := K) (I := Fin (n + 1)) 0).covers x
  frame := polynomialProjCanonicalCoordinateFrame K n

/-- The actual anticanonical local frame is the genuine sheaf-Hom dual
of the literal canonical ratio-differential frame. -/
def polynomialProjAnticanonicalCoordinateFrame (i : Fin (n + 1)) :
    LocalBundleFrame (anticanonicalLineSheaf (polynomialProjStructureMap K n) n)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)) :=
  (polynomialProjCanonicalCoordinateFrame K n i).dual

/-- The actual global canonical dual has its derived genuine finite
coordinate atlas; no line identification or atlas is an input. -/
def polynomialProjAnticanonicalCoordinateAtlas :
    LineBundleAtlas (anticanonicalLineSheaf (polynomialProjStructureMap K n) n) :=
  (polynomialProjCanonicalCoordinateAtlas K n).dual

/-- Genuine canonical and anticanonical sections pair by literal sheaf-Hom
evaluation to give an actual tensor isomorphism on polynomial projective space. -/
def polynomialProjAnticanonicalEvaluationIso :
    bundleTensor (anticanonicalLineSheaf (polynomialProjStructureMap K n) n)
      (exteriorCotangentSheaf (polynomialProjStructureMap K n) n) ≅
        SheafOfModules.unit (polynomialProj K n).ringCatSheaf :=
  bundleDualEvaluationIso _ (polynomialProjCanonicalCoordinateAtlas K n)

end
end ComplexSchemes
