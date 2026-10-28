import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.Algebra.MvPolynomial.Expand

/-! # Literal independent-coordinate Kummer pullbacks with smooth source

The coordinate power map fixes the actual coefficient ring.  The new source
is the genuine pullback of the original etale chart, and its etale map is
to the source polynomial space.  No smoothness of the branched projection
to the original chart, or global covering-existence input, is used.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelKummerCover

variable (R : Type u) [CommRing R]

/-- The actual polynomial spectrum with its original n coordinates. -/
abbrev polynomialSpace (n : ℕ) : Scheme.{u} := Spec (.of (MvPolynomial (Fin n) R))

private def polynomialPrePresentation (n : ℕ) :
    Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty where
  toGenerators := Algebra.Generators.mvPolynomial R (Fin n)
  relation := Empty.elim
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_mvPolynomial]
    simp
  map := Empty.elim
  map_inj := Function.injective_of_subsingleton _

private def polynomialPresentation (n : ℕ) :
    Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty where
  __ := polynomialPrePresentation R n
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Matrix.det_isEmpty, map_one]
    exact isUnit_one

/-- The original n-variable polynomial algebra has its actual empty-relation
standard-smooth presentation of exactly the original relative dimension. -/
theorem polynomialAlgebra_standardSmooth (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) :=
  (polynomialPresentation R n).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

/-- The original coefficient projection of the actual polynomial spectrum. -/
def polynomialProjection (n : ℕ) : polynomialSpace R n ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R)))

/-- The actual coefficient projection is smooth of the precise original
relative dimension; this is derived from the genuine polynomial presentation. -/
theorem polynomialProjection_smooth (n : ℕ) :
    SmoothOfRelativeDimension n (polynomialProjection R n) := by
  rw [polynomialProjection, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  exact RingHom.locally_of
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)) _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr
      (polynomialAlgebra_standardSmooth R n))

/-- The actual independent-coordinate power homomorphism fixes R and sends
coordinate j to its literal m j-th power. -/
def coordinatePowerHom {n : ℕ} (m : Fin n → ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (fun j => MvPolynomial.X j ^ m j)

@[simp] theorem coordinatePowerHom_X {n : ℕ} (m : Fin n → ℕ) (j : Fin n) :
    coordinatePowerHom R m (MvPolynomial.X j) = MvPolynomial.X j ^ m j :=
  MvPolynomial.aeval_X _ _

@[simp] theorem coordinatePowerHom_C {n : ℕ} (m : Fin n → ℕ) (r : R) :
    coordinatePowerHom R m (MvPolynomial.C r) = MvPolynomial.C r :=
  (coordinatePowerHom R m).commutes r

/-- The original scheme coordinate-power map, with no etaleness assertion
along its branch coordinate hyperplanes. -/
def coordinatePowerMap {n : ℕ} (m : Fin n → ℕ) : polynomialSpace R n ⟶ polynomialSpace R n :=
  Spec.map (CommRingCat.ofHom (coordinatePowerHom R m).toRingHom)

/-- The actual coordinate-power map retains the SAME coefficient projection. -/
theorem coordinatePowerMap_over {n : ℕ} (m : Fin n → ℕ) :
    coordinatePowerMap R m ≫ polynomialProjection R n = polynomialProjection R n := by
  rw [coordinatePowerMap, polynomialProjection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (coordinatePowerHom R m).commutes r)

/-- The actual power-map comorphism on every original polynomial section. -/
theorem coordinatePowerMap_appTop {n : ℕ} (m : Fin n → ℕ)
    (z : MvPolynomial (Fin n) R) :
    (coordinatePowerMap R m).appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R))).inv z) =
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R))).inv (coordinatePowerHom R m z) := by
  rw [coordinatePowerMap, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  rfl

variable {R} {n : ℕ} {U : Scheme.{u}} (g : U ⟶ polynomialSpace R n) (m : Fin n → ℕ)

/-- The literal pullback of the SAME original chart through the actual
independent-coordinate power map. -/
def pullbackScheme : Scheme.{u} := Limits.pullback g (coordinatePowerMap R m)

/-- The actual (in general branched) projection to the original chart. -/
def chartProjection : pullbackScheme g m ⟶ U := Limits.pullback.fst _ _

/-- The actual projection to the source polynomial space. -/
def affineProjection : pullbackScheme g m ⟶ polynomialSpace R n := Limits.pullback.snd _ _

/-- The actual coefficient structure on the literal new source. -/
def structureMap : pullbackScheme g m ⟶ Spec (.of R) :=
  affineProjection g m ≫ polynomialProjection R n

/-- The original square is the genuine native pullback square. -/
theorem projection_square :
    chartProjection g m ≫ g = affineProjection g m ≫ coordinatePowerMap R m :=
  Limits.pullback.condition

/-- The original coordinate on the source polynomial space, pulled to
the SAME literal new source through its actual second projection. -/
def coordinateRoot (j : Fin n) : Γ(pullbackScheme g m, ⊤) :=
  (affineProjection g m).appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R))).inv (MvPolynomial.X j))

/-- The actual new coordinate is a literal root of the SAME original
chart coordinate, by the native pullback square and actual comorphisms. -/
theorem coordinateRoot_pow (j : Fin n) :
    (chartProjection g m).appTop
        (g.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R))).inv (MvPolynomial.X j))) =
      coordinateRoot g m j ^ m j := by
  have h := congrArg
    (fun t : pullbackScheme g m ⟶ polynomialSpace R n =>
      t.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R))).inv (MvPolynomial.X j)))
    (projection_square g m)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [coordinatePowerMap_appTop, coordinatePowerHom_X, map_pow, map_pow] at h
  exact h

/-- The actual polynomial projection is etale by base change of the
ORIGINAL etale chart; the branched chart projection is a different map. -/
theorem affineProjection_etale [Etale g] : Etale (affineProjection g m) :=
  inferInstanceAs (Etale (Limits.pullback.snd g (coordinatePowerMap R m)))

/-- The literal source is smooth of the same n-dimensional relative
geometry, by etale base change followed by the actual polynomial projection. -/
theorem structureMap_smooth [Etale g] : SmoothOfRelativeDimension n (structureMap g m) := by
  let : Etale (affineProjection g m) := affineProjection_etale g m
  let : SmoothOfRelativeDimension n (polynomialProjection R n) := polynomialProjection_smooth R n
  change SmoothOfRelativeDimension n (affineProjection g m ≫ polynomialProjection R n)
  simpa only [Nat.zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n)
      (affineProjection g m ≫ polynomialProjection R n))

/-- Any genuine original chart structure triangle is retained by the SAME
actual pullback source and its two original projections. -/
theorem chartProjection_over (p : U ⟶ Spec (.of R))
    (hg : g ≫ polynomialProjection R n = p) :
    chartProjection g m ≫ p = structureMap g m := by
  rw [← hg, ← Category.assoc, projection_square, Category.assoc, coordinatePowerMap_over]
  rfl

end EnvelopeProperty.Vanishing.NadelKummerCover
