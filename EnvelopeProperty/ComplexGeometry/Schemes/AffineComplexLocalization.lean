import EnvelopeProperty.ComplexGeometry.Schemes.AffineComplexPoints
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Localization.Algebra

/-! # Actual analytic principal-open charts

Complex points of the actual algebra localization are identified with the
nonvanishing open subset of the original complex point space. The topology
comparison comes from actual fraction evaluation, not a presumed analytic atlas.
-/

namespace ComplexSchemes

noncomputable section

universe u v

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The actual nonvanishing locus of an algebra element on complex points. -/
def complexPrincipalOpen (f : A) : Set (ComplexAlgebraPoint A) := {p | p f ≠ 0}

/-- A principal nonvanishing locus is open in the evaluation topology. -/
theorem complexPrincipalOpen_isOpen (f : A) : IsOpen (complexPrincipalOpen f) := by
  exact isClosed_singleton.isOpen_compl.preimage (complexPoint_evaluation_continuous f)

variable (S : Type v) [CommRing S] [Algebra ℂ S] [Algebra A S]
  [IsScalarTower ℂ A S] (f : A) [IsLocalization.Away f S]

/-- Actual localization points pull back to the principal nonvanishing locus. -/
def localizationComplexPoint_restrict (p : ComplexAlgebraPoint S) :
    complexPrincipalOpen f :=
  ⟨p.comp (Algebra.algHom ℂ A S), by
    change p (algebraMap A S f) ≠ 0
    exact ((IsLocalization.Away.algebraMap_isUnit f).map p).ne_zero⟩

/-- An actual point with nonzero denominator extends by the localization
universal property. -/
def localizationComplexPoint_extend (p : complexPrincipalOpen f) :
    ComplexAlgebraPoint S :=
  IsLocalization.Away.liftAlgHom f (isUnit_iff_ne_zero.mpr p.property)

/-- Extension evaluates original algebra elements by their original point. -/
theorem localizationComplexPoint_extend_algebraMap (p : complexPrincipalOpen f) (a : A) :
    localizationComplexPoint_extend S f p (algebraMap A S a) = p.val a := by
  exact IsLocalization.Away.lift_eq f (isUnit_iff_ne_zero.mpr p.property) a

/-- The actual universal maps are inverse, including arbitrary localization models. -/
def localizationComplexPointEquiv : ComplexAlgebraPoint S ≃ complexPrincipalOpen f where
  toFun := localizationComplexPoint_restrict S f
  invFun := localizationComplexPoint_extend S f
  left_inv p := by
    apply IsLocalization.algHom_ext (Submonoid.powers f)
    ext a
    exact localizationComplexPoint_extend_algebraMap S f _ a
  right_inv p := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    exact localizationComplexPoint_extend_algebraMap S f p a

/-- The value of a genuine localization element is its numerator divided by
the corresponding denominator power. -/
theorem localizationComplexPoint_eval_fraction (p : complexPrincipalOpen f)
    (s : S) (n : ℕ) (a : A) (hs : s * algebraMap A S f ^ n = algebraMap A S a) :
    localizationComplexPoint_extend S f p s = p.val a / p.val f ^ n := by
  apply (eq_div_iff (pow_ne_zero n p.property)).mpr
  have h := congrArg (localizationComplexPoint_extend S f p) hs
  simpa only [map_mul, map_pow, localizationComplexPoint_extend_algebraMap] using h

/-- Restriction is the continuous pullback by the actual localization map. -/
theorem localizationComplexPoint_restrict_continuous :
    Continuous (localizationComplexPoint_restrict S f) := by
  apply Continuous.subtype_mk
  exact complexPoint_pullback_continuous (Algebra.algHom ℂ A S)

/-- Actual fraction evaluations make point extension continuous on the
nonvanishing open subset. -/
theorem localizationComplexPoint_extend_continuous :
    Continuous (localizationComplexPoint_extend S f) := by
  apply (continuous_complexPoint_iff _).2
  intro s
  obtain ⟨n, a, hs⟩ := IsLocalization.Away.surj f s
  have hn := (complexPoint_evaluation_continuous a).comp
    (continuous_subtype_val : Continuous (Subtype.val : complexPrincipalOpen f → _))
  have hd := ((complexPoint_evaluation_continuous f).comp
    (continuous_subtype_val : Continuous (Subtype.val : complexPrincipalOpen f → _))).pow n
  have hdiv := hn.div hd (fun p => pow_ne_zero n p.property)
  convert hdiv using 1
  funext p
  exact localizationComplexPoint_eval_fraction S f p s n a hs

/-- Complex points of a localization have the actual analytic principal-open topology. -/
def localizationComplexPointHomeomorph :
    ComplexAlgebraPoint S ≃ₜ complexPrincipalOpen f where
  toEquiv := localizationComplexPointEquiv S f
  continuous_toFun := localizationComplexPoint_restrict_continuous S f
  continuous_invFun := localizationComplexPoint_extend_continuous S f

end

end ComplexSchemes
