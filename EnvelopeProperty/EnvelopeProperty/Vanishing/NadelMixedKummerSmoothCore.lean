import EnvelopeProperty.Vanishing.NadelMixedKummerMinor
import EnvelopeProperty.Vanishing.NadelMixedKummerLocalization
import Mathlib.RingTheory.Smooth.Locus

/-! # Actual ambient geometry and localization of the whole mixed Kummer source -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer
namespace SmoothSource
open Algebra
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {n q : ℕ} (x : Fin n → R) (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
  (N : Fin q → ℕ) (c : Fin q → R)

/-- The ACTUAL whole polynomial ambient extension of the SAME mixed quotient. -/
def extension : Algebra.Extension.{u} k (Ring N c) :=
  Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k (equationsIdeal N c))
    Ideal.Quotient.mk_surjective

/-- The ACTUAL ambient extension kernel is the entire original equation ideal. -/
theorem extension_ker : (extension (k := k) N c).ker = equationsIdeal N c := by
  change RingHom.ker (Ideal.Quotient.mk (equationsIdeal N c)) = equationsIdeal N c
  exact Ideal.mk_ker

/-- The original equation family generates the SAME whole actual extension kernel. -/
theorem span_relation_eq_ker : Ideal.span (Set.range (relation N c)) =
    (extension (k := k) N c).ker := (extension_ker (k := k) N c).symm

include x hx in
/-- The original etale coordinate chart derives actual smoothness of its
whole coefficient algebra over the original base. -/
theorem coefficient_smooth : Algebra.Smooth k R := by
  let _ := (MvPolynomial.aeval (R := k) x).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) R :=
    IsScalarTower.of_algebraMap_eq fun a => ((MvPolynomial.aeval x).commutes a).symm
  have : Algebra.Etale (MvPolynomial (Fin n) k) R := hx.toAlgebra
  have : Algebra.Smooth k (MvPolynomial (Fin n) k) := {}
  exact Algebra.Smooth.comp k (MvPolynomial (Fin n) k) R

include x hx in
/-- The SAME whole polynomial ambient algebra is actually formally smooth;
this is derived from the actual original etale coordinate map. -/
theorem ambient_formallySmooth : Algebra.FormallySmooth k (extension (k := k) N c).Ring := by
  have := coefficient_smooth x hx
  have : Algebra.FormallySmooth R (MvPolynomial (Fin q) R) := inferInstance
  exact Algebra.FormallySmooth.comp k R (MvPolynomial (Fin q) R)

include x hx in
/-- The WHOLE original mixed quotient is actually finitely presented over k. -/
theorem finitePresentation : Algebra.FinitePresentation k (Ring N c) := by
  have := coefficient_smooth x hx
  have : Algebra.FinitePresentation k (MvPolynomial (Fin q) R) :=
    Algebra.FinitePresentation.trans k R (MvPolynomial (Fin q) R)
  have : Algebra.FinitePresentation (MvPolynomial (Fin q) R) (Ring N c) :=
    Algebra.FinitePresentation.quotient
      (Submodule.fg_span (Set.finite_range (relation N c)))
  exact Algebra.FinitePresentation.trans k (MvPolynomial (Fin q) R) (Ring N c)

/-- The actual original old-coordinate/root-coordinate derivation on the
SAME whole ambient polynomial algebra. -/
def ambientDerivative : (Fin n ⊕ Fin q) → Derivation k (MvPolynomial (Fin q) R) (MvPolynomial (Fin q) R) :=
  Sum.elim (fun j => coefficientDerivation (Char0.etalePartialDeriv x hx j))
    (fun j => by
      letI : LinearMap.CompatibleSMul (MvPolynomial (Fin q) R) (MvPolynomial (Fin q) R) k R :=
        inferInstance
      exact (MvPolynomial.pderiv j).restrictScalars k)

/-- The SAME actual old/root derivative on the actual extension's ambient ring. -/
def extensionDerivative (j : Fin n ⊕ Fin q) :
    Derivation k (extension (k := k) N c).Ring (extension (k := k) N c).Ring :=
  ambientDerivative x hx j

variable (p : Ideal (Ring N c)) [p.IsPrime]

/-- The native actual extension at the SAME actual source prime. -/
abbrev localExtension := ExtensionLocalization.localExtension (extension (k := k) N c) p

local instance ambientAlgebra : Algebra (extension (k := k) N c).Ring (localExtension (k := k) N c p).Ring :=
  ExtensionLocalization.ambientAlgebra _ _
local instance ambientLocalization : IsLocalization
    (p.primeCompl.comap (algebraMap (extension (k := k) N c).Ring (Ring N c)))
      (localExtension (k := k) N c p).Ring := ExtensionLocalization.ambientLocalization _ _
local instance ambientTower : IsScalarTower k (extension (k := k) N c).Ring (localExtension (k := k) N c p).Ring :=
  ExtensionLocalization.ambientTower _ _
local instance ambientFormallyEtale : Algebra.FormallyEtale (extension (k := k) N c).Ring
    (localExtension (k := k) N c p).Ring :=
  Algebra.FormallyEtale.of_isLocalization
    (p.primeCompl.comap (algebraMap (extension (k := k) N c).Ring (Ring N c)))

/-- The ACTUAL original polynomial element retains the actual original target
value after native source/target localization. -/
theorem local_triangle (a : (extension (k := k) N c).Ring) :
    algebraMap (localExtension (k := k) N c p).Ring (Localization.AtPrime p)
      (algebraMap (extension (k := k) N c).Ring (localExtension (k := k) N c p).Ring a) =
        algebraMap (Ring N c) (Localization.AtPrime p)
          (algebraMap (extension (k := k) N c).Ring (Ring N c) a) := by
  exact congrArg (fun f : (extension (k := k) N c).Ring →+* Localization.AtPrime p => f a)
    (IsLocalization.map_comp (Q := Localization.AtPrime p)
      (g := algebraMap (extension (k := k) N c).Ring (Ring N c)) (le_refl _))

/-- Every actual old/root derivative is transported to the actual whole
prime-localized extension and its SAME actual target localization. -/
def localDerivative (j : Fin n ⊕ Fin q) :
    Derivation k (localExtension (k := k) N c p).Ring (Localization.AtPrime p) :=
  (Algebra.linearMap (localExtension (k := k) N c p).Ring (Localization.AtPrime p)).compDer
    (DerivativeLocalization.extend (extensionDerivative x hx N c j))

/-- The actual localized derivative retains the original derivative of every
original relation; no derivative or chart compatibility is assumed. -/
theorem localDerivative_original (j : Fin n ⊕ Fin q) (a : (extension (k := k) N c).Ring) :
    localDerivative x hx N c p j
      (algebraMap (extension (k := k) N c).Ring (localExtension (k := k) N c p).Ring a) =
        algebraMap (Ring N c) (Localization.AtPrime p)
          (algebraMap (extension (k := k) N c).Ring (Ring N c) (extensionDerivative x hx N c j a)) := by
  change algebraMap (localExtension (k := k) N c p).Ring (Localization.AtPrime p)
    (DerivativeLocalization.extend (extensionDerivative x hx N c j)
      (algebraMap (extension (k := k) N c).Ring (localExtension (k := k) N c p).Ring a)) = _
  rw [DerivativeLocalization.extend_algebraMap, local_triangle N c p]

/-- The SAME actual whole-source residue map at its original prime. -/
def residueMap : Ring N c →+* IsLocalRing.ResidueField (Localization.AtPrime p) :=
  (IsLocalRing.residue (Localization.AtPrime p)).comp
    (algebraMap (Ring N c) (Localization.AtPrime p))

/-- The whole original relation family in its actual localized ambient extension. -/
def localRelation (i : Fin q) : (localExtension (k := k) N c p).Ring :=
  algebraMap (extension (k := k) N c).Ring (localExtension (k := k) N c p).Ring (relation N c i)

/-- The actual localized relation Jacobian at any explicitly named old/root columns. -/
def derivativeJacobian (j : Fin q → (Fin n ⊕ Fin q)) :
    Matrix (Fin q) (Fin q) (Localization.AtPrime p) :=
  CotangentCriterion.jacobian (localExtension (k := k) N c p) (localRelation N c p)
    (fun i => localDerivative x hx N c p (j i))

/-- Every actual localized Jacobian entry retains its original relation derivative. -/
theorem derivativeJacobian_apply (j : Fin q → (Fin n ⊕ Fin q)) (a b : Fin q) :
    derivativeJacobian x hx N c p j a b =
      algebraMap (Ring N c) (Localization.AtPrime p)
        (algebraMap (extension (k := k) N c).Ring (Ring N c)
          (extensionDerivative x hx N c (j a) (relation N c b))) :=
  localDerivative_original x hx N c p (j a) (relation N c b)

end SmoothSource
end EnvelopeProperty.Vanishing.NadelMixedKummer
