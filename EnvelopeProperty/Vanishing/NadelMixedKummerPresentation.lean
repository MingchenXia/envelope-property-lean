import EnvelopeProperty.Vanishing.NadelMixedKummerDifferential
import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverChartsRoots
import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts

/-! # The WHOLE actual mixed root quotient and its original geometric chart

All original root degrees may vary. The quotient and every map are internally
constructed. Its whole universal property identifies it with the original
finite-list multicover chart; no chart identification is an input.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelMixedKummer
variable {R : Type u} [CommRing R] {q : ℕ}

/-- The literal ideal of ALL original mixed root equations. -/
def equationsIdeal (N : Fin q → ℕ) (c : Fin q → R) : Ideal (MvPolynomial (Fin q) R) :=
  Ideal.span (Set.range (relation N c))

/-- The WHOLE actual original simultaneous quotient; all components and
nilpotents, including complete unit-root factors, are retained. -/
abbrev Ring (N : Fin q → ℕ) (c : Fin q → R) := MvPolynomial (Fin q) R ⧸ equationsIdeal N c

/-- Every original root in the SAME whole quotient. -/
def root (N : Fin q → ℕ) (c : Fin q → R) (i : Fin q) : Ring N c :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- Every original root satisfies its actual original-degree equation. -/
theorem root_pow (N : Fin q → ℕ) (c : Fin q → R) (i : Fin q) :
    root N c i ^ N i = algebraMap R (Ring N c) (c i) := by
  have h : Ideal.Quotient.mk (equationsIdeal N c) (relation N c i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  change Ideal.Quotient.mk _ (MvPolynomial.X i ^ N i - MvPolynomial.C (c i)) = 0 at h
  rw [map_sub, map_pow] at h
  exact sub_eq_zero.mp h

variable {S : Type u} [CommRing S] (N : Fin q → ℕ) (c : Fin q → R)
  (f : R →+* S) (y : Fin q → S) (hy : ∀ i, y i ^ N i = f (c i))

/-- The actual universal map of the WHOLE original mixed root quotient. -/
def evaluate : Ring N c →+* S :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f y) (by
    change equationsIdeal N c ≤ RingHom.ker (MvPolynomial.eval₂Hom f y)
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change MvPolynomial.eval₂Hom f y (relation N c i) = 0
    simp only [relation, map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
      hy i, sub_self])

/-- The whole mixed evaluation retains the original coefficient map. -/
theorem evaluate_structure : (evaluate N c f y hy).comp (algebraMap R (Ring N c)) = f := by
  ext a
  exact MvPolynomial.eval₂Hom_C f y a

/-- Every original root retains its actual evaluation value. -/
theorem evaluate_root (i : Fin q) : evaluate N c f y hy (root N c i) = y i :=
  MvPolynomial.eval₂Hom_X' f y i

/-- Equality on all original coefficients and ALL original roots gives
WHOLE algebra equality; no component or nilpotent is discarded. -/
theorem hom_ext (g h : Ring N c →+* S)
    (hc : g.comp (algebraMap R (Ring N c)) = h.comp (algebraMap R (Ring N c)))
    (hr : ∀ i, g (root N c i) = h (root N c i)) : g = h := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    exact congrArg (fun t : R →+* S => t a) hc
  · exact hr

namespace OriginalChart
open NadelAuxiliaryMulticover
variable {X : Scheme.{u}} (U : X.Opens) (D : List (AuxiliarySection X)) (e : NadelAuxiliaryMulticoverCharts.Frames U D)

/-- The SAME original finite-list root degrees, with no common-degree replacement. -/
abbrev degree (i : Fin D.length) : ℕ := (D.get i).degree

/-- The literal mixed quotient of the SAME original framed section coefficients. -/
abbrev Ring := NadelMixedKummer.Ring (degree D) (NadelAuxiliaryMulticoverCharts.coefficients U D e)

/-- The actual whole quotient evaluation into the original affine chart algebra. -/
def toChart : Ring U D e →+* NadelAuxiliaryMulticoverCharts.ring U D e :=
  evaluate (degree D) (NadelAuxiliaryMulticoverCharts.coefficients U D e) (NadelAuxiliaryMulticoverCharts.structureMap U D e).hom
    (NadelAuxiliaryMulticoverCharts.root U D e) (NadelAuxiliaryMulticoverCharts.root_pow U D e)

/-- The original chart evaluation into the WHOLE mixed quotient algebra. -/
def fromChart : NadelAuxiliaryMulticoverCharts.ring U D e →+* Ring U D e :=
  NadelAuxiliaryMulticoverCharts.evaluate U D e (algebraMap (NadelAuxiliaryMulticoverCharts.baseRing U) (Ring U D e))
    (NadelMixedKummer.root (degree D) (NadelAuxiliaryMulticoverCharts.coefficients U D e))
    (NadelMixedKummer.root_pow (degree D) (NadelAuxiliaryMulticoverCharts.coefficients U D e))

/-- The actual whole original finite-list chart is this entire variable-degree
quotient. The equivalence is proved by BOTH whole universal properties. -/
def equiv : NadelAuxiliaryMulticoverCharts.ring U D e ≃+* Ring U D e := by
  refine RingEquiv.ofRingHom (fromChart U D e) (toChart U D e) ?_ ?_
  · apply hom_ext
    · dsimp only [fromChart, toChart]
      rw [RingHom.comp_assoc, evaluate_structure, NadelAuxiliaryMulticoverCharts.evaluate_structure]
      rfl
    · intro i
      change fromChart U D e (toChart U D e _) = _
      dsimp only [fromChart, toChart]
      rw [evaluate_root]
      exact NadelAuxiliaryMulticoverCharts.evaluate_root _ _ _ _ _ _ _
  · apply NadelAuxiliaryMulticoverCharts.hom_ext U D e
    · dsimp only [fromChart, toChart]
      rw [RingHom.comp_assoc, NadelAuxiliaryMulticoverCharts.evaluate_structure, evaluate_structure]
      rfl
    · intro i
      change toChart U D e (fromChart U D e _) = _
      dsimp only [fromChart, toChart]
      rw [NadelAuxiliaryMulticoverCharts.evaluate_root]
      exact evaluate_root _ _ _ _ _ _

/-- A genuine scheme isomorphism from the WHOLE actual mixed quotient spectrum
to the SAME original whole affine-open multicover restriction. -/
def schemeIso [IsAffine U.toScheme] :
    Spec (.of (Ring U D e)) ≅ Limits.pullback (projection D) U.ι :=
  Scheme.Spec.mapIso (equiv U D e).toCommRingCatIso.op ≪≫ NadelAuxiliaryMulticoverCharts.wholeChartIso U D e

end OriginalChart
end EnvelopeProperty.Vanishing.NadelMixedKummer
