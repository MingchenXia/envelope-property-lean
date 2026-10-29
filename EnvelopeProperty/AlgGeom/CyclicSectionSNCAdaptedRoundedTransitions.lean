import EnvelopeProperty.AlgGeom.CyclicSectionSNCAdaptedRoundedCharts
import EnvelopeProperty.AlgGeom.CyclicSectionSNCAdaptedFramedUnits
import EnvelopeProperty.AlgGeom.CyclicSectionSNCInjectiveBaseChange
import EnvelopeProperty.AlgGeom.CyclicSectionSNCRoundedRescaling

/-! # Actual whole rounded transitions of the original adapted framed atlas

The true coefficient injection, canonical component units and original frame
unit construct each actual generic and rounded map. No preservation, matching
or cocycle conclusion is a premise.
-/

noncomputable section
universe u v w
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
open scoped BigOperators
attribute [local instance] OreLocalization.instAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionSNCAdaptedRoundedTransitions
open CyclicSectionSNCAdaptedFramedAtlas CyclicSectionSNCAdaptedFramedUnits
open CyclicSectionSNCAdaptedRoundedCharts

namespace Comparison
open CyclicSectionSNCNormalizationRounded

private theorem trans_apply_smul {R A B C : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (e : A ≃ₐ[R] B) (f : B ≃ₐ[R] C) (x : A) (y : B) (z : C) (v w : Rˣ)
    (hx : e x = v • y) (hy : f y = (w : R) • z) :
    (e.trans f) x = (w * v) • z := by
  change f (e x) = _
  rw [hx, Units.smul_def, _root_.map_smul, hy]
  simp only [Units.smul_def, Units.val_mul, smul_smul]
  exact congrArg (fun r : R => r • z) (mul_comm _ _)

variable {R : Type v} [CommRing R] [IsDomain R] {J : Type w} [Fintype J]
variable (n : ℕ) (α : J → ℕ) (b : R) (f : J → R) (ν : Rˣ) (ε : J → Rˣ)
variable (u : R) (g : J → R)
variable (hu : u = CyclicSectionSNCBranchUnitGauge.coefficient α ((ν : R)^n * b) ε)
variable (hg : g = CyclicSectionSNCBranchUnitGauge.branches f ε)

private def generic : GenericRootRing n α u g ≃ₐ[R] GenericRootRing n α b f := by
  subst u
  subst g
  exact ((CyclicSectionSNCBranchUnitGauge.genericEquiv n α ((ν : R)^n * b) f ε).restrictScalars R).trans
    (CyclicSectionSNCIntegralClosureRescaling.genericRescaleEquiv n α b ((ν : R)^n * b) f ν rfl)

omit [IsDomain R] in
private theorem generic_fraction (r : FractionRing R) :
    generic n α b f ν ε u g hu hg (algebraMap (FractionRing R) (GenericRootRing n α u g) r) =
      algebraMap (FractionRing R) (GenericRootRing n α b f) r := by
  subst u
  subst g
  exact (congrArg
    (CyclicSectionSNCIntegralClosureRescaling.genericRescaleEquiv n α b ((ν : R)^n * b) f ν rfl)
    ((CyclicSectionSNCBranchUnitGauge.genericEquiv n α ((ν : R)^n * b) f ε).commutes r)).trans
      (RingHom.congr_fun
        (CyclicSectionSNCIntegralClosureRescaling.genericRescaleEquiv_fraction_coefficients
          n α b ((ν : R)^n * b) f ν rfl) r)

omit [IsDomain R] in
private theorem generic_root :
    generic n α b f ν ε u g hu hg
      (CyclicSectionAlgebra.root n (algebraMap R (FractionRing R) (u * ∏ j, g j ^ α j))) =
      algebraMap R (GenericRootRing n α b f) (ν : R) *
        CyclicSectionAlgebra.root n (algebraMap R (FractionRing R) (b * ∏ j, f j ^ α j)) := by
  subst u
  subst g
  exact (congrArg
    (CyclicSectionSNCIntegralClosureRescaling.genericRescaleEquiv n α b ((ν : R)^n * b) f ν rfl)
    (CyclicSectionSNCBranchUnitGauge.genericEquiv_root n α ((ν : R)^n * b) f ε)).trans
      (CyclicSectionSNCIntegralClosureRescaling.genericRescaleEquiv_root
        n α b ((ν : R)^n * b) f ν rfl)

variable (hn : 0 < n) (hf : ∀ j, f j ≠ 0) (hg0 : ∀ j, g j ≠ 0)

private def rounded : roundedAlgebra n α u g hn hg0 ≃ₐ[R] roundedAlgebra n α b f hn hf := by
  subst u
  subst g
  exact (CyclicSectionSNCBranchUnitGauge.roundedAlgebraEquiv n α ((ν : R)^n * b) f ε hn hf).trans
    (CyclicSectionSNCRoundedRescaling.roundedAlgebraEquiv n α b ((ν : R)^n * b) f ν rfl hn hf)

private theorem rounded_coe (x : roundedAlgebra n α u g hn hg0) :
    (rounded n α b f ν ε u g hu hg hn hf hg0 x : GenericRootRing n α b f) =
      generic n α b f ν ε u g hu hg (x : GenericRootRing n α u g) := by
  subst u
  subst g
  rfl

private theorem rounded_basis_canonical (i : Fin n) :
    ((CyclicSectionSNCBranchUnitGauge.roundedAlgebraEquiv n α ((ν : R)^n * b) f ε hn hf).trans
      (CyclicSectionSNCRoundedRescaling.roundedAlgebraEquiv n α b ((ν : R)^n * b) f ν rfl hn hf))
      (basis n α (CyclicSectionSNCBranchUnitGauge.coefficient α ((ν : R)^n * b) ε)
        (CyclicSectionSNCBranchUnitGauge.branches f ε) hn
        (CyclicSectionSNCBranchUnitGauge.branches_nonzero f ε hf) i) =
      (ν ^ (i : ℕ) * (CyclicSectionSNCBranchUnitGauge.productUnit
        (fun j => (i : ℕ) * α j / n) ε)⁻¹ : Rˣ) • basis n α b f hn hf i := by
  exact trans_apply_smul
    (CyclicSectionSNCBranchUnitGauge.roundedAlgebraEquiv n α ((ν : R)^n * b) f ε hn hf)
    (CyclicSectionSNCRoundedRescaling.roundedAlgebraEquiv n α b ((ν : R)^n * b) f ν rfl hn hf)
    _ _ _ (CyclicSectionSNCBranchUnitGauge.productUnit (fun j => (i : ℕ) * α j / n) ε)⁻¹
    (ν ^ (i : ℕ))
    (CyclicSectionSNCBranchUnitGauge.roundedAlgebraEquiv_basis n α ((ν : R)^n * b) f ε hn hf i)
    (CyclicSectionSNCRoundedRescaling.roundedAlgebraEquiv_basis n α b ((ν : R)^n * b) f ν rfl hn hf i)

private theorem rounded_basis (i : Fin n) :
    rounded n α b f ν ε u g hu hg hn hf hg0 (basis n α u g hn hg0 i) =
      (ν ^ (i : ℕ) * (CyclicSectionSNCBranchUnitGauge.productUnit
        (fun j => (i : ℕ) * α j / n) ε)⁻¹ : Rˣ) • basis n α b f hn hf i := by
  subst u
  subst g
  exact rounded_basis_canonical n α b f ν ε hn hf i

end Comparison

variable {X : Scheme.{u}} [IsIntegral X]
variable {L : X.Modules} {n : ℕ} {s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L n}
variable {F : Scheme.DivisorFamily X} {a : F.ι → ℕ}

/-- The genuine original affine coefficient restriction, with its actual arrow. -/
abbrev restriction {c d : Chart L n s F a} (h : c ⟶ d) :
    coefficientRing d →+* coefficientRing c := (X.presheaf.map h.hom.op).hom

omit [IsIntegral X] in
theorem restriction_id (c : Chart L n s F a) : restriction (𝟙 c) = RingHom.id _ := by
  change (X.presheaf.map (𝟙 (Opposite.op (chartAffine c).1))).hom = _
  rw [X.presheaf.map_id]
  rfl

omit [IsIntegral X] in
theorem restriction_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) :
    restriction (h ≫ k) = (restriction h).comp (restriction k) := by
  change (X.presheaf.map ((h.hom ≫ k.hom).op)).hom = _
  rw [op_comp, X.presheaf.map_comp]
  rfl

/-- Original base integrality and the actual nonempty source make restriction injective. -/
theorem restriction_injective {c d : Chart L n s F a} (h : c ⟶ d) :
    Function.Injective (restriction h) := by
  let : Nonempty (chartAffine c).1 := chart_nonempty c
  exact map_injective_of_isIntegral X h.hom

/-- The coefficient algebra action is constructed from this SAME true restriction. -/
@[instance_reducible] def restrictionAlgebra {c d : Chart L n s F a} (h : c ⟶ d) :
    Algebra (coefficientRing d) (coefficientRing c) := (restriction h).toAlgebra

/-- The actual original fraction-field extension comes from the SAME coefficient restriction. -/
def fractionMap {c d : Chart L n s F a} (h : c ⟶ d) :
    FractionRing (coefficientRing d) →+* FractionRing (coefficientRing c) := by
  letI := coefficientDomain c
  letI := restrictionAlgebra h
  exact CyclicSectionSNCInjectiveBaseChange.fractionMap (restriction_injective h)

theorem fractionMap_algebraMap {c d : Chart L n s F a} (h : c ⟶ d) (r : coefficientRing d) :
    fractionMap h (algebraMap (coefficientRing d) (FractionRing (coefficientRing d)) r) =
      algebraMap (coefficientRing c) (FractionRing (coefficientRing c)) (restriction h r) := by
  let := coefficientDomain c
  let := restrictionAlgebra h
  exact CyclicSectionSNCInjectiveBaseChange.fractionMap_algebraMap (restriction_injective h) r

/-- Actual branch and frame comparisons of the complete restricted generic algebra. -/
def genericComparison {c d : Chart L n s F a} (h : c ⟶ d) :
    letI := coefficientDomain c
    CyclicSectionSNCNormalizationRounded.GenericRootRing n a
      (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j)) ≃ₐ[coefficientRing c]
        genericRing c := by
  letI := coefficientDomain c
  exact Comparison.generic (R := coefficientRing c) n a (chartUnit c) (chartBranches c) (frameUnit h) (branchUnit h)
    (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j))
    (restricted_unit_eq_gauge_coefficient h) (branches_transition h)

/-- The actual whole generic arrow is genuine base change followed by the two derived comparisons. -/
def genericMap {c d : Chart L n s F a} (h : c ⟶ d) : genericRing d →+* genericRing c := by
  letI := coefficientDomain c
  letI := coefficientDomain d
  letI := restrictionAlgebra h
  exact (genericComparison h).toRingHom.comp
    (CyclicSectionSNCInjectiveBaseChange.genericMap (restriction_injective h)
      n a (chartUnit d) (chartBranches d)).toRingHom

/-- EVERY original fraction coefficient follows precisely the actual original fraction map. -/
theorem genericMap_fraction {c d : Chart L n s F a} (h : c ⟶ d)
    (r : FractionRing (coefficientRing d)) :
    genericMap h (algebraMap (FractionRing (coefficientRing d)) (genericRing d) r) =
      algebraMap (FractionRing (coefficientRing c)) (genericRing c) (fractionMap h r) := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := restrictionAlgebra h
  change genericComparison h
    (CyclicSectionSNCInjectiveBaseChange.genericMap (restriction_injective h) n a (chartUnit d)
      (chartBranches d) (algebraMap (FractionRing (coefficientRing d)) (genericRing d) r)) = _
  rw [CyclicSectionSNCInjectiveBaseChange.genericMap_algebraMap]
  exact Comparison.generic_fraction (R := coefficientRing c) n a (chartUnit c) (chartBranches c)
    (frameUnit h) (branchUnit h) (restriction h (chartUnit d))
    (fun j => restriction h (chartBranches d j)) (restricted_unit_eq_gauge_coefficient h)
    (branches_transition h) _

/-- The constructed actual WHOLE generic map has the original frame-unit root formula. -/
theorem genericMap_root {c d : Chart L n s F a} (h : c ⟶ d) :
    genericMap h (CyclicSectionAlgebra.root n
      (algebraMap (coefficientRing d) (FractionRing (coefficientRing d))
        ((chartUnit d : coefficientRing d) * ∏ j, chartBranches d j ^ a j))) =
      algebraMap (coefficientRing c) (genericRing c) (frameUnit h : coefficientRing c) *
        CyclicSectionAlgebra.root n
          (algebraMap (coefficientRing c) (FractionRing (coefficientRing c))
            ((chartUnit c : coefficientRing c) * ∏ j, chartBranches c j ^ a j)) := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := restrictionAlgebra h
  change genericComparison h
    (CyclicSectionSNCInjectiveBaseChange.genericMap (restriction_injective h) n a (chartUnit d)
      (chartBranches d) (CyclicSectionAlgebra.root n _)) = _
  rw [CyclicSectionSNCInjectiveBaseChange.genericMap_root]
  exact Comparison.generic_root (R := coefficientRing c) n a (chartUnit c) (chartBranches c)
    (frameUnit h) (branchUnit h) (restriction h (chartUnit d))
    (fun j => restriction h (chartBranches d j)) (restricted_unit_eq_gauge_coefficient h)
    (branches_transition h)

theorem genericMap_algebraMap {c d : Chart L n s F a} (h : c ⟶ d) (r : coefficientRing d) :
    genericMap h (algebraMap (coefficientRing d) (genericRing d) r) =
      algebraMap (coefficientRing c) (genericRing c) (restriction h r) := by
  let := coefficientDomain c
  let := coefficientDomain d
  change genericMap h (algebraMap (FractionRing (coefficientRing d)) (genericRing d)
      (algebraMap (coefficientRing d) (FractionRing (coefficientRing d)) r)) =
    algebraMap (FractionRing (coefficientRing c)) (genericRing c)
      (algebraMap (coefficientRing c) (FractionRing (coefficientRing c)) (restriction h r))
  rw [genericMap_fraction, fractionMap_algebraMap]

/-- The ENTIRE original base-coefficient square commutes as actual RingHoms. -/
theorem genericMap_coefficients {c d : Chart L n s F a} (h : c ⟶ d) :
    (genericMap h).comp (algebraMap (coefficientRing d) (genericRing d)) =
      (algebraMap (coefficientRing c) (genericRing c)).comp (restriction h) := by
  ext r
  exact genericMap_algebraMap h r

/-- Actual whole rounded comparison over the SAME source coefficient ring. -/
def roundedComparison {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    letI := coefficientDomain c
    CyclicSectionSNCNormalizationRounded.roundedAlgebra n a
      (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j)) hn
      (fun j => (map_ne_zero_iff _ (restriction_injective h)).mpr (chart_branches_nonzero d j)) ≃ₐ[coefficientRing c]
        roundedRing c hn := by
  letI := coefficientDomain c
  exact Comparison.rounded (R := coefficientRing c) n a (chartUnit c) (chartBranches c) (frameUnit h) (branchUnit h)
    (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j))
    (restricted_unit_eq_gauge_coefficient h) (branches_transition h) hn (chart_branches_nonzero c) _

/-- The actual WHOLE original rounded algebra arrow. -/
def roundedMap {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    roundedRing d hn →+* roundedRing c hn := by
  letI := coefficientDomain c
  letI := coefficientDomain d
  letI := restrictionAlgebra h
  exact (roundedComparison h hn).toRingHom.comp
    (CyclicSectionSNCInjectiveBaseChange.roundedMap (restriction_injective h)
      n a (chartUnit d) (chartBranches d) hn (chart_branches_nonzero d)).toRingHom

/-- The entire constructed rounded arrow retains its actual generic value. -/
theorem roundedMap_coe {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n)
    (x : roundedRing d hn) : (roundedMap h hn x : genericRing c) = genericMap h (x : genericRing d) := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := restrictionAlgebra h
  exact Comparison.rounded_coe (R := coefficientRing c) n a (chartUnit c) (chartBranches c) (frameUnit h) (branchUnit h)
    (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j))
    (restricted_unit_eq_gauge_coefficient h) (branches_transition h) hn (chart_branches_nonzero c) _ _

theorem roundedMap_algebraMap {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n)
    (r : coefficientRing d) :
    roundedMap h hn (algebraMap (coefficientRing d) (roundedRing d hn) r) =
      algebraMap (coefficientRing c) (roundedRing c hn) (restriction h r) := by
  apply Subtype.ext
  rw [roundedMap_coe]
  exact genericMap_algebraMap h r

/-- The ENTIRE actual rounded scalar square uses the original true restriction. -/
theorem roundedMap_coefficients {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) :
    (roundedMap h hn).comp (algebraMap (coefficientRing d) (roundedRing d hn)) =
      (algebraMap (coefficientRing c) (roundedRing c hn)).comp (restriction h) := by
  apply RingHom.ext
  intro r
  exact roundedMap_algebraMap h hn r

theorem roundedMap_smul {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n)
    (r : coefficientRing d) (x : roundedRing d hn) :
    roundedMap h hn (r • x) = restriction h r • roundedMap h hn x := by
  simp only [Algebra.smul_def, map_mul, roundedMap_algebraMap]

/-- Every SAME original rounded basis vector has its precise internally derived diagonal unit. -/
theorem roundedMap_basis {c d : Chart L n s F a} (h : c ⟶ d) (hn : 0 < n) (i : Fin n) :
    roundedMap h hn (basis d hn i) =
      (diagonalUnit h (i : ℕ) : coefficientRing c) • basis c hn i := by
  let := coefficientDomain c
  let := coefficientDomain d
  let := restrictionAlgebra h
  change roundedComparison h hn
    (CyclicSectionSNCInjectiveBaseChange.roundedMap (restriction_injective h)
      n a (chartUnit d) (chartBranches d) hn (chart_branches_nonzero d)
        (CyclicSectionSNCNormalizationRounded.basis (R := coefficientRing d) n a (chartUnit d) (chartBranches d) hn
          (chart_branches_nonzero d) i)) = _
  rw [CyclicSectionSNCInjectiveBaseChange.roundedMap_basis]
  exact Comparison.rounded_basis (R := coefficientRing c) n a (chartUnit c) (chartBranches c) (frameUnit h) (branchUnit h)
    (restriction h (chartUnit d)) (fun j => restriction h (chartBranches d j))
    (restricted_unit_eq_gauge_coefficient h) (branches_transition h) hn (chart_branches_nonzero c) _ i

end EnvelopeProperty.CyclicSectionSNCAdaptedRoundedTransitions
