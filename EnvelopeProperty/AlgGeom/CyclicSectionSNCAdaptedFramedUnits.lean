import EnvelopeProperty.AlgGeom.CyclicSectionSNCAdaptedFramedAtlas
import EnvelopeProperty.AlgGeom.CyclicSectionSNCComponentOverlapUnits
import EnvelopeProperty.AlgGeom.CyclicSectionSNCBranchUnitGauge

/-! # Actual original chart component units and their full coefficient law

The SAME-component overlap producer supplies the actual canonical units.
Their original overlap laws and the actual original frame coefficient law
derive all identities, composition and the actual combined coefficient.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.CyclicSectionSNCAdaptedFramedUnits
open CyclicSectionSNCAdaptedFramedAtlas CyclicSectionSNCComponentOverlapUnits

private theorem mul_four_swap {G : Type*} [CommMonoid G] (x y z w : G) :
    (x * y) * (z * w) = (x * w) * (y * z) := by ac_rfl

variable {X : Scheme.{u}} [IsIntegral X]
variable {L : X.Modules} {n : ℕ} {s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L n}
variable {F : Scheme.DivisorFamily X} {a : F.ι → ℕ}

/-- The SAME actual component unit, in the target-to-source arrow direction. -/
def branchUnit {c d : Chart L n s F a} (h : c ⟶ d) (i : F.ι) :
    (Γ(X, (chartAffine c).1))ˣ :=
  overlapUnit F (chartAffine d) (chartAffine c) (chartAffine c) (chart_nonempty c)
    h.hom.le le_rfl (chartBranches d) (chartBranches c)
    (chart_branches_ideal d) (chart_branches_ideal c)
    (chart_branches_nonzero d) (chart_branches_nonzero c) i

/-- The canonical original unit compares the actual original equations on the whole source chart. -/
theorem branchUnit_spec {c d : Chart L n s F a} (h : c ⟶ d) (i : F.ι) :
    X.presheaf.map h.hom.op (chartBranches d i) =
      (branchUnit h i : Γ(X, (chartAffine c).1)) * chartBranches c i := by
  have hv := overlapUnit_spec F (chartAffine d) (chartAffine c) (chartAffine c)
    (chart_nonempty c) h.hom.le le_rfl (chartBranches d) (chartBranches c)
    (chart_branches_ideal d) (chart_branches_ideal c)
    (chart_branches_nonzero d) (chart_branches_nonzero c) i
  rw [show X.presheaf.map (homOfLE h.hom.le).op = X.presheaf.map h.hom.op from
    X.presheaf.congr_map (Subsingleton.elim _ _)] at hv
  simpa only [branchUnit, show (homOfLE (le_rfl : (chartAffine c).1 ≤ (chartAffine c).1)).op =
      𝟙 (op (chartAffine c).1) from Subsingleton.elim _ _,
    X.presheaf.map_id, CommRingCat.hom_id, RingHom.id_apply] using hv

theorem branchUnit_id (c : Chart L n s F a) (i : F.ι) : branchUnit (𝟙 c) i = 1 :=
  overlapUnit_self F (chartAffine c) (chartAffine c) (chart_nonempty c) le_rfl
    (chartBranches c) (chart_branches_ideal c) (chart_branches_nonzero c) i

/-- Whole actual component-unit composition uses the TRUE original restriction map. -/
theorem branchUnit_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) (i : F.ι) :
    branchUnit (h ≫ k) i = branchUnit h i *
      Units.map (X.presheaf.map h.hom.op).hom.toMonoidHom (branchUnit k i) := by
  have hm := overlapUnit_mul F (chartAffine e) (chartAffine d) (chartAffine c)
    (chart_nonempty c) (h.hom.le.trans k.hom.le) h.hom.le
    (chartBranches e) (chartBranches d) (chart_branches_ideal e) (chart_branches_ideal d)
    (chart_branches_nonzero e) (chart_branches_nonzero d)
    (chartAffine c) le_rfl (chartBranches c) (chart_branches_ideal c)
    (chart_branches_nonzero c) i
  have hr := overlapUnit_restrict F (chartAffine e) (chartAffine d) (chartAffine d)
    (chart_nonempty d) k.hom.le le_rfl (chartBranches e) (chartBranches d)
    (chart_branches_ideal e) (chart_branches_ideal d)
    (chart_branches_nonzero e) (chart_branches_nonzero d)
    (chartAffine c) (chart_nonempty c) h.hom.le i
  rw [show X.presheaf.map (homOfLE h.hom.le).op = X.presheaf.map h.hom.op from
    X.presheaf.congr_map (Subsingleton.elim _ _)] at hr
  unfold branchUnit
  rw [← hm, ← hr]
  exact mul_comm _ _

/-- The actual restricted full family is exactly its internally derived SAME-index unit gauge. -/
theorem branches_transition {c d : Chart L n s F a} (h : c ⟶ d) :
    (fun i => X.presheaf.map h.hom.op (chartBranches d i)) =
      CyclicSectionSNCBranchUnitGauge.branches (chartBranches c) (branchUnit h) := by
  funext i
  exact branchUnit_spec h i

/-- Original component and frame laws derive the WHOLE unit coefficient relation internally. -/
theorem factorUnit_transition {c d : Chart L n s F a} (h : c ⟶ d) :
    Units.map (X.presheaf.map h.hom.op).hom.toMonoidHom (chartUnit d) *
        CyclicSectionSNCBranchUnitGauge.productUnit a (branchUnit h) =
      frameUnit h ^ n * chartUnit c := by
  let : Nonempty (chartAffine c).1 := chart_nonempty c
  have hP : (∏ i, chartBranches c i ^ a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (chart_branches_nonzero c i)
  apply Units.ext
  apply mul_right_cancel₀ hP
  have hc := coefficient_transition h
  rw [chart_coefficient_eq d, chart_coefficient_eq c, map_mul, map_prod] at hc
  simp_rw [map_pow, branchUnit_spec h, mul_pow] at hc
  rw [Finset.prod_mul_distrib] at hc
  simpa [CyclicSectionSNCBranchUnitGauge.productUnit_coe, mul_assoc] using hc

/-- The actual mapped affine scalar is precisely the combined original frame/component gauge scalar. -/
theorem restricted_unit_eq_gauge_coefficient {c d : Chart L n s F a} (h : c ⟶ d) :
    X.presheaf.map h.hom.op (chartUnit d : Γ(X, (chartAffine d).1)) =
      CyclicSectionSNCBranchUnitGauge.coefficient a
        ((frameUnit h : Γ(X, (chartAffine c).1)) ^ n * chartUnit c) (branchUnit h) := by
  have hu : Units.map (X.presheaf.map h.hom.op).hom.toMonoidHom (chartUnit d) =
      (frameUnit h ^ n * chartUnit c) *
        (CyclicSectionSNCBranchUnitGauge.productUnit a (branchUnit h))⁻¹ := by
    apply eq_mul_inv_iff_mul_eq.mpr
    exact factorUnit_transition h
  simpa [CyclicSectionSNCBranchUnitGauge.coefficient] using congrArg (fun v : (Γ(X, (chartAffine c).1))ˣ => (v : Γ(X, (chartAffine c).1))) hu

/-- The actual unit multiplying each original rounded vector under the original chart arrow. -/
def diagonalUnit {c d : Chart L n s F a} (h : c ⟶ d) (i : ℕ) :
    (Γ(X, (chartAffine c).1))ˣ :=
  frameUnit h ^ i *
    (CyclicSectionSNCBranchUnitGauge.productUnit (fun j => i * a j / n) (branchUnit h))⁻¹

theorem diagonalUnit_id (c : Chart L n s F a) (i : ℕ) : diagonalUnit (𝟙 c) i = 1 := by
  have he : branchUnit (𝟙 c) = fun _ => 1 := funext fun j => branchUnit_id c j
  simp only [diagonalUnit, frameUnit_id, he,
    CyclicSectionSNCBranchUnitGauge.productUnit_one, one_pow, inv_one, mul_one]

omit [IsIntegral X] in
private theorem productUnit_map {U W : X.Opens} (ρ : Γ(X, U) →+* Γ(X, W))
    (e : F.ι → ℕ) (ε : F.ι → (Γ(X, U))ˣ) :
    Units.map ρ.toMonoidHom (CyclicSectionSNCBranchUnitGauge.productUnit e ε) =
      CyclicSectionSNCBranchUnitGauge.productUnit e (fun j => Units.map ρ.toMonoidHom (ε j)) := by
  simp only [CyclicSectionSNCBranchUnitGauge.productUnit, map_prod, map_pow]

/-- The original rounded-vector diagonal obeys its whole actual restriction cocycle. -/
theorem diagonalUnit_comp {c d e : Chart L n s F a} (h : c ⟶ d) (k : d ⟶ e) (i : ℕ) :
    diagonalUnit (h ≫ k) i = diagonalUnit h i *
      Units.map (X.presheaf.map h.hom.op).hom.toMonoidHom (diagonalUnit k i) := by
  have he : branchUnit (h ≫ k) = fun j => branchUnit h j *
      Units.map (X.presheaf.map h.hom.op).hom.toMonoidHom (branchUnit k j) :=
    funext fun j => branchUnit_comp h k j
  simp only [diagonalUnit, frameUnit_comp, he,
    CyclicSectionSNCBranchUnitGauge.productUnit_mul, mul_pow, mul_inv_rev,
    map_mul, map_pow, map_inv, productUnit_map]
  exact mul_four_swap _ _ _ _

end EnvelopeProperty.CyclicSectionSNCAdaptedFramedUnits
