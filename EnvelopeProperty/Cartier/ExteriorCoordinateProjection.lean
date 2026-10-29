import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Genuine coordinate projections on the original exterior algebra

Actual coordinate contractions and actual left wedges select the ORIGINAL exterior basis.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.ExteriorCoordinateProjection
open scoped Classical
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An actual covector annihilating EVERY original factor annihilates the actual full wedge. -/
theorem contract_wedge_eq_zero (ℓ : Module.Dual R M) (q : ℕ) (v : Fin q → M)
    (hv : ∀ j, ℓ (v j) = 0) :
    CliffordAlgebra.contractLeft (Q := 0) ℓ (ExteriorAlgebra.ιMulti R q v) = 0 := by
  induction q with
  | zero => rw [ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, hv 0,
      zero_smul, ih (Matrix.vecTail v) (fun j => hv j.succ), mul_zero, sub_zero]

/-- Prepending a factor ALREADY present in an original wedge gives zero by actual alternation. -/
theorem prepend_wedge_eq_zero (q : ℕ) (v : Fin q → M) (m : M) (h : ∃ j, v j = m) :
    ExteriorAlgebra.ι R m * ExteriorAlgebra.ιMulti R q v = 0 := by
  obtain ⟨j, hj⟩ := h
  have he : ExteriorAlgebra.ιMulti R (q+1) (Fin.cons m v) = 0 :=
    (ExteriorAlgebra.ιMulti R (q+1)).map_eq_zero_of_eq (Fin.cons m v) (i := 0) (j := j.succ)
      (by simpa only [Fin.cons_zero, Fin.cons_succ] using hj.symm) (Ne.symm (Fin.succ_ne_zero j))
  simpa only [ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero, Matrix.vecTail, Function.comp_def, Fin.cons_succ] using he

/-- The actual original exterior coordinate projection L_i C_i. -/
def projection (b : Module.Basis I R M) (i : I) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  (LinearMap.mulLeft R (ExteriorAlgebra.ι R (b i))).comp
    (CliffordAlgebra.contractLeft (Q := 0) (b.coord i))

/-- Its genuine original contraction/left-wedge complement. -/
def complement (b : Module.Basis I R M) (i : I) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  (CliffordAlgebra.contractLeft (Q := 0) (b.coord i)).comp
    (LinearMap.mulLeft R (ExteriorAlgebra.ι R (b i)))

/-- The actual two operators decompose EVERY whole original exterior-algebra element. -/
theorem complement_add_projection (b : Module.Basis I R M) (i : I) (x : ExteriorAlgebra R M) :
    complement b i x + projection b i x = x := by
  change CliffordAlgebra.contractLeft (Q := 0) (b.coord i) (ExteriorAlgebra.ι R (b i) * x) +
    ExteriorAlgebra.ι R (b i) * CliffordAlgebra.contractLeft (Q := 0) (b.coord i) x = x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

/-- The ORIGINAL coordinate projection selects exactly the ORIGINAL ordered exterior basis
wedges containing its index, and kills the other actual wedges. -/
theorem projection_wedge [LinearOrder I] (b : Module.Basis I R M) (i : I)
    (q : ℕ) (s : Set.powersetCard I q) :
    projection b i (ExteriorAlgebra.ιMulti_family R q b s) =
      if i ∈ s then ExteriorAlgebra.ιMulti_family R q b s else 0 := by
  classical
  dsimp only [ExteriorAlgebra.ιMulti_family]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
    have hw : ExteriorAlgebra.ι R (b i) *
        ExteriorAlgebra.ιMulti R q (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) = 0 :=
      prepend_wedge_eq_zero q _ (b i) ⟨j, congrArg b hj⟩
    have hc := complement_add_projection b i
      (ExteriorAlgebra.ιMulti R q (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s))
    change CliffordAlgebra.contractLeft (Q := 0) (b.coord i)
      (ExteriorAlgebra.ι R (b i) * _) + _ = _ at hc
    rw [hw, map_zero, zero_add] at hc
    exact hc
  · rw [if_neg hi]
    have hv : ∀ j : Fin q,
        (b.coord i) ((b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) j) = 0 := by
      intro j
      have hji : Set.powersetCard.ofFinEmbEquiv.symm s j ≠ i := by
        intro h
        apply hi
        exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mp ⟨j, h⟩
      simp only [Function.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne (Ne.symm hji)]
    change ExteriorAlgebra.ι R (b i) *
      CliffordAlgebra.contractLeft (Q := 0) (b.coord i)
        (ExteriorAlgebra.ιMulti R q (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) = 0
    rw [contract_wedge_eq_zero _ _ _ hv, mul_zero]

/-- The genuine complement has the complementary ORIGINAL exterior basis rule. -/
theorem complement_wedge [LinearOrder I] (b : Module.Basis I R M) (i : I)
    (q : ℕ) (s : Set.powersetCard I q) :
    complement b i (ExteriorAlgebra.ιMulti_family R q b s) =
      if i ∈ s then 0 else ExteriorAlgebra.ιMulti_family R q b s := by
  classical
  have h := complement_add_projection b i (ExteriorAlgebra.ιMulti_family R q b s)
  rw [projection_wedge] at h
  by_cases hi : i ∈ s
  · rw [if_pos hi] at h ⊢
    have he := congrArg (fun z => z - ExteriorAlgebra.ιMulti_family R q b s) h
    simpa only [add_sub_cancel_right, sub_self] using he
  · rw [if_neg hi, add_zero] at h
    rw [if_neg hi]
    exact h

/-- The ACTUAL coordinate projection is idempotent on the WHOLE original exterior algebra. -/
theorem projection_idempotent (b : Module.Basis I R M) (i : I) (x : ExteriorAlgebra R M) :
    projection b i (projection b i x) = projection b i x := by
  change ExteriorAlgebra.ι R (b i) *
    CliffordAlgebra.contractLeft (Q := 0) (b.coord i)
      (ExteriorAlgebra.ι R (b i) * CliffordAlgebra.contractLeft (Q := 0) (b.coord i) x) = _
  rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_contractLeft]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    one_smul, mul_zero, sub_zero]
  rfl

/-- The genuine complementary projection is idempotent on EVERY original element. -/
theorem complement_idempotent (b : Module.Basis I R M) (i : I) (x : ExteriorAlgebra R M) :
    complement b i (complement b i x) = complement b i x := by
  have h := complement_add_projection b i x
  have hp : complement b i x = x - projection b i x := eq_sub_iff_add_eq.mpr h
  rw [hp, map_sub]
  have h2 := complement_add_projection b i (projection b i x)
  rw [projection_idempotent] at h2
  have hz : complement b i (projection b i x) = 0 := by
    have he := congrArg (fun z => z - projection b i x) h2
    simpa only [add_sub_cancel_right, sub_self] using he
  rw [hz, sub_zero]
  exact hp

end EnvelopeProperty.Cartier.ExteriorCoordinateProjection
