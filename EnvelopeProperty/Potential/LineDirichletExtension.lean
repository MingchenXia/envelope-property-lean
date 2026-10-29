import EnvelopeProperty.Potential.LineDirichlet
import EnvelopeProperty.Potential.LineHarmonicAlgebra

/-! # Actual harmonic extension, order bounds and exact extended-real boundary splitting -/
open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

/-- Two extended-real values below a finite sum bound admit an exact finite split. -/
theorem exists_real_boundary_split (a b : EReal) (c : ℝ) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hsum : a+b ≤ (c : EReal)) :
    ∃ d : ℝ, a ≤ (d : EReal) ∧ b ≤ ((c-d : ℝ) : EReal) := by
  by_cases haB : a = ⊥
  · refine ⟨c-b.toReal,?_,?_⟩
    · simp [haB]
    · simpa only [sub_sub_cancel] using EReal.le_coe_toReal hb
  · refine ⟨a.toReal,(EReal.coe_toReal ha haB).symm.le,?_⟩
    have hs : b+(a.toReal : EReal) ≤ (c : EReal) := by
      simpa only [EReal.coe_toReal ha haB,add_comm] using hsum
    have h := (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot a.toReal)) (Or.inl (EReal.coe_ne_top a.toReal))).2 hs
    simpa only [EReal.coe_sub] using h

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The actual harmonic extension of data on the set of distinct Gauss boundary points. -/
def dirichletExtension (β : U.boundary → ℝ) : U.carrier → ℝ :=
  (U.exists_isHarmonic_boundary_values β).choose

theorem isHarmonic_dirichletExtension (β : U.boundary → ℝ) :
    U.IsHarmonic (U.dirichletExtension β) :=
  (U.exists_isHarmonic_boundary_values β).choose_spec.1

theorem dirichletExtension_boundary (β : U.boundary → ℝ) (z : U.boundary) :
    U.dirichletExtension β ⟨z.1,U.boundary_subset z.2⟩ = β z :=
  (U.exists_isHarmonic_boundary_values β).choose_spec.2 z

theorem dirichletExtension_eq_of_boundary (β : U.boundary → ℝ) (h : U.carrier → ℝ)
    (hh : U.IsHarmonic h)
    (hB : ∀ z : U.boundary, h ⟨z.1,U.boundary_subset z.2⟩ = β z) :
    U.dirichletExtension β = h := by
  apply IsHarmonic.eq_of_boundary U (U.isHarmonic_dirichletExtension β) hh
  intro z hz
  exact (U.dirichletExtension_boundary β ⟨z.1,hz⟩).trans (hB ⟨z.1,hz⟩).symm

theorem dirichletExtension_const (c : ℝ) :
    U.dirichletExtension (fun _ => c) = fun _ => c :=
  U.dirichletExtension_eq_of_boundary _ _ (IsHarmonic.const U c) (fun _ => rfl)

theorem dirichletExtension_add (β δ : U.boundary → ℝ) :
    U.dirichletExtension (β+δ) = U.dirichletExtension β+U.dirichletExtension δ := by
  apply U.dirichletExtension_eq_of_boundary _ _
    ((U.isHarmonic_dirichletExtension β).add U (U.isHarmonic_dirichletExtension δ))
  intro z
  simp only [Pi.add_apply,U.dirichletExtension_boundary]

theorem dirichletExtension_smul (c : ℝ) (β : U.boundary → ℝ) :
    U.dirichletExtension (c • β) = c • U.dirichletExtension β := by
  apply U.dirichletExtension_eq_of_boundary _ _
    ((U.isHarmonic_dirichletExtension β).smul U c)
  intro z
  simp only [Pi.smul_apply,U.dirichletExtension_boundary]

/-- Real linearity belongs to the constructed actual solution operator. -/
def dirichletExtensionLinearMap : (U.boundary → ℝ) →ₗ[ℝ] (U.carrier → ℝ) where
  toFun := U.dirichletExtension
  map_add' := U.dirichletExtension_add
  map_smul' := U.dirichletExtension_smul

theorem continuous_dirichletExtension (β : U.boundary → ℝ) :
    Continuous (U.dirichletExtension β) :=
  IsHarmonic.continuous U (U.isHarmonic_dirichletExtension β)

/-- Actual harmonic boundary order propagates to every point of the affinoid. -/
theorem IsHarmonic.le_of_boundary_le {h k : U.carrier → ℝ} (hh : U.IsHarmonic h)
    (hk : U.IsHarmonic k) (hB : ∀ z : U.carrier, z.1 ∈ U.boundary → h z ≤ k z) :
    h ≤ k := by
  obtain ⟨c,γ,hγ⟩ := hh.sub U hk
  intro x
  obtain ⟨z,hz,hxz⟩ := U.harmonicExpression_exists_boundary_ge c γ x.2
  have he := hγ ⟨z,U.boundary_subset hz⟩
  have hx := hγ x
  have hzle := hB ⟨z,U.boundary_subset hz⟩ hz
  simp only [Pi.sub_apply] at he hx
  linarith

theorem dirichletExtension_mono {β δ : U.boundary → ℝ} (hβδ : β ≤ δ) :
    U.dirichletExtension β ≤ U.dirichletExtension δ := by
  apply IsHarmonic.le_of_boundary_le U (U.isHarmonic_dirichletExtension β)
    (U.isHarmonic_dirichletExtension δ)
  intro z hz
  simpa only [U.dirichletExtension_boundary β ⟨z.1,hz⟩,
    U.dirichletExtension_boundary δ ⟨z.1,hz⟩] using hβδ ⟨z.1,hz⟩

theorem dirichletExtension_abs_le (β : U.boundary → ℝ) (C : ℝ)
    (hB : ∀ z, |β z| ≤ C) (x : U.carrier) : |U.dirichletExtension β x| ≤ C := by
  have hlow : (fun _ => -C) ≤ β := fun z => (abs_le.mp (hB z)).1
  have hupp : β ≤ fun _ => C := fun z => (abs_le.mp (hB z)).2
  have hl := U.dirichletExtension_mono hlow x
  have hu := U.dirichletExtension_mono hupp x
  rw [U.dirichletExtension_const] at hl hu
  exact abs_le.mpr ⟨hl,hu⟩

theorem dirichletExtension_sub_abs_le (β δ : U.boundary → ℝ) (C : ℝ)
    (hB : ∀ z, |β z-δ z| ≤ C) (x : U.carrier) :
    |U.dirichletExtension β x-U.dirichletExtension δ x| ≤ C := by
  have h := U.dirichletExtension_abs_le (β-δ) C hB x
  change |U.dirichletExtensionLinearMap (β-δ) x| ≤ C at h
  rw [map_sub] at h
  exact h

/-- Exact harmonic splitting of finite-above extended-real boundary data, allowing both values bottom. -/
theorem exists_isHarmonic_boundary_split (u v : U.boundary → EReal) (b : U.boundary → ℝ)
    (hu : ∀ z, u z ≠ ⊤) (hv : ∀ z, v z ≠ ⊤)
    (hsum : ∀ z, u z+v z ≤ (b z : EReal)) :
    ∃ H : U.carrier → ℝ, U.IsHarmonic H ∧
      ∀ z : U.boundary, u z ≤ (H ⟨z.1,U.boundary_subset z.2⟩ : EReal) ∧
        v z ≤ ((b z-H ⟨z.1,U.boundary_subset z.2⟩ : ℝ) : EReal) := by
  choose β hβ using fun z => exists_real_boundary_split (u z) (v z) (b z) (hu z) (hv z) (hsum z)
  refine ⟨U.dirichletExtension β,U.isHarmonic_dirichletExtension β,?_⟩
  intro z
  simpa only [U.dirichletExtension_boundary] using hβ z

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
