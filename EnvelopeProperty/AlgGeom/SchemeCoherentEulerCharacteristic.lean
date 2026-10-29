import EnvelopeProperty.AlgGeom.SchemeCoherentEulerExact
import EnvelopeProperty.AlgGeom.CohomologyFiniteEuler

/-! # Intrinsic full coherent Euler characteristic, with genuinely derived bounds -/
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules TopCat TopCat.Sheaf
noncomputable section
universe u
namespace EnvelopeProperty.SchemeCoherentEulerCharacteristic
open SchemeCoherentEulerIndex SchemeCoherentEulerExact
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The true field Cech homology vanishes above the actual finite-cover cardinality. -/
theorem fieldCech_isZero_of_card_le (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (n : ℕ) (hn : Nat.card ι ≤ n) :
    IsZero (fieldCech f M U n) := by
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have ho : IsZero ((orderedBaseCechComplex f M U).homology n) :=
    (orderedBaseCechComplex_exactAt_of_card_le f M U n
      (by simpa only [Nat.card_eq_fintype_card] using hn)).isZero_homology
  have hb := IsZero.of_iso ho (baseCechOrderedHomologyIso f M U n)
  exact (ModuleCat.restrictScalars (baseScalar (k := k))).map_isZero hb

/-- Original projective coherent geometry derives finite-dimensionality in EVERY actual degree. -/
theorem fieldCech_finite (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) (n : ℕ) : Module.Finite k (fieldCech f M U n) := by
  cases n with
  | zero =>
    let : Module.Finite k (fieldSections f M) := fieldSections_finite f hf M
    exact Module.Finite.equiv (fieldSectionsCechZeroIso f M U hU).toLinearEquiv
  | succ n => exact fieldCech_succ_finite f hf M U hU hUa n

/-- The actual alternating sum on the specified original field-linear cover. -/
def coverEuler (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range N, (-1 : ℤ)^i * Module.finrank k (fieldCech f M U i)

/-- Increasing the actual finite-cover bound adds only genuinely zero original cohomology groups. -/
theorem coverEuler_eq_of_card_le (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) {N P : ℕ}
    (hN : Nat.card ι ≤ N) (hNP : N ≤ P) : coverEuler f M U N = coverEuler f M U P := by
  unfold coverEuler
  apply Finset.sum_subset (Finset.range_mono hNP)
  intro n _ hn
  have hcard : Nat.card ι ≤ n := hN.trans (by simpa using hn)
  let : Subsingleton (fieldCech f M U n) :=
    ModuleCat.subsingleton_of_isZero (fieldCech_isZero_of_card_le f M U n hcard)
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

/-- Every original finite affine cover has the same cohomology dimensions in every degree. -/
theorem fieldCech_finrank_eq_of_affine_openCovers [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (M : X.Modules) [M.IsQuasicoherent]
    {ι κ : Type u} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (V : κ → X.Opens) (hV : IsOpenCover V) (hVa : ∀ i, IsAffineOpen (V i)) (n : ℕ) :
    Module.finrank k (fieldCech f M U n) = Module.finrank k (fieldCech f M V n) := by
  cases n with
  | zero => exact ((fieldSectionsCechZeroIso f M U hU).symm ≪≫
      fieldSectionsCechZeroIso f M V hV).toLinearEquiv.finrank_eq
  | succ n => exact (fieldCechCoverIso f M U hU hUa V hV hVa n).toLinearEquiv.finrank_eq

/-- The full original coherent Euler characteristic uses a DERIVED actual finite affine-cover bound. -/
def eulerCharacteristic [CompactSpace X] (f : X ⟶ Spec (.of k)) (M : X.Modules) : ℤ :=
  coverEuler f M (finiteAffineOpens X) (Nat.card (finiteAffineCover X).I₀ + 1)

/-- The normalized full Euler characteristic uses the SAME original module and original structure line. -/
def normalizedEulerCharacteristic [CompactSpace X] (f : X ⟶ Spec (.of k)) (M : X.Modules) : ℤ :=
  eulerCharacteristic f M - eulerCharacteristic f (unitObj X)

/-- Every actual finite affine cover with its derived bound computes the SAME intrinsic characteristic. -/
theorem eulerCharacteristic_eq_on_cover [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) :
    eulerCharacteristic f M = coverEuler f M U (Nat.card ι + 1) := by
  let P := max (Nat.card (finiteAffineCover X).I₀ + 1) (Nat.card ι + 1)
  rw [eulerCharacteristic,
    coverEuler_eq_of_card_le f M (finiteAffineOpens X) (by omega)
      (show Nat.card (finiteAffineCover X).I₀+1 ≤ P from le_max_left _ _),
    coverEuler_eq_of_card_le f M U (by omega)
      (show Nat.card ι+1 ≤ P from le_max_right _ _)]
  apply Finset.sum_congr rfl
  intro n _
  rw [fieldCech_finrank_eq_of_affine_openCovers f M
    (finiteAffineOpens X) (finiteAffineOpens_cover X) (finiteAffineOpens_isAffine X) U hU hUa n]

/-- Actual whole original module isomorphisms preserve the full coherent Euler characteristic. -/
theorem eulerCharacteristic_eq_of_iso [CompactSpace X] (f : X ⟶ Spec (.of k))
    {M N : X.Modules} (e : M ≅ N) : eulerCharacteristic f M = eulerCharacteristic f N := by
  unfold eulerCharacteristic coverEuler
  apply Finset.sum_congr rfl
  intro n _
  rw [(fieldCechIso f e (finiteAffineOpens X) n).toLinearEquiv.finrank_eq]

/-- The normalized original full index is invariant under actual whole line/module isomorphisms. -/
theorem normalizedEulerCharacteristic_eq_of_iso [CompactSpace X] (f : X ⟶ Spec (.of k))
    {M N : X.Modules} (e : M ≅ N) :
    normalizedEulerCharacteristic f M = normalizedEulerCharacteristic f N := by
  unfold normalizedEulerCharacteristic
  rw [eulerCharacteristic_eq_of_iso f e]

@[simp] theorem normalizedEulerCharacteristic_unit [CompactSpace X] (f : X ⟶ Spec (.of k)) :
    normalizedEulerCharacteristic f (unitObj X) = 0 := sub_self _

/-- The whole original field-linear complex computes the same actual finite Euler sum. -/
theorem coverEuler_eq_partialEuler (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (N : ℕ) :
    coverEuler f M U N = CohomologyFiniteEuler.partialEuler ((fieldComplexFunctor f U).obj M) N := by
  apply Finset.sum_congr rfl
  intro n _
  rw [(fieldComplexHomologyIso f M U n).toLinearEquiv.finrank_eq]

/-- Actual original coherent Euler additivity has NO vanishing assumption:
all finiteness, affine exactness and terminal vanishing are genuinely derived. -/
theorem eulerCharacteristic_add [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [S.X₁.IsFiniteType] [S.X₂.IsFiniteType] [S.X₃.IsFiniteType] :
    eulerCharacteristic f S.X₂ = eulerCharacteristic f S.X₁ + eulerCharacteristic f S.X₃ := by
  let U := finiteAffineOpens X
  let F := fieldComplexFunctor f U
  have hU := finiteAffineOpens_cover X
  have hUa := finiteAffineOpens_isAffine X
  have hfinite (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
      Module.Finite k (((fieldComplexFunctor f U).obj M).homology n) := by
    let : Module.Finite k (fieldCech f M U n) := fieldCech_finite f hf M U hU hUa n
    exact Module.Finite.equiv (fieldComplexHomologyIso f M U n).symm.toLinearEquiv
  let : ∀ n, Module.Finite k (((S.map F).X₁).homology n) := hfinite S.X₁
  let : ∀ n, Module.Finite k (((S.map F).X₂).homology n) := hfinite S.X₂
  let : ∀ n, Module.Finite k (((S.map F).X₃).homology n) := hfinite S.X₃
  have hfield : (S.map F).ShortExact :=
    (hS.map_baseCechComplexFunctor_of_affine_openCover f U hUa).map_of_exact
      ((ModuleCat.restrictScalars (baseScalar (k := k))).mapHomologicalComplex (.up ℕ))
  have hzero : IsZero ((S.map F).X₁.homology (Nat.card (finiteAffineCover X).I₀+1)) :=
    IsZero.of_iso (fieldCech_isZero_of_card_le f S.X₁ U _ (by omega))
      (fieldComplexHomologyIso f S.X₁ U _)
  unfold eulerCharacteristic
  rw [coverEuler_eq_partialEuler, coverEuler_eq_partialEuler, coverEuler_eq_partialEuler]
  exact CohomologyFiniteEuler.partialEuler_add (S.map F) hfield _ hzero

end EnvelopeProperty.SchemeCoherentEulerCharacteristic
