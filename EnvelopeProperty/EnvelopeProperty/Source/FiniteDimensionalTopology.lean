import EnvelopeProperty.Source.PSH
import EnvelopeProperty.AlgGeom.NativeNumericalFiniteSpanTopology

/-! # Ample-cone convergence is Euclidean convergence when `N¹(X)_ℝ` is finite dimensional

BJ22 works in the finite dimensional real vector space `Num(X) = N¹(X)_ℝ` (`bj22-trivval`,
conventions), in which the ample cone is open. The finite dimensionality (Néron–Severi) is not
formalized; this file proves that, **assuming** `[FiniteDimensional ℝ (Space p)]`, the order
convergence `Variety.AmpleTendsto` used in `Variety.IsPSH` is the convergence of the (unique
Hausdorff vector space, here the curve-weak) topology of `N¹(X)_ℝ`, so that `Variety.IsPSH` is
literally BJ22 Definition 4.1 (`bj22-trivval:defi:psh`):

* `Variety.isOpen_ampleCone`: the ample cone is open. Write a basis of `N¹(X)_ℝ` with finitely
  many line classes; the resulting finite line family has a surjective coefficient map, which is
  open (finite dimensional target), and the preimage of the ample cone is open
  (`NativeRealNumericalClasses.isOpen_lineFamilyMap_preimage_ampleCone`).
* `Variety.ampleTendsto_iff_tendsto`: if `c → θ` then `c - θ → 0`, and for ample `η` the set
  `{x | η + x, η - x ∈ Amp(X)}` is an open neighbourhood of `0`. The converse is
  `Variety.AmpleTendsto.tendsto` (no finite dimensionality needed).
* `Variety.isPSH_iff_isCurveWeakPSH`: `Variety.IsPSH` agrees with Codex's
  `NativeNumericalFubiniStudy.IsCurveWeakPSH`, which is BJ22 Definition 4.1 with convergence in
  the topology of `N¹(X)_ℝ`.

The hypothesis `[FiniteDimensional ℝ (Space p)]` is an explicit assumption of the statements of
this file only; nothing else depends on it.
-/

open AlgebraicGeometry CategoryTheory Filter Topology Scheme.Modules
open scoped NNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty.Variety

open NativeRealNumericalClasses

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]
  [IsIntegral X]

/-- **The ample cone is open** if `N¹(X)_ℝ` is finite dimensional
(`lem:var-ample-cone-open-fd`). -/
theorem isOpen_ampleCone [FiniteDimensional ℝ (Space p)] :
    IsOpen (ampleCone p : Set (Space p)) := by
  classical
  let b := Module.finBasis ℝ (Space p)
  choose n L hL c hc using fun i => exists_finite_line_family p (b i)
  let L' : (Σ i, Fin (n i)) → X.Modules := fun x => L x.1 x.2
  let hL' : ∀ x, IsInvertible (L' x) := fun x => hL x.1 x.2
  let F := lineFamilyMap p L' hL'
  have hgen (x : Σ i, Fin (n i)) : lineClass p (L' x) (hL' x) ∈ LinearMap.range F := by
    refine LinearMap.mem_range.mpr ⟨Pi.single x 1, ?_⟩
    change ∑ y, (Pi.single x 1 : (Σ i, Fin (n i)) → ℝ) y • lineClass p (L' y) (hL' y) = _
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Pi.single_eq_of_ne hy]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have hbasis (i : Fin (Module.finrank ℝ (Space p))) : b i ∈ LinearMap.range F := by
    rw [hc i, lineFamilyMap_apply]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hgen ⟨i, t⟩)
  have htop : LinearMap.range F = ⊤ := by
    apply top_le_iff.mp
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbasis i)
  have hsurj : Function.Surjective F := LinearMap.range_eq_top.mp htop
  have himg : F '' (F ⁻¹' (ampleCone p : Set (Space p))) = ampleCone p :=
    Set.image_preimage_eq _ hsurj
  rw [← himg]
  exact LinearMap.isOpenMap_of_finiteDimensional F hsurj _
    (isOpen_lineFamilyMap_preimage_ampleCone p L' hL')

variable {p} in
/-- **Ample-cone convergence is topological convergence** if `N¹(X)_ℝ` is finite dimensional
(`thm:var-ample-convergence-fd`). -/
theorem ampleTendsto_iff_tendsto [FiniteDimensional ℝ (Space p)] {J : Type*}
    {c : J → Space p} {l : Filter J} {θ : Space p} :
    AmpleTendsto p c l θ ↔ Tendsto c l (𝓝 θ) := by
  refine ⟨AmpleTendsto.tendsto, fun h η hη => ?_⟩
  have hopen := isOpen_ampleCone p
  have h₀ : Tendsto (fun j => c j - θ) l (𝓝 0) := by
    simpa only [sub_self] using h.sub_const θ
  have hc₁ : Continuous fun x : Space p => η + x := continuous_const.add continuous_id
  have hc₂ : Continuous fun x : Space p => η - x := continuous_const.sub continuous_id
  have hU : {x : Space p | η + x ∈ ampleCone p ∧ η - x ∈ ampleCone p} ∈ 𝓝 (0 : Space p) := by
    refine IsOpen.mem_nhds ((hopen.preimage hc₁).inter (hopen.preimage hc₂)) ?_
    change η + 0 ∈ ampleCone p ∧ η - 0 ∈ ampleCone p
    rw [add_zero, sub_zero]
    exact ⟨hη, hη⟩
  exact h₀.eventually hU

/-- **`Variety.IsPSH` is BJ22 Definition 4.1** with the topology of `N¹(X)_ℝ`, if `N¹(X)_ℝ` is
finite dimensional (`cor:var-psh-curve-weak-fd`). -/
theorem isPSH_iff_isCurveWeakPSH [FiniteDimensional ℝ (Space p)] (θ : Space p)
    (φ : An p → EReal) :
    IsPSH p θ φ ↔ NativeNumericalFubiniStudy.IsCurveWeakPSH p θ φ := by
  constructor
  · exact IsPSH.isCurveWeakPSH
  · rintro ⟨hfin, husc, J, hJ, hdir, hne, D, hD, hconv, hanti, he⟩
    exact ⟨hfin, husc, J, hJ, hdir, hne, D, hD, ampleTendsto_iff_tendsto.mpr hconv, hanti, he⟩

end EnvelopeProperty.Variety
