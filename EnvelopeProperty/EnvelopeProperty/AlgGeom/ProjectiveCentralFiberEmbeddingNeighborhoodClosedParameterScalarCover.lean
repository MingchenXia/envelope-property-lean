import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeAmple
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Actual finite scalar translates of the same original parameter open

The cover is on the entire scheme, not only coefficient-field points.
No model action, generator, eigenbasis or desired generation certificate is input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedParameterScalarCover
variable {k : Type u} [Field k]

/-- Literal original parameter scaling t ↦ u*t on the SAME affine line. -/
def parameterScalarMap (u : kˣ) : Spec (.of k[X]) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (u : k) * Polynomial.X)))

/-- Entire native inverse image is the actual original scaled polynomial open. -/
theorem parameterScalarMap_preimage (u : kˣ) (g : k[X]) :
    parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g =
      PrimeSpectrum.basicOpen (g.comp (Polynomial.C (u : k) * Polynomial.X)) := rfl

variable [Infinite k]

private theorem exists_scalar_notMem (g : k[X]) (hg : g.eval 0 ≠ 0)
    (x : PrimeSpectrum k[X]) :
    ∃ u : kˣ, g.comp (Polynomial.C (u : k) * Polynomial.X) ∉ x.asIdeal := by
  classical
  by_contra h
  push Not at h
  let : Fact x.asIdeal.IsPrime := ⟨x.isPrime⟩
  let A := k[X] ⧸ x.asIdeal
  let ρ : k[X] →+* A := Ideal.Quotient.mk x.asIdeal
  let c : k →+* A := ρ.comp Polynomial.C
  let t : A := ρ Polynomial.X
  let q : A[X] := (g.map c).comp (Polynomial.C t * Polynomial.X)
  have hρ : Polynomial.eval₂RingHom c t = ρ := by
    apply Polynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ c t (Polynomial.C a) = _
      rw [Polynomial.eval₂_C]
      rfl
    · change Polynomial.eval₂ c t Polynomial.X = _
      rw [Polynomial.eval₂_X]
  have hz (u : kˣ) : q.eval (c (u : k)) = 0 := by
    have hm : ρ (g.comp (Polynomial.C (u : k) * Polynomial.X)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (h u)
    calc
      q.eval (c (u : k)) = (g.map c).eval (t * c (u : k)) := by
        simp only [q, Polynomial.eval_comp, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X]
      _ = (g.map c).eval (c (u : k) * t) :=
        congrArg (fun z : A => (g.map c).eval z) (mul_comm _ _)
      _ = g.eval₂ c (c (u : k) * t) := Polynomial.eval_map _ _
      _ = (g.comp (Polynomial.C (u : k) * Polynomial.X)).eval₂ c t := by
        rw [Polynomial.eval₂_comp, Polynomial.eval₂_mul,
          Polynomial.eval₂_C, Polynomial.eval₂_X]
      _ = ρ (g.comp (Polynomial.C (u : k) * Polynomial.X)) :=
        RingHom.congr_fun hρ _
      _ = 0 := hm
  have hc : Function.Injective c := c.injective
  have hi : Set.Infinite {a : k | a ≠ 0} := by
    have he : ({(0 : k)} : Set k)ᶜ = {a : k | a ≠ 0} := by
      ext a
      simp
    exact he ▸ (Set.finite_singleton (0 : k)).infinite_compl
  have himage : (c '' {a : k | a ≠ 0}).Infinite := hi.image hc.injOn
  have hroot : Set.Infinite {a : A | q.IsRoot a} := himage.mono (by
    rintro _ ⟨a, ha, rfl⟩
    exact hz (Units.mk0 a ha))
  have hq : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q hroot
  have hzero : c (g.eval 0) = 0 := by
    simpa [q] using congrArg (Polynomial.eval (0 : A)) hq
  exact hg (hc (hzero.trans c.map_zero.symm))

private theorem scalarOpens_cover (g : k[X]) (hg : g.eval 0 ≠ 0) :
    (⨆ u : kˣ, parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨u, hu⟩ := exists_scalar_notMem g hg x
  apply Opens.mem_iSup.mpr
  refine ⟨u, ?_⟩
  change x ∈ parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g
  rw [parameterScalarMap_preimage]
  exact hu

/-- Finitely many literal nonzero scalar translates of the SAME D(g)
cover the ENTIRE original parameter scheme, including every nonclosed point. -/
theorem exists_finite_parameterScalar_cover (g : k[X]) (hg : g.eval 0 ≠ 0) :
    ∃ T : Finset kˣ,
      (⨆ u ∈ T, parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g) = ⊤ := by
  classical
  let V : kˣ → Set (Spec (.of k[X])) :=
    fun u => (parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g : Set (Spec (.of k[X])))
  have hcover : Set.univ ⊆ ⋃ u, V u := by
    intro x _
    have hx : x ∈ ⨆ u : kˣ, parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g := by
      rw [scalarOpens_cover g hg]
      trivial
    obtain ⟨u, hu⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨u, hu⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover V
    (fun u => (parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g).isOpen) hcover
  refine ⟨T, top_unique ?_⟩
  intro x _
  obtain ⟨u, huT, hx⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨u, Opens.mem_iSup.mpr ⟨huT, hx⟩⟩

/-- Pulling the actual finite parameter cover back retains the ENTIRE same
original total model under its SAME original structure map. -/
theorem exists_finite_modelParameterScalar_cover {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k[X])) (g : k[X]) (hg : g.eval 0 ≠ 0) :
    ∃ T : Finset kˣ,
      (⨆ u ∈ T, (p ≫ parameterScalarMap u) ⁻¹ᵁ PrimeSpectrum.basicOpen g) = ⊤ := by
  obtain ⟨T, hT⟩ := exists_finite_parameterScalar_cover g hg
  refine ⟨T, top_unique ?_⟩
  intro x _
  have hx : p x ∈ ⨆ u ∈ T, parameterScalarMap u ⁻¹ᵁ PrimeSpectrum.basicOpen g := by
    rw [hT]
    trivial
  obtain ⟨u, hu⟩ := Opens.mem_iSup.mp hx
  obtain ⟨huT, hxu⟩ := Opens.mem_iSup.mp hu
  exact Opens.mem_iSup.mpr ⟨u, Opens.mem_iSup.mpr ⟨huT, hxu⟩⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedParameterScalarCover
