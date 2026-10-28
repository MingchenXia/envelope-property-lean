import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberGeneratorNeighborhood
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # The same original morphism is finite near its closed central embedding

The original central map is the actual categorical pullback along evaluation
at zero. A closed immersion of that central map internally produces a genuine
principal base neighborhood on which the same original morphism is finite.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhood
open ProjectiveCentralFiberSectionLifting

/-- The actual original central morphism, with its full scheme structure. -/
def centralMap {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) (hf : f ≫ q = p) : zeroFiber p ⟶ zeroFiber q :=
  pullback.lift (zeroInclusion p ≫ f) (pullback.snd p (zeroMap k)) (by
    rw [Category.assoc, hf]
    exact pullback.condition)

/-- The SAME entire central morphism retains the original ambient triangle. -/
theorem centralMap_inclusion {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) (hf : f ≫ q = p) :
    centralMap p q f hf ≫ zeroInclusion q = zeroInclusion p ≫ f :=
  pullback.lift_fst _ _ _

/-- Every ENTIRE original ambient fibre through a central point is a singleton,
derived from the point injection of the actual central morphism. -/
theorem preimage_singleton_of_central_injective {k : Type u} [Field k]
    {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) (hf : f ≫ q = p)
    (h₀ : Function.Injective (centralMap p q f hf)) (a : zeroFiber p) :
    f ⁻¹' {f (zeroInclusion p a)} = {zeroInclusion p a} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hy
    have hpy : p y = p (zeroInclusion p a) := by
      have hp (z : Y) : q (f z) = p z :=
        congrArg (fun r : Y ⟶ Spec (CommRingCat.of (Polynomial k)) => r z) hf
      exact (hp y).symm.trans ((congrArg (fun z => q z) hy).trans (hp _))
    have hya : y ∈ Set.range (zeroInclusion p) := by
      rw [zeroInclusion, Scheme.Pullback.range_fst]
      refine ⟨pullback.snd p (zeroMap k) a, ?_⟩
      have hc : p (zeroInclusion p a) = zeroMap k (pullback.snd p (zeroMap k) a) :=
        congrArg (fun r : zeroFiber p ⟶ Spec (CommRingCat.of (Polynomial k)) => r a)
          (pullback.condition (f := p) (g := zeroMap k))
      exact hc.symm.trans hpy.symm
    obtain ⟨b, hb⟩ := hya
    have hpoint (z : zeroFiber p) :
        zeroInclusion q (centralMap p q f hf z) = f (zeroInclusion p z) :=
      congrArg (fun r : zeroFiber p ⟶ Z => r z) (centralMap_inclusion p q f hf)
    have hba : centralMap p q f hf b = centralMap p q f hf a := by
      apply (zeroInclusion q).isEmbedding.injective
      exact (hpoint b).trans ((congrArg (fun z => f z) hb).trans (hy.trans (hpoint a).symm))
    exact hb.symm.trans (congrArg (fun z => zeroInclusion p z) (h₀ hba))
  · intro hy
    exact congrArg (fun z => f z) hy

/-- The actual quasi-finite open contains EVERY original central point. -/
theorem central_range_subset_quasiFiniteLocus {k : Type u} [Field k]
    {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) [LocallyOfFiniteType f] (hf : f ≫ q = p)
    (h₀ : Function.Injective (centralMap p q f hf)) :
    Set.range (zeroInclusion p) ⊆ (f.quasiFiniteLocus : Set Y) := by
  rintro x ⟨a, rfl⟩
  have hfinite : (f ⁻¹' {f (zeroInclusion p a)}).Finite := by
    rw [preimage_singleton_of_central_injective p q f hf h₀ a]
    exact Set.finite_singleton _
  have : Finite (f.fiber (f (zeroInclusion p a))) :=
    (f.fiberHomeo _).finite_iff.mpr hfinite
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/-- Properness and the ACTUAL central point injection internally produce a
finite restriction of the SAME original morphism over a genuine D(g), g(0) != 0. -/
theorem exists_finite_neighborhood_of_central_injective {k : Type u} [Field k]
    {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper p]
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k))) [IsSeparated q]
    (f : Y ⟶ Z) (hf : f ≫ q = p)
    (h₀ : Function.Injective (centralMap p q f hf)) :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      IsFinite (f ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen g)) := by
  have : IsProper (f ≫ q) := hf.symm ▸ inferInstance
  have : IsProper f := IsProper.of_comp f q
  have hT := central_range_subset_quasiFiniteLocus p q f hf h₀
  obtain ⟨g, hg, hU⟩ :=
    ProjectiveCentralFiberGeneratorNeighborhood.exists_principal_neighborhood_of_fiber_subset
      p f.quasiFiniteLocus hT
  refine ⟨g, hg, ?_⟩
  let B : (Spec (CommRingCat.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
  let V : Z.Opens := q ⁻¹ᵁ B
  have hVU : f ⁻¹ᵁ V ≤ f.quasiFiniteLocus := by
    intro x hx
    apply hU
    change q (f x) ∈ B at hx
    change p x ∈ B
    have hpx : q (f x) = p x :=
      congrArg (fun r : Y ⟶ Spec (CommRingCat.of (Polynomial k)) => r x) hf
    exact hpx ▸ hx
  have : LocallyQuasiFinite (f ∣_ V) := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    ext x
    have hx : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := hVU x.2
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff] at hx
    simpa using hx
  exact IsFinite.of_isProper_of_locallyQuasiFinite (f ∣_ V)

/-- An ACTUAL original central closed immersion, without a finite-neighborhood
certificate, gives finiteness of the same ambient map near zero. -/
theorem exists_finite_neighborhood_of_central_closedImmersion {k : Type u} [Field k]
    {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsProper p]
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k))) [IsSeparated q]
    (f : Y ⟶ Z) (hf : f ≫ q = p) [IsClosedImmersion (centralMap p q f hf)] :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      IsFinite (f ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen g)) :=
  exists_finite_neighborhood_of_central_injective p q f hf
    (centralMap p q f hf).isEmbedding.injective

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhood
