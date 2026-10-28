import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Genuine low-degree Euler additivity for actual cochain complexes -/
open CategoryTheory Limits
noncomputable section
universe u
namespace EnvelopeProperty.CohomologyEulerAdditivity
variable {k : Type u} [Field k]

private theorem exact_six_finrank {A B C D E F : ModuleCat.{u} k}
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    [Module.Finite k D] [Module.Finite k E] [Module.Finite k F]
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F)
    (ha : Function.Injective a) (he : Function.Surjective e)
    (hab : LinearMap.range a.hom = LinearMap.ker b.hom)
    (hbc : LinearMap.range b.hom = LinearMap.ker c.hom)
    (hcd : LinearMap.range c.hom = LinearMap.ker d.hom)
    (hde : LinearMap.range d.hom = LinearMap.ker e.hom) :
    (Module.finrank k A : ℤ) - Module.finrank k B + Module.finrank k C -
      Module.finrank k D + Module.finrank k E - Module.finrank k F = 0 := by
  have h0 := LinearMap.finrank_range_of_inj (f := a.hom) ha
  have h1 := b.hom.finrank_range_add_finrank_ker
  have h2 := c.hom.finrank_range_add_finrank_ker
  have h3 := d.hom.finrank_range_add_finrank_ker
  have h4 := e.hom.finrank_range_add_finrank_ker
  rw [← hab] at h1
  rw [← hbc] at h2
  rw [← hcd] at h3
  rw [← hde] at h4
  have h5 : Module.finrank k (LinearMap.range e.hom) = Module.finrank k F := by
    rw [LinearMap.range_eq_top.mpr he, finrank_top]
  omega

/-- The Euler index of the whole actual original groups in degrees zero and one. -/
def eulerIndex (C : CochainComplex (ModuleCat.{u} k) ℕ) : ℤ :=
  (Module.finrank k (C.homology 0) : ℤ) - Module.finrank k (C.homology 1)

/-- The actual long exact sequence gives true Euler additivity whenever the
actual first-left H² vanishes; every finite-dimensionality premise concerns
only the SAME actual original cohomology groups. -/
theorem eulerIndex_add (S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ))
    (hS : S.ShortExact)
    [Module.Finite k (S.X₁.homology 0)] [Module.Finite k (S.X₂.homology 0)]
    [Module.Finite k (S.X₃.homology 0)] [Module.Finite k (S.X₁.homology 1)]
    [Module.Finite k (S.X₂.homology 1)] [Module.Finite k (S.X₃.homology 1)]
    (h₂ : IsZero (S.X₁.homology 2)) :
    eulerIndex S.X₂ = eulerIndex S.X₁ + eulerIndex S.X₃ := by
  let a := HomologicalComplex.homologyMap S.f 0
  let b := HomologicalComplex.homologyMap S.g 0
  let c := hS.δ 0 1 (by decide)
  let d := HomologicalComplex.homologyMap S.f 1
  let e := HomologicalComplex.homologyMap S.g 1
  have hmono : Mono (S.f.f 0) := by
    have h := hS.map_of_exact (HomologicalComplex.eval (ModuleCat.{u} k) (.up ℕ) 0)
    exact h.mono_f
  let : Mono (S.f.f 0) := hmono
  have ha : Function.Injective a := by
    have : Mono a := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0
      (fun i hi => by change i+1=0 at hi; omega)
    exact (ModuleCat.mono_iff_injective a).mp inferInstance
  have he : Function.Surjective e := by
    have : Epi e := (hS.homology_exact₃ 1 2 (by decide)).epi_f
      (h₂.eq_of_tgt _ _)
    exact (ModuleCat.epi_iff_surjective e).mp inferInstance
  have h := exact_six_finrank a b c d e ha he
    (hS.homology_exact₂ 0).moduleCat_range_eq_ker
    (hS.homology_exact₃ 0 1 (by decide)).moduleCat_range_eq_ker
    (hS.homology_exact₁ 0 1 (by decide)).moduleCat_range_eq_ker
    (hS.homology_exact₂ 1).moduleCat_range_eq_ker
  unfold eulerIndex
  omega

end EnvelopeProperty.CohomologyEulerAdditivity
