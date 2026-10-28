import EnvelopeProperty.Vanishing.SpecializationFiniteComplex
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Specialization retains the original finite free modules and tensor maps -/

open Function
open scoped TensorProduct

noncomputable section
universe u v w z

namespace EnvelopeProperty.Vanishing.SpecializationOriginalFreeModules

section Coordinates

variable {R : Type u} [CommRing R]
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    {α β γ : Type w} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]

omit [DecidableEq β] in
/-- The matrix of the actual tensor-base-changed original map is the
coefficientwise image of its original matrix, in the actual base-changed bases. -/
theorem toMatrix_baseChange (S : Type z) [CommRing S] [Algebra R S]
    (bA : Module.Basis α R A) (bB : Module.Basis β R B) (f : A →ₗ[R] B) :
    LinearMap.toMatrix (bA.baseChange S) (bB.baseChange S) (f.baseChange S) =
      (LinearMap.toMatrix bA bB f).map (algebraMap R S) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul, Matrix.map_apply,
    Algebra.smul_def, mul_one]

omit [DecidableEq β] in
/-- Original coordinate isomorphisms conjugate the whole original linear map. -/
theorem toLin_toMatrix (bA : Module.Basis α R A) (bB : Module.Basis β R B)
    (f : A →ₗ[R] B) :
    Matrix.toLin' (LinearMap.toMatrix bA bB f) =
      bB.equivFun.toLinearMap.comp (f.comp bA.equivFun.symm.toLinearMap) := by
  simp only [LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix']
  rfl

omit [DecidableEq γ] in
/-- The matrix exactness statement is exactly the original one under the
original three basis isomorphisms. -/
theorem matrix_exact_iff (bA : Module.Basis α R A) (bB : Module.Basis β R B)
    (bC : Module.Basis γ R C) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (Matrix.toLin' (LinearMap.toMatrix bA bB f))
      (Matrix.toLin' (LinearMap.toMatrix bB bC g)) ↔ Exact f g := by
  rw [toLin_toMatrix, toLin_toMatrix]
  have hA := bA.equivFun.symm.surjective.comp_exact_iff_exact
    (f := bB.equivFun.toLinearMap.comp f)
    (g := bC.equivFun.toLinearMap.comp (g.comp bB.equivFun.symm.toLinearMap))
  have hC := bC.equivFun.injective.comp_exact_iff_exact
    (f := bB.equivFun.toLinearMap.comp f) (g := g.comp bB.equivFun.symm.toLinearMap)
  simpa only [LinearMap.comp_assoc] using
    hA.trans (hC.trans (LinearEquiv.conj_exact_iff_exact f g bB.equivFun))

omit [DecidableEq γ] in
/-- Exactness of the original tensor maps is identified with exactness of
their original coefficientwise matrix images, without a supplied comparison. -/
theorem baseChange_exact_iff (S : Type z) [CommRing S] [Algebra R S]
    (bA : Module.Basis α R A) (bB : Module.Basis β R B)
    (bC : Module.Basis γ R C) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.baseChange S) (g.baseChange S) ↔
      Exact (Matrix.toLin' ((LinearMap.toMatrix bA bB f).map (algebraMap R S)))
        (Matrix.toLin' ((LinearMap.toMatrix bB bC g).map (algebraMap R S))) := by
  have h := matrix_exact_iff (bA.baseChange S) (bB.baseChange S) (bC.baseChange S)
    (f.baseChange S) (g.baseChange S)
  rw [toMatrix_baseChange, toMatrix_baseChange] at h
  exact h.symm

/-- The original finite free module complex has one actual principal open
on which all coefficient extensions to fields are exact.  The source fibre
is the canonical residue field of the original closed point. -/
theorem exists_closed_fibre_exactness_neighborhood
    (p : Ideal R) [p.IsMaximal]
    (bA : Module.Basis α R A) (bB : Module.Basis β R B) (bC : Module.Basis γ R C)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : g.comp f = 0)
    (hex : Exact (f.baseChange p.ResidueField) (g.baseChange p.ResidueField)) :
    ∃ r : R, r ∉ p ∧ ∀ (K : Type z) [Field K] [Algebra R K], algebraMap R K r ≠ 0 →
      Exact (f.baseChange K) (g.baseChange K) := by
  let F := LinearMap.toMatrix bA bB f
  let G := LinearMap.toMatrix bB bC g
  have hGF : G * F = 0 := by
    change LinearMap.toMatrix bB bC g * LinearMap.toMatrix bA bB f = 0
    rw [← LinearMap.toMatrix_comp bA bB bC, hgf, map_zero]
  have hexM : Exact (Matrix.toLin' (F.map (algebraMap R p.ResidueField)))
      (Matrix.toLin' (G.map (algebraMap R p.ResidueField))) :=
    (baseChange_exact_iff p.ResidueField bA bB bC f g).mp hex
  obtain ⟨r, hr, hExact⟩ := SpecializationFiniteComplex.exists_field_exactness_neighborhood
    (algebraMap R p.ResidueField) p.algebraMap_residueField_surjective F G hGF hexM
  refine ⟨r, ?_, ?_⟩
  · intro hp
    exact zero_ne_one ((Ideal.algebraMap_residueField_eq_zero.mpr hp).symm.trans hr)
  · intro K _ _ hK
    apply (baseChange_exact_iff K bA bB bC f g).mpr
    exact hExact K (algebraMap R K) hK

/-- The actual tensor extension of the SAME original finite free module
complex to its fraction field is exact when its actual closed residue
fibre is exact. All basis and coefficient comparisons are proved internally. -/
theorem generic_exact_of_closed_fibre_exact [IsDomain R]
    (p : Ideal R) [p.IsMaximal]
    (bA : Module.Basis α R A) (bB : Module.Basis β R B) (bC : Module.Basis γ R C)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : g.comp f = 0)
    (hex : Exact (f.baseChange p.ResidueField) (g.baseChange p.ResidueField))
    (K : Type z) [Field K] [Algebra R K] [IsFractionRing R K] :
    Exact (f.baseChange K) (g.baseChange K) := by
  obtain ⟨r, hr, hExact⟩ := exists_closed_fibre_exactness_neighborhood p bA bB bC f g hgf hex
  apply hExact K
  intro h
  have hrzero : r = 0 :=
    IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm)
  exact hr (hrzero ▸ p.zero_mem)

/-- The native short complex of the actual tensor extensions of the
original maps, with no replacement of their original module carriers. -/
def baseChangeComplex (S : Type z) [CommRing S] [Algebra R S]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : g.comp f = 0) :
    CategoryTheory.ShortComplex (ModuleCat.{max z v} S) :=
  CategoryTheory.ShortComplex.moduleCatMk (f.baseChange S) (g.baseChange S) (by
    rw [← LinearMap.baseChange_comp, hgf, LinearMap.baseChange_zero])

/-- Native homology of the original tensor complex vanishes on a
constructed principal neighborhood of the original closed point. -/
theorem exists_original_homology_zero_neighborhood
    (p : Ideal R) [p.IsMaximal]
    (bA : Module.Basis α R A) (bB : Module.Basis β R B) (bC : Module.Basis γ R C)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : g.comp f = 0)
    (hzero : CategoryTheory.Limits.IsZero
      (baseChangeComplex p.ResidueField f g hgf).homology) :
    ∃ r : R, r ∉ p ∧ ∀ (K : Type z) [Field K] [Algebra R K], algebraMap R K r ≠ 0 →
      CategoryTheory.Limits.IsZero (baseChangeComplex K f g hgf).homology := by
  have hex : Exact (f.baseChange p.ResidueField) (g.baseChange p.ResidueField) :=
    LinearMap.exact_iff.mpr
      (((baseChangeComplex p.ResidueField f g hgf).moduleCat_exact_iff_range_eq_ker.mp
        ((baseChangeComplex p.ResidueField f g hgf).exact_iff_isZero_homology.mpr hzero)).symm)
  obtain ⟨r, hr, hExact⟩ := exists_closed_fibre_exactness_neighborhood p bA bB bC f g hgf hex
  refine ⟨r, hr, fun K _ _ hK => ?_⟩
  apply (baseChangeComplex K f g hgf).exact_iff_isZero_homology.mp
  apply (baseChangeComplex K f g hgf).moduleCat_exact_iff_range_eq_ker.mpr
  exact (LinearMap.exact_iff.mp (hExact K hK)).symm

/-- The native homology of the SAME original tensor complex vanishes over
its original fraction field if it vanishes on its original closed fibre. -/
theorem original_generic_homology_isZero_of_closed_fibre [IsDomain R]
    (p : Ideal R) [p.IsMaximal]
    (bA : Module.Basis α R A) (bB : Module.Basis β R B) (bC : Module.Basis γ R C)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : g.comp f = 0)
    (hzero : CategoryTheory.Limits.IsZero
      (baseChangeComplex p.ResidueField f g hgf).homology)
    (K : Type z) [Field K] [Algebra R K] [IsFractionRing R K] :
    CategoryTheory.Limits.IsZero (baseChangeComplex K f g hgf).homology := by
  obtain ⟨r, hr, hExact⟩ := exists_original_homology_zero_neighborhood p bA bB bC f g hgf hzero
  apply hExact K
  intro h
  have hrzero : r = 0 :=
    IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm)
  exact hr (hrzero ▸ p.zero_mem)

end Coordinates

end EnvelopeProperty.Vanishing.SpecializationOriginalFreeModules
