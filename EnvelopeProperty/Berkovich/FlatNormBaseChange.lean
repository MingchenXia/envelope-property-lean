/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.FiniteFlatNormGeneral
import EnvelopeProperty.Berkovich.SpectrumFibreScalarExtension

/-!
# Actual finite-flat function norms and scalar base change

The existing paper multiplicity is the true local dimension of the completed
residue tensor fibre. A whole-point fibre equivalence identifies its function
norm with the generic spectrum sum. Genuine finite-algebra local-dimension
conservation then proves all-function base change, including the literal
scalar-extended algebra and all EReal functions with their actual conventions.

Only module finiteness is needed. The statements evaluate at a supplied new
point; no scalar-extension fibre bijection or point-extension existence is
asserted. This module consumes the paper norm interface and intentionally sits
outside the generic spectrum umbrella. Regularizability is a separate existing
consumer theorem, not a premise in the pointwise comparison.
-/

open scoped NNReal TensorProduct
open Classical
noncomputable section
namespace EnvelopeProperty.Berk
variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The paper local-dimension multiplicity equals the actual generic fibre weight. -/
theorem flatFibreMult_eq_spectrumFibreNormMult [Module.Finite A B] (y : Berk k B) :
    flatFibreMult A y = Berkovich.Spectrum.fibreNormMult A y.toSpectrum := by
  let x := comap (IsScalarTower.toAlgHom k A B) y
  have hx : Berkovich.Spectrum.comap (algebraMap A B) y.toSpectrum = x.toSpectrum := rfl
  rw [flatFibreMult_eq (rfl : comap (IsScalarTower.toAlgHom k A B) y = x)]
  exact (Berkovich.Spectrum.fibreNormMult_eq_localFinrank_of_comap hx).symm

/-- The genuine whole paper fibre equals the absolute spectrum fibre. -/
def absoluteFibreEquiv (x : Berk k A) :
    comap (IsScalarTower.toAlgHom k A B) ⁻¹' {x} ≃
      Berkovich.Spectrum.comap (algebraMap A B) ⁻¹' {x.toSpectrum} := by
  let e : {y : Berk k B // comap (IsScalarTower.toAlgHom k A B) y = x} ≃ₜ
      Berkovich.RelativeSpectrum.Fibre (relativeSpectrumHomeomorph x) :=
    (relativeSpectrumHomeomorph (k := k) (A := B)).subtype (fun y => by
      change comap (IsScalarTower.toAlgHom k A B) y = x ↔
        Berkovich.RelativeSpectrum.comap (IsScalarTower.toAlgHom k A B)
          (relativeSpectrumHomeomorph y) = relativeSpectrumHomeomorph x
      rw [← relativeSpectrumHomeomorph_comap]
      exact (relativeSpectrumHomeomorph (k := k) (A := A)).injective.eq_iff.symm)
  let e₀ : comap (IsScalarTower.toAlgHom k A B) ⁻¹' {x} ≃
      {y : Berk k B // comap (IsScalarTower.toAlgHom k A B) y = x} :=
    Equiv.subtypeEquivRight (fun _ => Set.mem_singleton_iff)
  let e₁ : Berkovich.Spectrum.Fibre (B := B) x.toSpectrum ≃
      Berkovich.Spectrum.comap (algebraMap A B) ⁻¹' {x.toSpectrum} :=
    (Equiv.subtypeEquivRight (fun _ => Set.mem_singleton_iff)).symm
  exact e₀.trans (e.toEquiv.trans
    ((Berkovich.RelativeSpectrum.fibreForgetEquiv (relativeSpectrumHomeomorph x)).trans e₁))

/-- The fibre comparison preserves the entire seminorm. -/
theorem absoluteFibreEquiv_apply_val (x : Berk k A)
    (y : comap (IsScalarTower.toAlgHom k A B) ⁻¹' {x}) :
    (absoluteFibreEquiv x y).1 = y.1.toSpectrum := rfl

/-- Extend an old-space function by zero outside the prescribed trivial-base locus. -/
def extendFunction {M : Type*} [Zero M] (u : Berk k B → M)
    (y : Berkovich.Spectrum B) : M :=
  if h : ∀ c : k, c ≠ 0 → y.val (algebraMap k B c) = 1 then u ⟨y.val, h⟩ else 0

/-- The extension returns the original value on each actual paper point. -/
theorem extendFunction_toSpectrum {M : Type*} [Zero M]
    (u : Berk k B → M) (y : Berk k B) : extendFunction u y.toSpectrum = u y := by
  have h : ∀ c : k, c ≠ 0 → y.toSpectrum.val (algebraMap k B c) = 1 :=
    fun c hc => y.val_algebraMap c hc
  rw [extendFunction, dif_pos h]
  rfl

/-- The existing paper function norm is the true generic local-weighted sum. -/
theorem flatNormFun_eq_spectrumWeightedSum [Module.Finite A B]
    (u : Berk k B → EReal) (x : Berk k A) :
    flatNormFun u x =
      ∑ y ∈ (Berkovich.Spectrum.finite_preimage_singleton (A := B) x.toSpectrum).toFinset,
        (Berkovich.Spectrum.fibreNormMult A y : EReal) * extendFunction u y := by
  classical
  rw [flatNormFun]
  let e := absoluteFibreEquiv (B := B) x
  refine Finset.sum_bij (fun y hy => (e ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩).1) ?_ ?_ ?_ ?_
  · intro y hy
    exact (Set.Finite.mem_toFinset _).2 (e ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩).2
  · intro y₁ h₁ y₂ h₂ he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  · intro z hz
    obtain ⟨⟨y, hy⟩, he⟩ := e.surjective ⟨z, (Set.Finite.mem_toFinset _).1 hz⟩
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, congrArg Subtype.val he⟩
  · intro y hy
    dsimp only [e]
    rw [absoluteFibreEquiv_apply_val]
    rw [flatFibreMult_eq_spectrumFibreNormMult, extendFunction_toSpectrum]
    norm_cast

/-- The entire coefficient-locus extension commutes with actual algebra pullback. -/
theorem extendFunction_comap {D M : Type*} [CommRing D] [Algebra k D] [Zero M]
    (φ : B →ₐ[k] D) (u : Berk k B → M) (y : Berkovich.Spectrum D) :
    extendFunction (fun z => u (comap φ z)) y =
      extendFunction u (Berkovich.Spectrum.comap φ.toRingHom y) := by
  classical
  have hp : (∀ c : k, c ≠ 0 → y.val (algebraMap k D c) = 1) ↔
      ∀ c : k, c ≠ 0 →
        (Berkovich.Spectrum.comap φ.toRingHom y).val (algebraMap k B c) = 1 := by
    change (∀ c : k, c ≠ 0 → y.val (algebraMap k D c) = 1) ↔
      ∀ c : k, c ≠ 0 → y.val (φ (algebraMap k B c)) = 1
    simp only [AlgHom.commutes]
  by_cases h : ∀ c : k, c ≠ 0 → y.val (algebraMap k D c) = 1
  · rw [extendFunction, extendFunction, dif_pos h, dif_pos (hp.mp h)]
    rfl
  · rw [extendFunction, extendFunction, dif_neg h, dif_neg (mt hp.mpr h)]

/-- All EReal function norms commute with actual coefficient-algebra base change. -/
theorem flatNormFun_baseChange {C : Type*} [CommRing C] [Algebra k C]
    [Algebra A C] [IsScalarTower k A C] [Module.Finite A B]
    (u : Berk k B → EReal) (x' : Berk k C) :
    flatNormFun (B := C)
      (fun y : Berk k (C ⊗[A] B) =>
        u (comap ((Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).restrictScalars k) y)) x' =
      flatNormFun (B := A) u (comap (IsScalarTower.toAlgHom k A C) x') := by
  rw [flatNormFun_eq_spectrumWeightedSum, flatNormFun_eq_spectrumWeightedSum]
  simp only [extendFunction_comap]
  exact Berkovich.Spectrum.fibreWeightedERealSum_baseChange
    (A := A) (B := B) x'.toSpectrum (extendFunction u)

section ScalarExtension
variable {S : Type*} [CommRing S] [Algebra k S]
private local instance flatNormScalar_rightAlgebra : Algebra A (S ⊗[k] A) :=
  Algebra.TensorProduct.rightAlgebra
private local instance flatNormScalar_algebra : Algebra (S ⊗[k] A) (S ⊗[k] B) :=
  ScalarExtension.algebra k S A B
private local instance flatNormScalar_finite [Module.Finite A B] :
    Module.Finite (S ⊗[k] A) (S ⊗[k] B) := ScalarExtension.moduleFinite k S A B
private local instance flatNormScalar_tower : IsScalarTower k (S ⊗[k] A) (S ⊗[k] B) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((ScalarExtension.ringMap k S A B).restrictScalars k).commutes c |>.symm

/-- All EReal paper function norms commute with the literal scalar-extended map. -/
theorem flatNormFun_scalarExtension [Module.Finite A B]
    (u : Berk k B → EReal) (x' : Berk k (S ⊗[k] A)) :
    flatNormFun (B := S ⊗[k] A)
      (fun y : Berk k (S ⊗[k] B) =>
        u (comap (Algebra.TensorProduct.includeRight : B →ₐ[k] S ⊗[k] B) y)) x' =
      flatNormFun (B := A) u (comap (IsScalarTower.toAlgHom k A (S ⊗[k] A)) x') := by
  rw [flatNormFun_eq_spectrumWeightedSum, flatNormFun_eq_spectrumWeightedSum]
  simp only [extendFunction_comap]
  exact Berkovich.Spectrum.fibreWeightedERealSum_scalarExtension
    (R := k) (S := S) (A := A) (B := B) (extendFunction u) x'.toSpectrum

end ScalarExtension
end EnvelopeProperty.Berk
