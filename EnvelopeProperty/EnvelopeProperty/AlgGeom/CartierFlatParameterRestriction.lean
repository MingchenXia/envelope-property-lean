/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Actual parameter restriction on flat scheme charts

The actual original affine coordinate coefficient algebra is flat, so true
nonzerodivisor base parameters remain regular. Actual basic-open localization
therefore makes the original parameter-open restriction injective.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.CartierFlatParameter
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of R)) {U : X.Opens} (hU : IsAffineOpen U)

/-- The coefficient homomorphism comes from the entire original chart/base map. -/
def affineCoefficient : R →+* Γ(X, U) :=
  (Spec.preimage (hU.fromSpec ≫ f)).hom

/-- The actual coefficient spectrum morphism is the original whole composite. -/
theorem affineCoefficient_specMap :
    Spec.map (CommRingCat.ofHom (affineCoefficient f hU)) = hU.fromSpec ≫ f :=
  Spec.map_preimage _

/-- Flatness of the actual scheme map proves flatness of its original chart algebra. -/
theorem affineCoefficient_flat [Flat f] :
    letI := (affineCoefficient f hU).toAlgebra
    Module.Flat R Γ(X, U) := by
  let := (affineCoefficient f hU).toAlgebra
  have h : Flat (Spec.map (CommRingCat.ofHom (affineCoefficient f hU))) := by
    rw [affineCoefficient_specMap]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h)

/-- The original nonzerodivisor base element is regular in the actual affine chart. -/
theorem affineParameter_isRegular [Flat f] (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsRegular (affineCoefficient f hU r) := by
  let := (affineCoefficient f hU).toAlgebra
  have : Module.Flat R Γ(X, U) := affineCoefficient_flat f hU
  apply (Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr
  change Function.Injective (fun x : Γ(X, U) => r • x)
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hr

/-- The actual chart parameter open is the whole original base-open intersection. -/
theorem affineParameter_basicOpen (r : R) :
    X.basicOpen (affineCoefficient f hU r) = U ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
  have he : PrimeSpectrum.basicOpen (affineCoefficient f hU r) =
      (hU.fromSpec ≫ f) ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
    rw [← affineCoefficient_specMap]
    exact (SpecMap_preimage_basicOpen (CommRingCat.ofHom (affineCoefficient f hU)) r).symm
  rw [← hU.fromSpec_image_basicOpen, he, Scheme.Hom.comp_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf, hU.opensRange_fromSpec]

/-- Actual localization by the true parameter separates entire affine sections. -/
theorem affineParameter_basicOpen_restriction_injective [Flat f]
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    Function.Injective (X.presheaf.map (homOfLE
      (X.basicOpen_le (affineCoefficient f hU r))).op) := by
  have := hU.isLocalization_basicOpen (affineCoefficient f hU r)
  change Function.Injective (algebraMap Γ(X, U)
    Γ(X, X.basicOpen (affineCoefficient f hU r)))
  apply IsLocalization.injectiveₛ (M := Submonoid.powers (affineCoefficient f hU r))
  intro a ha
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff a (affineCoefficient f hU r)).mp ha
  exact (affineParameter_isRegular f hU r hr).pow n

include hU in
/-- The actual whole original parameter-open restriction is injective. -/
theorem affineParameter_restriction_injective [Flat f]
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    Function.Injective (X.presheaf.map
      (homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ U)).op) := by
  have transport (V : X.Opens) (hV : V ≤ U)
      (e : X.basicOpen (affineCoefficient f hU r) = V) :
      Function.Injective (X.presheaf.map (homOfLE hV).op) := by
    subst V
    exact affineParameter_basicOpen_restriction_injective f hU r hr
  exact transport _ inf_le_left (affineParameter_basicOpen f hU r)


/-- The actual whole parameter-open restriction separates functions on every
original open, without affineness or quasi-compactness assumptions. -/
theorem parameter_restriction_injective [Flat f] (V : X.Opens)
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    Function.Injective (X.presheaf.map
      (homOfLE (inf_le_left : V ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ V)).op) := by
  intro s t hst
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := V) hx
  refine ⟨W, hWV, hxW, ?_⟩
  apply affineParameter_restriction_injective f hW r hr
  have he (a : Γ(X, V)) :
      X.presheaf.map (homOfLE
        (inf_le_left : W ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ W)).op
          (X.presheaf.map (homOfLE hWV).op a) =
        X.presheaf.map (homOfLE
          (inf_le_inf hWV le_rfl : W ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤
            V ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r)).op
          (X.presheaf.map (homOfLE
            (inf_le_left : V ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ V)).op a) := by
    simp only [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl
  exact (he s).trans ((congrArg (fun a => X.presheaf.map (homOfLE
    (inf_le_inf hWV le_rfl : W ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤
      V ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r)).op a) hst).trans (he t).symm)

end EnvelopeProperty.CartierFlatParameter
