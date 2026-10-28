/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Hironaka.Algebra.RegularSmooth.Stalk

/-!
# Original section rings as literal subalgebras of the actual function field

The embeddings are the actual generic germs on the original integral scheme.
No independent function-field or coordinate comparison is supplied.
-/

noncomputable section
namespace AlgebraicGeometry.Scheme.Hom
open CategoryTheory TopologicalSpace Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k))

/-- The actual generic germ is an algebra homomorphism for the original
structure morphism's section and stalk algebra structures. -/
def sectionsFunctionFieldAlgHom (U : X.Opens) [Nonempty U] :
    letI := f.sectionsAlgebra U
    letI := f.stalkAlgebra (genericPoint X)
    Γ(X, U) →ₐ[k] X.functionField := by
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra (genericPoint X)
  refine { (X.germToFunctionField U).hom with commutes' := ?_ }
  intro c
  exact congrArg (fun g : k →+* X.functionField => g c)
    (f.germ_comp_algebraMap_sectionsAlgebra U
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))))

/-- The literal image of the original section ring in the original function field. -/
def sectionsFunctionFieldSubalgebra (U : X.Opens) [Nonempty U] :
    letI := f.stalkAlgebra (genericPoint X)
    Subalgebra k X.functionField := by
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra (genericPoint X)
  exact (f.sectionsFunctionFieldAlgHom U).range

/-- Actual integrality identifies the entire original section ring with its
literal generic-germ image, rather than only with an abstract isomorphic copy. -/
def sectionsFunctionFieldEquiv (U : X.Opens) [Nonempty U] :
    letI := f.sectionsAlgebra U
    letI := f.stalkAlgebra (genericPoint X)
    Γ(X, U) ≃ₐ[k] f.sectionsFunctionFieldSubalgebra U := by
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra (genericPoint X)
  exact AlgEquiv.ofInjective (f.sectionsFunctionFieldAlgHom U)
    (X.germToFunctionField_injective U)

/-- The actual coordinate equivalence maps a section to its actual generic germ. -/
theorem sectionsFunctionFieldEquiv_apply (U : X.Opens) [Nonempty U] (s : Γ(X, U)) :
    letI := f.sectionsAlgebra U
    letI := f.stalkAlgebra (genericPoint X)
    ((f.sectionsFunctionFieldEquiv U s : f.sectionsFunctionFieldSubalgebra U) : X.functionField) =
      X.germToFunctionField U s := rfl

/-- Restriction to a nonempty open gives literal containment in the SAME
actual function field of the original scheme. -/
theorem sectionsFunctionFieldSubalgebra_le {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hUV : U ≤ V) :
    letI := f.stalkAlgebra (genericPoint X)
    f.sectionsFunctionFieldSubalgebra V ≤ f.sectionsFunctionFieldSubalgebra U := by
  let _ := f.stalkAlgebra (genericPoint X)
  rintro a ⟨s, rfl⟩
  refine ⟨(X.presheaf.map (homOfLE hUV).op) s, ?_⟩
  exact X.presheaf.germ_res_apply (homOfLE hUV) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))) s

/-- The actual restriction and the literal field-subalgebra inclusion commute
on every original section, retaining the actual scheme restriction map. -/
theorem sectionsFunctionFieldEquiv_restriction {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hUV : U ≤ V) (s : Γ(X, V)) :
    letI := f.stalkAlgebra (genericPoint X)
    letI := f.sectionsAlgebra U
    letI := f.sectionsAlgebra V
    Subalgebra.inclusion (f.sectionsFunctionFieldSubalgebra_le hUV)
        (f.sectionsFunctionFieldEquiv V s) =
      f.sectionsFunctionFieldEquiv U ((X.presheaf.map (homOfLE hUV).op) s) := by
  let _ := f.stalkAlgebra (genericPoint X)
  let _ := f.sectionsAlgebra U
  let _ := f.sectionsAlgebra V
  apply Subtype.ext
  exact (X.presheaf.germ_res_apply (homOfLE hUV) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))) s).symm

/-- Every original nonempty affine section image has the ORIGINAL scheme's
actual function field as its fraction field. -/
theorem sectionsFunctionFieldSubalgebra_isFractionRing
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := f.stalkAlgebra (genericPoint X)
    IsFractionRing (f.sectionsFunctionFieldSubalgebra U) X.functionField := by
  let _ := f.stalkAlgebra (genericPoint X)
  let _ := f.sectionsAlgebra U
  have : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  let e := f.sectionsFunctionFieldEquiv U
  apply IsFractionRing.of_ringEquiv_left e.symm.toRingEquiv
  intro x
  change (x : X.functionField) = ((e (e.symm x) : f.sectionsFunctionFieldSubalgebra U) : X.functionField)
  exact congrArg (fun y : f.sectionsFunctionFieldSubalgebra U => (y : X.functionField))
    (e.apply_symm_apply x).symm

/-- An actual intrinsic basic open gives the actual principal localization
of the literal original section subalgebra, with its genuine inclusion in K(X). -/
theorem sectionsFunctionFieldSubalgebra_isLocalization_basicOpen
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) (s : Γ(X, U))
    [Nonempty (X.basicOpen s)] :
    letI := f.stalkAlgebra (genericPoint X)
    letI := f.sectionsAlgebra U
    letI : Algebra (f.sectionsFunctionFieldSubalgebra U)
        (f.sectionsFunctionFieldSubalgebra (X.basicOpen s)) :=
      (Subalgebra.inclusion (f.sectionsFunctionFieldSubalgebra_le (X.basicOpen_le s))).toAlgebra
    IsLocalization.Away (f.sectionsFunctionFieldEquiv U s)
      (f.sectionsFunctionFieldSubalgebra (X.basicOpen s)) := by
  let _ := f.stalkAlgebra (genericPoint X)
  let _ := f.sectionsAlgebra U
  let _ := f.sectionsAlgebra (X.basicOpen s)
  let C := f.sectionsFunctionFieldSubalgebra U
  let D := f.sectionsFunctionFieldSubalgebra (X.basicOpen s)
  let hCD := f.sectionsFunctionFieldSubalgebra_le (X.basicOpen_le s)
  let _ : Algebra C D := (Subalgebra.inclusion hCD).toAlgebra
  have : IsLocalization.Away s Γ(X, X.basicOpen s) := hU.isLocalization_basicOpen s
  let eU := f.sectionsFunctionFieldEquiv U
  let eD := f.sectionsFunctionFieldEquiv (X.basicOpen s)
  have hinc (r : Γ(X, U)) : algebraMap C D (eU r) = eD (algebraMap Γ(X, U) Γ(X, X.basicOpen s) r) :=
    f.sectionsFunctionFieldEquiv_restriction (X.basicOpen_le s) r
  change IsLocalization (Submonoid.powers (eU s)) D
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow, hinc]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen s)) s).map
      eD.toMonoidHom).pow n
  · intro z
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj (Submonoid.powers s) (eD.symm z)
    have ht : eU t.val ∈ Submonoid.powers (eU s) := by
      obtain ⟨n, hn⟩ := t.property
      change s ^ n = t.val at hn
      refine ⟨n, ?_⟩
      change eU s ^ n = eU t.val
      rw [← map_pow, hn]
    refine ⟨(eU a, ⟨eU t.val, ht⟩), ?_⟩
    rw [hinc, hinc]
    have h := congrArg eD hat
    simpa only [map_mul, eD.apply_symm_apply] using h
  · intro a b hab
    exact ⟨1, by simp only [(Subalgebra.inclusion_injective hCD hab)]⟩

end AlgebraicGeometry.Scheme.Hom
