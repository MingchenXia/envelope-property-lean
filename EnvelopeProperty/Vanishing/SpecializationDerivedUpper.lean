import EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep

/-! # Higher homology in the actual finite-free replacement step

The actual boundary image in the following finite term is retained by the
constructed lift, including after arbitrary algebra base change.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.homology] [Module.Finite R S.X₃]
    (T : Type u) [CommRing T] [Algebra R T]

/-- The actual boundary image in the following term is retained after every
algebra base change. No flatness of the scalar-extension algebra is required. -/
theorem outgoing_baseChange_range :
    LinearMap.range ((outgoing S).baseChange T) =
      LinearMap.range (S.g.hom.baseChange T) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(lift S).baseChange T x, ?_⟩
    simp only [outgoing, LinearMap.baseChange_comp, LinearMap.comp_apply]
  · rintro _ ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := LinearMap.baseChange_surjective T (joint_surjective S) b
    let a := (TensorProduct.prodRight R T T S.X₁ (FreeTerm S) z).1
    let e := (TensorProduct.prodRight R T T S.X₁ (FreeTerm S) z).2
    have hjoint : (lift S).baseChange T e - S.f.hom.baseChange T a = b :=
      (joint_baseChange_apply S T z).symm.trans hz
    have hg : S.g.hom.baseChange T ((lift S).baseChange T e) =
        S.g.hom.baseChange T b := by
      have he := congrArg (S.g.hom.baseChange T) hjoint
      have hcomp : S.g.hom.baseChange T (S.f.hom.baseChange T a) = 0 :=
        (baseChangeComplex S T).moduleCat_zero_apply a
      rw [map_sub, hcomp, sub_zero] at he
      exact he
    refine ⟨e, ?_⟩
    simpa only [outgoing, LinearMap.baseChange_comp, LinearMap.comp_apply] using hg

variable {D : Type u} [AddCommGroup D] [Module R D]
    (h : S.X₃ →ₗ[R] D) (hh : h ∘ₗ S.g.hom = 0)

/-- The actual original complex in the next degree. -/
def upperOriginal : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk S.g.hom h hh

/-- The actual replacement in the next degree. -/
def upperReplacement : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (outgoing S) h (by
    change (h ∘ₗ S.g.hom) ∘ₗ lift S = 0
    rw [hh, LinearMap.zero_comp])

/-- The actual comparison in the next degree fixes the original middle
and outgoing modules. -/
def upperComparison : upperReplacement S h hh ⟶ upperOriginal S h hh where
  τ₁ := ModuleCat.ofHom (lift S)
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by apply ModuleCat.hom_ext; rfl
  comm₂₃ := by apply ModuleCat.hom_ext; rfl

/-- The comparison identifies the actual next-degree native cokernels after
arbitrary scalar extension. -/
theorem baseChange_upper_comparison_opcycles_isIso :
    IsIso (ShortComplex.opcyclesMap
      (baseChangeComparison (upperComparison S h hh) T)) := by
  apply opcyclesMap_isIso_of_relations
  · intro b
    refine ⟨0, b, ?_⟩
    change (LinearMap.id : S.X₃ →ₗ[R] S.X₃).baseChange T b -
      S.g.hom.baseChange T 0 = b
    rw [LinearMap.baseChange_id, map_zero, sub_zero]
    rfl
  · intro a e he
    change (LinearMap.id : S.X₃ →ₗ[R] S.X₃).baseChange T e =
      S.g.hom.baseChange T a at he
    rw [LinearMap.baseChange_id] at he
    have hmem : e ∈ LinearMap.range (S.g.hom.baseChange T) := ⟨a, he.symm⟩
    rw [← outgoing_baseChange_range S T] at hmem
    exact hmem

/-- The actual next-degree native homology is retained after every algebra
base change, including nonflat residue maps. -/
def baseChangeUpperHomologyIso :
    (baseChangeComplex (upperReplacement S h hh) T).homology ≅
      (baseChangeComplex (upperOriginal S h hh) T).homology := by
  let : IsIso (ShortComplex.opcyclesMap
      (baseChangeComparison (upperComparison S h hh) T)) :=
    baseChange_upper_comparison_opcycles_isIso S T h hh
  have hthird : (baseChangeComparison (upperComparison S h hh) T).τ₃ = 𝟙 _ := by
    apply ModuleCat.hom_ext
    change (LinearMap.id : D →ₗ[R] D).baseChange T = LinearMap.id
    exact LinearMap.baseChange_id
  let : Mono (baseChangeComparison (upperComparison S h hh) T).τ₃ := by
    rw [hthird]
    change Mono (𝟙 (ModuleCat.of T (T ⊗[R] D)))
    infer_instance
  let : IsIso (ShortComplex.homologyMap
      (baseChangeComparison (upperComparison S h hh) T)) :=
    ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap (baseChangeComparison (upperComparison S h hh) T))

end EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep
