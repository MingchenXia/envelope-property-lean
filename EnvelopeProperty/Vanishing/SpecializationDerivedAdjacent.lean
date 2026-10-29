import EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep

/-! # Adjacent homology in the actual finite-free replacement step

The pullback predecessor has exactly the old cycles, after arbitrary algebra
base change, so the replacement also preserves the preceding native homology.
This is the comparison needed to iterate the construction down a bounded complex.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep

variable {R : Type u} [CommRing R]

/-- Native cycles detect an isomorphism by the actual middle-term cycles.
The later application produces both elementwise conditions from purity. -/
theorem cyclesMap_isIso_of_relations
    {U V : ShortComplex (ModuleCat.{u} R)} (φ : U ⟶ V)
    (hinj : ∀ x y : U.X₂, U.g x = 0 → U.g y = 0 → φ.τ₂ x = φ.τ₂ y → x = y)
    (hsurj : ∀ y : V.X₂, V.g y = 0 → ∃ x : U.X₂, U.g x = 0 ∧ φ.τ₂ x = y) :
    IsIso (ShortComplex.cyclesMap φ) := by
  apply (ConcreteCategory.isIso_iff_bijective (ShortComplex.cyclesMap φ)).mpr
  have hU := (ModuleCat.mono_iff_injective U.iCycles).mp inferInstance
  have hV := (ModuleCat.mono_iff_injective V.iCycles).mp inferInstance
  have hnatural (x : U.cycles) :
      V.iCycles (ShortComplex.cyclesMap φ x) = φ.τ₂ (U.iCycles x) :=
    ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) x
  constructor
  · intro x y hxy
    apply hU
    apply hinj
    · exact ConcreteCategory.congr_hom U.iCycles_g x
    · exact ConcreteCategory.congr_hom U.iCycles_g y
    · rw [← hnatural, ← hnatural, hxy]
  · intro y
    obtain ⟨x, hx, hxy⟩ := hsurj (V.iCycles y)
      (ConcreteCategory.congr_hom V.iCycles_g y)
    let z := U.moduleCatCyclesIso.inv ⟨x, hx⟩
    have hz : U.iCycles z = x :=
      ConcreteCategory.congr_hom U.moduleCatCyclesIso_inv_iCycles ⟨x, hx⟩
    refine ⟨z, hV ?_⟩
    rw [hnatural, hz, hxy]

variable [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.homology] [Module.Finite R S.X₃]

variable {D : Type u} [AddCommGroup D] [Module R D]
    (h : D →ₗ[R] S.X₁) (hh : S.f.hom ∘ₗ h = 0)

/-- The actual incoming map into the pullback predecessor. -/
def lowerDifferential : D →ₗ[R] PullbackTerm S :=
  LinearMap.codRestrict _ (h.prod 0) fun x => by
    change lift S 0 - S.f (h x) = 0
    have hz := LinearMap.congr_fun hh x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    rw [map_zero, hz, sub_self]

/-- The original three consecutive terms below the replacement degree. -/
def lowerOriginal : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk h S.f.hom hh

/-- The actual replacement in the preceding three terms. -/
def lowerReplacement : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (lowerDifferential S h hh) (differential S) (by
    ext x
    rfl)

/-- The actual comparison in the preceding degree. -/
def lowerComparison : lowerReplacement S h hh ⟶ lowerOriginal S h hh where
  τ₁ := 𝟙 _
  τ₂ := ModuleCat.ofHom (predecessor S)
  τ₃ := ModuleCat.ofHom (lift S)
  comm₁₂ := by apply ModuleCat.hom_ext; rfl
  comm₂₃ := by apply ModuleCat.hom_ext; exact (comparison_commutes S).symm

/-- Before scalar extension, the preceding cycles are already identified by
the explicit pullback projections. -/
theorem lower_comparison_cycles_isIso :
    IsIso (ShortComplex.cyclesMap (lowerComparison S h hh)) := by
  apply cyclesMap_isIso_of_relations
  · intro x y hx hy hxy
    apply Subtype.ext
    apply Prod.ext
    · exact hxy
    · exact hx.trans hy.symm
  · intro y hy
    change S.f y = 0 at hy
    refine ⟨⟨(y, 0), ?_⟩, rfl, rfl⟩
    change lift S 0 - S.f y = 0
    rw [map_zero, hy, sub_self]

/-- The preceding original native homology is preserved before scalar extension.
This allows its independently known finiteness to feed the next replacement step. -/
def lowerHomologyIso : (lowerReplacement S h hh).homology ≅
    (lowerOriginal S h hh).homology := by
  let : IsIso (ShortComplex.cyclesMap (lowerComparison S h hh)) :=
    lower_comparison_cycles_isIso S h hh
  let : Epi (lowerComparison S h hh).τ₁ := by
    change Epi (𝟙 (ModuleCat.of R D))
    infer_instance
  let : IsIso (ShortComplex.homologyMap (lowerComparison S h hh)) :=
    ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap (lowerComparison S h hh))

variable (T : Type u) [CommRing T] [Algebra R T]

/-- The actual tensor predecessor comparison is the first projection of the
scalar-extended relation inclusion. -/
theorem predecessor_baseChange_apply (x : T ⊗[R] PullbackTerm S) :
    (predecessor S).baseChange T x =
      (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)
        ((LinearMap.ker (joint S)).subtype.baseChange T x)).1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t x => rfl
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add]

/-- Both actual projections together remain injective under arbitrary scalar
extension, by the already produced pure kernel comparison. -/
theorem projections_baseChange_injective [Module.Flat R S.X₂] :
    Function.Injective ((predecessor S).baseChange T |>.prod
      ((differential S).baseChange T)) := by
  intro x y hxy
  apply (joint_kernel_baseChange_bijective S T).injective
  apply Subtype.ext
  apply (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)).injective
  apply Prod.ext
  · change (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)
      ((LinearMap.ker (joint S)).subtype.baseChange T x)).1 =
        (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)
          ((LinearMap.ker (joint S)).subtype.baseChange T y)).1
    rw [← predecessor_baseChange_apply, ← predecessor_baseChange_apply]
    exact congrArg Prod.fst hxy
  · change (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)
      ((LinearMap.ker (joint S)).subtype.baseChange T x)).2 =
        (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)
          ((LinearMap.ker (joint S)).subtype.baseChange T y)).2
    rw [← differential_baseChange_apply, ← differential_baseChange_apply]
    exact congrArg Prod.snd hxy

/-- An original scalar-extended cycle has an actual lift to a cycle of the
constructed predecessor; the lift is produced from the pure relation kernel. -/
theorem exists_cycle_lift [Module.Flat R S.X₂]
    (a : T ⊗[R] S.X₁) (ha : S.f.hom.baseChange T a = 0) :
    ∃ x : T ⊗[R] PullbackTerm S,
      (differential S).baseChange T x = 0 ∧
        (predecessor S).baseChange T x = a := by
  let z := (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)).symm (a, 0)
  have hz : (joint S).baseChange T z = 0 := by
    rw [joint_baseChange_apply]
    simp only [z, LinearEquiv.apply_symm_apply, map_zero, ha, sub_self]
  obtain ⟨x, hx⟩ := (joint_kernel_baseChange_bijective S T).surjective ⟨z, hz⟩
  have hval := congrArg Subtype.val hx
  change (LinearMap.ker (joint S)).subtype.baseChange T x = z at hval
  refine ⟨x, ?_, ?_⟩
  · rw [differential_baseChange_apply, hval]
    simp only [z, LinearEquiv.apply_symm_apply]
  · rw [predecessor_baseChange_apply, hval]
    simp only [z, LinearEquiv.apply_symm_apply]

/-- The comparison of the preceding actual cycle modules is an isomorphism
after every algebra base change. -/
theorem baseChange_lower_comparison_cycles_isIso [Module.Flat R S.X₂] :
    IsIso (ShortComplex.cyclesMap
      (baseChangeComparison (lowerComparison S h hh) T)) := by
  apply cyclesMap_isIso_of_relations
  · intro x y hx hy hxy
    apply projections_baseChange_injective S T
    apply Prod.ext
    · exact hxy
    · exact hx.trans hy.symm
  · intro y hy
    exact exists_cycle_lift S T y hy

/-- The preceding native homology is preserved after every algebra base change,
with the original incoming module and incoming map retained. -/
def baseChangeLowerHomologyIso [Module.Flat R S.X₂] :
    (baseChangeComplex (lowerReplacement S h hh) T).homology ≅
      (baseChangeComplex (lowerOriginal S h hh) T).homology := by
  let : IsIso (ShortComplex.cyclesMap
      (baseChangeComparison (lowerComparison S h hh) T)) :=
    baseChange_lower_comparison_cycles_isIso S h hh T
  have hfirst : (baseChangeComparison (lowerComparison S h hh) T).τ₁ = 𝟙 _ := by
    apply ModuleCat.hom_ext
    change (LinearMap.id : D →ₗ[R] D).baseChange T = LinearMap.id
    exact LinearMap.baseChange_id
  let : Epi (baseChangeComparison (lowerComparison S h hh) T).τ₁ := by
    rw [hfirst]
    change Epi (𝟙 (ModuleCat.of T (T ⊗[R] D)))
    infer_instance
  let : IsIso (ShortComplex.homologyMap
      (baseChangeComparison (lowerComparison S h hh) T)) :=
    ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap (baseChangeComparison (lowerComparison S h hh) T))

end EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep
