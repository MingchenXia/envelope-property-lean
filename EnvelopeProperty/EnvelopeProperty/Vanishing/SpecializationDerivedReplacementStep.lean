import ModularCurves.ForMathlib.BaseChangeKerCoker
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # An actual finite-free replacement step for cochain complexes

The finite cokernel and finite free middle term are constructed from the
original native homology and original outgoing term.  No finite-free model
or cohomology base-change comparison is supplied as an input.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual cokernel of an original incoming differential is finite when
the native middle homology and original next term are finite. -/
theorem finite_cokernel (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.homology] [Module.Finite R S.X₃] :
    Module.Finite R (S.X₂ ⧸ LinearMap.range S.f.hom) := by
  let T := ShortComplex.mk S.homologyι S.fromOpcycles S.homologyι_comp_fromOpcycles
  have hT : T.Exact := T.exact_of_f_is_kernel S.homologyIsKernel
  let : Module.Finite R S.opcycles :=
    ModularCurves.Module.Finite.of_exact_of_finite
      S.homologyι.hom S.fromOpcycles.hom
      (LinearMap.exact_iff.mpr (T.moduleCat_exact_iff_range_eq_ker.mp hT).symm)
  exact Module.Finite.equiv S.moduleCatOpcyclesIso.toLinearEquiv

variable (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.homology] [Module.Finite R S.X₃]

/-- A finite free module and an actual lift to the original middle term,
constructed from a finite cover of the original cokernel. -/
def liftData : Σ r : ℕ, {e : (Fin r → R) →ₗ[R] S.X₂ //
    Function.Surjective ((LinearMap.range S.f.hom).mkQ ∘ₗ e)} := by
  let : Module.Finite R (S.X₂ ⧸ LinearMap.range S.f.hom) := finite_cokernel S
  let hcover := Module.Finite.exists_fin' R (S.X₂ ⧸ LinearMap.range S.f.hom)
  let r := hcover.choose
  let q := hcover.choose_spec.choose
  have hq := hcover.choose_spec.choose_spec
  let hlift := Module.projective_lifting_property
    (LinearMap.range S.f.hom).mkQ q
    (Submodule.mkQ_surjective (LinearMap.range S.f.hom))
  refine ⟨r, hlift.choose, ?_⟩
  rw [hlift.choose_spec]
  exact hq

/-- The constructed finite free middle term. -/
abbrev FreeTerm := Fin (liftData S).1 → R

/-- The constructed comparison from the finite free term to the original term. -/
def lift : FreeTerm S →ₗ[R] S.X₂ := (liftData S).2.1

/-- The constructed lift generates the original cokernel. -/
theorem quotient_comp_lift_surjective :
    Function.Surjective ((LinearMap.range S.f.hom).mkQ ∘ₗ lift S) :=
  (liftData S).2.2

/-- The original incoming differential and constructed free lift jointly cover
the original middle term. -/
def joint : (S.X₁ × FreeTerm S) →ₗ[R] S.X₂ :=
  lift S ∘ₗ LinearMap.snd R S.X₁ (FreeTerm S) -
    S.f.hom ∘ₗ LinearMap.fst R S.X₁ (FreeTerm S)

/-- Surjectivity is produced by the finite cokernel cover, not supplied. -/
theorem joint_surjective : Function.Surjective (joint S) := by
  intro b
  obtain ⟨e, he⟩ := quotient_comp_lift_surjective S
    ((LinearMap.range S.f.hom).mkQ b)
  have hmem : lift S e - b ∈ LinearMap.range S.f.hom := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (LinearMap.range S.f.hom).mkQ (lift S e - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  obtain ⟨a, ha⟩ := hmem
  exact ⟨(a, e), by simp only [joint, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.snd_apply, LinearMap.fst_apply]; rw [ha]; abel⟩

/-- The actual pullback relation module, retaining the original modules and maps. -/
abbrev PullbackTerm := LinearMap.ker (joint S)

/-- The constructed predecessor comparison. -/
def predecessor : PullbackTerm S →ₗ[R] S.X₁ :=
  LinearMap.fst R S.X₁ (FreeTerm S) ∘ₗ (LinearMap.ker (joint S)).subtype

/-- The actual next differential in the replacement. -/
def differential : PullbackTerm S →ₗ[R] FreeTerm S :=
  LinearMap.snd R S.X₁ (FreeTerm S) ∘ₗ (LinearMap.ker (joint S)).subtype

/-- The actual comparison commutes with the original differential. -/
theorem comparison_commutes :
    lift S ∘ₗ differential S = S.f.hom ∘ₗ predecessor S := by
  apply LinearMap.ext
  intro x
  exact sub_eq_zero.mp x.2

/-- The pullback relation module is flat whenever the two original terms are flat. -/
theorem pullback_flat [Module.Flat R S.X₁] [Module.Flat R S.X₂] :
    Module.Flat R (PullbackTerm S) := by
  let : Module.Flat R (S.X₁ × FreeTerm S) := ModularCurves.Module.Flat.prod
  let : Module.Flat R ((S.X₁ × FreeTerm S) ⧸ LinearMap.ker (joint S)) :=
    Module.Flat.of_linearEquiv ((joint S).quotKerEquivOfSurjective (joint_surjective S))
  exact ModularCurves.Module.Flat.of_flat_quotient _

/-- The next outgoing differential after the actual replacement. -/
def outgoing : FreeTerm S →ₗ[R] S.X₃ := S.g.hom ∘ₗ lift S

/-- The constructed replacement is a genuine complex. -/
theorem outgoing_comp_differential : outgoing S ∘ₗ differential S = 0 := by
  change S.g.hom ∘ₗ (lift S ∘ₗ differential S) = 0
  rw [comparison_commutes]
  change (S.g.hom ∘ₗ S.f.hom) ∘ₗ predecessor S = 0
  have hzero : S.g.hom ∘ₗ S.f.hom = 0 := by
    ext x
    exact S.moduleCat_zero_apply x
  rw [hzero, LinearMap.zero_comp]

omit [IsNoetherianRing R] in
/-- A comparison inducing the same original relations induces an isomorphism
on native cokernels. This is an algebraic criterion used below with the
constructed pure pullback sequence. -/
theorem opcyclesMap_isIso_of_relations
    {T U : ShortComplex (ModuleCat.{u} R)} (φ : T ⟶ U)
    (hcover : ∀ b : U.X₂, ∃ a : U.X₁, ∃ e : T.X₂, φ.τ₂ e - U.f a = b)
    (hrelations : ∀ (a : U.X₁) (e : T.X₂), φ.τ₂ e = U.f a →
      ∃ z : T.X₁, T.f z = e) :
    IsIso (ShortComplex.opcyclesMap φ) := by
  apply (ConcreteCategory.isIso_iff_bijective (ShortComplex.opcyclesMap φ)).mpr
  have hT := (ModuleCat.epi_iff_surjective T.pOpcycles).mp inferInstance
  have hU := (ModuleCat.epi_iff_surjective U.pOpcycles).mp inferInstance
  have hnatural (e : T.X₂) :
      ShortComplex.opcyclesMap φ (T.pOpcycles e) = U.pOpcycles (φ.τ₂ e) := by
    exact ConcreteCategory.congr_hom (ShortComplex.p_opcyclesMap φ) e
  constructor
  · intro x y hxy
    obtain ⟨e₁, rfl⟩ := hT x
    obtain ⟨e₂, rfl⟩ := hT y
    rw [hnatural, hnatural] at hxy
    obtain ⟨a, ha⟩ := (U.moduleCat_pOpcycles_eq_iff _ _).mp hxy
    have he : φ.τ₂ (e₁ - e₂) = U.f a := by
      rw [map_sub]
      exact ha.symm
    obtain ⟨z, hz⟩ := hrelations a (e₁ - e₂) he
    exact (T.moduleCat_pOpcycles_eq_iff _ _).mpr ⟨z, hz⟩
  · intro y
    obtain ⟨b, rfl⟩ := hU y
    obtain ⟨a, e, he⟩ := hcover b
    refine ⟨T.pOpcycles e, ?_⟩
    rw [hnatural]
    apply (U.moduleCat_pOpcycles_eq_iff _ _).mpr
    exact ⟨a, by rw [← he]; abel⟩

/-- The actual replacement short complex. -/
def replacement : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (differential S) (outgoing S) (outgoing_comp_differential S)

/-- The actual comparison from the constructed replacement to the original complex. -/
def comparison : replacement S ⟶ S where
  τ₁ := ModuleCat.ofHom (predecessor S)
  τ₂ := ModuleCat.ofHom (lift S)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ModuleCat.hom_ext
    exact (comparison_commutes S).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    rfl

/-- The comparison on actual cokernels is an isomorphism. -/
theorem comparison_opcycles_isIso : IsIso (ShortComplex.opcyclesMap (comparison S)) := by
  apply opcyclesMap_isIso_of_relations
  · intro b
    obtain ⟨⟨a, e⟩, he⟩ := joint_surjective S b
    exact ⟨a, e, he⟩
  · intro a e he
    refine ⟨⟨(a, e), ?_⟩, rfl⟩
    exact sub_eq_zero.mpr he

/-- The constructed replacement computes the native original middle homology. -/
def homologyIso : (replacement S).homology ≅ S.homology := by
  let : IsIso (ShortComplex.opcyclesMap (comparison S)) := comparison_opcycles_isIso S
  let : Mono (comparison S).τ₃ := by change Mono (𝟙 S.X₃); infer_instance
  let : IsIso (ShortComplex.homologyMap (comparison S)) :=
    ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap (comparison S))

/-- Actual scalar extension of the original three modules and their original maps. -/
def baseChangeComplex (U : ShortComplex (ModuleCat.{u} R))
    (T : Type u) [CommRing T] [Algebra R T] : ShortComplex (ModuleCat.{u} T) :=
  ShortComplex.moduleCatMk (U.f.hom.baseChange T) (U.g.hom.baseChange T) (by
    rw [← LinearMap.baseChange_comp]
    have hz : U.g.hom ∘ₗ U.f.hom = 0 := by ext x; exact U.moduleCat_zero_apply x
    rw [hz, LinearMap.baseChange_zero])

/-- Actual scalar extension of a comparison, with no supplied cohomology map. -/
def baseChangeComparison {U V : ShortComplex (ModuleCat.{u} R)} (φ : U ⟶ V)
    (T : Type u) [CommRing T] [Algebra R T] :
    baseChangeComplex U T ⟶ baseChangeComplex V T where
  τ₁ := ModuleCat.ofHom (φ.τ₁.hom.baseChange T)
  τ₂ := ModuleCat.ofHom (φ.τ₂.hom.baseChange T)
  τ₃ := ModuleCat.ofHom (φ.τ₃.hom.baseChange T)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change V.f.hom.baseChange T ∘ₗ φ.τ₁.hom.baseChange T =
      φ.τ₂.hom.baseChange T ∘ₗ U.f.hom.baseChange T
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact ModuleCat.hom_ext_iff.mp φ.comm₁₂
  comm₂₃ := by
    apply ModuleCat.hom_ext
    change V.g.hom.baseChange T ∘ₗ φ.τ₂.hom.baseChange T =
      φ.τ₃.hom.baseChange T ∘ₗ U.g.hom.baseChange T
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact ModuleCat.hom_ext_iff.mp φ.comm₂₃

variable (T : Type u) [CommRing T] [Algebra R T]

/-- The actual tensor-product/product isomorphism respects the joint map. -/
theorem joint_baseChange_apply (x : T ⊗[R] (S.X₁ × FreeTerm S)) :
    (joint S).baseChange T x =
      (lift S).baseChange T
          ((TensorProduct.prodRight R T T S.X₁ (FreeTerm S) x).2) -
        S.f.hom.baseChange T
          ((TensorProduct.prodRight R T T S.X₁ (FreeTerm S) x).1) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t x =>
    simp [joint, LinearMap.baseChange_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]
    abel

/-- The actual tensor differential is the second projection of the scalar-extended
relation inclusion. -/
theorem differential_baseChange_apply (x : T ⊗[R] PullbackTerm S) :
    (differential S).baseChange T x =
      (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)
        ((LinearMap.ker (joint S)).subtype.baseChange T x)).2 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t x => rfl
  | add x y hx hy => simp only [map_add, hx, hy, Prod.snd_add]

/-- Purity of the actual surjective joint map constructs the kernel comparison
after every scalar extension. Only flatness of its original target is needed. -/
theorem joint_kernel_baseChange_bijective [Module.Flat R S.X₂] :
    Function.Bijective (ModularCurves.kerBaseChangeComparison T (joint S)) := by
  let : Module.Flat R (S.X₂ ⧸ LinearMap.range (joint S)) := by
    have hr : LinearMap.range (joint S) = ⊤ :=
      LinearMap.range_eq_top.mpr (joint_surjective S)
    rw [hr]
    infer_instance
  exact ModularCurves.kerBaseChangeComparison_bijective T (joint S)

/-- The constructed replacement induces an actual cokernel isomorphism after
every algebra base change; no cycle or cohomology comparison is assumed. -/
theorem baseChange_comparison_opcycles_isIso [Module.Flat R S.X₂] :
    IsIso (ShortComplex.opcyclesMap (baseChangeComparison (comparison S) T)) := by
  apply opcyclesMap_isIso_of_relations
  · intro b
    obtain ⟨x, hx⟩ := LinearMap.baseChange_surjective T (joint_surjective S) b
    refine ⟨(TensorProduct.prodRight R T T S.X₁ (FreeTerm S) x).1,
      (TensorProduct.prodRight R T T S.X₁ (FreeTerm S) x).2, ?_⟩
    exact (joint_baseChange_apply S T x).symm.trans hx
  · intro a e he
    let x := (TensorProduct.prodRight R T T S.X₁ (FreeTerm S)).symm (a, e)
    have hx : (joint S).baseChange T x = 0 := by
      rw [joint_baseChange_apply]
      simp only [x, LinearEquiv.apply_symm_apply]
      exact sub_eq_zero.mpr he
    obtain ⟨z, hz⟩ := (joint_kernel_baseChange_bijective S T).surjective ⟨x, hx⟩
    refine ⟨z, ?_⟩
    change (differential S).baseChange T z = e
    rw [differential_baseChange_apply]
    have hval := congrArg Subtype.val hz
    change (LinearMap.ker (joint S)).subtype.baseChange T z = x at hval
    rw [hval]
    simp only [x, LinearEquiv.apply_symm_apply]
    rfl

/-- The actual scalar-extended replacement computes the native homology of
the original scalar-extended complex, for every algebra base change. -/
def baseChangeHomologyIso [Module.Flat R S.X₂] :
    (baseChangeComplex (replacement S) T).homology ≅
      (baseChangeComplex S T).homology := by
  let : IsIso (ShortComplex.opcyclesMap
      (baseChangeComparison (comparison S) T)) := baseChange_comparison_opcycles_isIso S T
  have hthird : (baseChangeComparison (comparison S) T).τ₃ = 𝟙 _ := by
    apply ModuleCat.hom_ext
    change (LinearMap.id : S.X₃ →ₗ[R] S.X₃).baseChange T = LinearMap.id
    exact LinearMap.baseChange_id
  let : Mono (baseChangeComparison (comparison S) T).τ₃ := by
    rw [hthird]
    change Mono (𝟙 (ModuleCat.of T (T ⊗[R] S.X₃)))
    infer_instance
  let : IsIso (ShortComplex.homologyMap
      (baseChangeComparison (comparison S) T)) :=
    ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono inferInstance inferInstance
  exact asIso (ShortComplex.homologyMap (baseChangeComparison (comparison S) T))

end EnvelopeProperty.Vanishing.SpecializationDerivedReplacementStep
