import EnvelopeProperty.AlgGeom.IntegralSchemeDimension
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras
import EnvelopeProperty.Char0.ResidueTrdeg

/-! # Actual finite-type dimensions from the SAME original native function field -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeFunctionFieldDimension

private theorem trdeg_eq_of_algebraic (k A K : Type u) [Field k] [CommRing A]
    [IsDomain A] [CommRing K] [NoZeroDivisors K] [Algebra k A] [Algebra k K]
    [Algebra A K] [IsScalarTower k A K] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] :
    Algebra.trdeg k A = Algebra.trdeg k K := by
  have h := trdeg_add_eq k A (A := K)
  rwa [trdeg_eq_zero (R := A),add_zero] at h

/-- The SAME actual finite-type domain's dimension is its original fraction
field degree, derived by genuine Noether normalization and going-up. -/
theorem affine_dimension_eq (k A K : Type u) [Field k] [CommRing A] [IsDomain A]
    [Field K] [Algebra k A] [Algebra.FiniteType k A] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] (d : ℕ) (htr : Algebra.trdeg k K = d) :
    ringKrullDim A = d := by
  obtain ⟨n,f,hf,hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Module.Finite P A := hfin
  let : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hf
  let : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hP : ringKrullDim P = n := by
    simp [P,MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hd : ringKrullDim A = n := by
    apply le_antisymm
    · exact (EnvelopeProperty.ringKrullDim_le_of_isIntegral f.toRingHom
        (algebraMap_isIntegral_iff.mpr inferInstance)).trans_eq hP
    · exact hP ▸ IntegralSchemeDimension.ringKrullDim_le_of_isIntegral_of_injective
        f.toRingHom (algebraMap_isIntegral_iff.mpr inferInstance) hf
  have hA : Algebra.trdeg k A = n := by
    rw [← trdeg_eq_of_algebraic k P A]
    simp [P]
  let : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have hK : Algebra.trdeg k K = n := (trdeg_eq_of_algebraic k A K).symm.trans hA
  have hnd : n = d := by exact_mod_cast hK.symm.trans htr
  simpa only [hnd] using hd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem dimension_le_of_affine_sections (X : Scheme.{u}) (d : ℕ)
    (h : ∀ U : X.affineOpens, Nonempty U.1 → ringKrullDim Γ(X,U.1) ≤ d) :
    topologicalKrullDim X ≤ d := by
  change Order.krullDim (IrreducibleCloseds X) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨_,⟨U,hU,rfl⟩,hx,-⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
      (⊤ : X.Opens).isOpen
  obtain ⟨z,hz⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  rw [← hz,coheight_eq_of_isOpenImmersion hU.fromSpec]
  have hdim : topologicalKrullDim (Spec Γ(X,U)) ≤ d := by
    change topologicalKrullDim (PrimeSpectrum Γ(X,U)) ≤ d
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact h ⟨U,hU⟩ ⟨⟨x,hx⟩⟩
  have ho : Order.krullDim (Spec Γ(X,U)) ≤ d := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Spec Γ(X,U)))]
    exact hdim
  exact (Order.coheight_le_krullDim z).trans ho

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- EVERY original nonempty affine section ring has the true original
function-field dimension for the SAME native structure-map coefficients. -/
theorem affineSections_dimension_eq (U : X.affineOpens) [Nonempty U.1] (d : ℕ)
    (htr : letI := f.stalkAlgebra (genericPoint X); Algebra.trdeg k X.functionField = d) :
    ringKrullDim Γ(X,U.1) = d := by
  let := f.sectionsAlgebra U.1
  let := f.stalkAlgebra (genericPoint X)
  let : IsScalarTower k Γ(X,U.1) X.functionField :=
    f.isScalarTower_sectionsAlgebra_stalk U.1
      (((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by simpa using ‹Nonempty U.1›))
  let : Algebra.FiniteType k Γ(X,U.1) := f.finiteType_sectionsAlgebra U.2
  let : IsFractionRing Γ(X,U.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  exact affine_dimension_eq k Γ(X,U.1) X.functionField d htr

/-- The whole SAME actual scheme dimension is derived from actual local finite
type and native generic-stalk degree; no dimension certificate is assumed. -/
theorem topologicalKrullDim_eq (d : ℕ)
    (htr : letI := f.stalkAlgebra (genericPoint X); Algebra.trdeg k X.functionField = d) :
    topologicalKrullDim X = d := by
  apply le_antisymm
  · apply dimension_le_of_affine_sections X d
    intro U hU
    let := hU
    exact (affineSections_dimension_eq f U d htr).le
  · let x := genericPoint X
    obtain ⟨_,⟨U,hU,rfl⟩,hx,-⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
        (⊤ : X.Opens).isOpen
    let : Nonempty U := ⟨⟨x,hx⟩⟩
    have hd := affineSections_dimension_eq f ⟨U,hU⟩ d htr
    have hle := hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum Γ(X,U)) ≤ topologicalKrullDim X at hle
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,hd] at hle

end EnvelopeProperty.SchemeFunctionFieldDimension
