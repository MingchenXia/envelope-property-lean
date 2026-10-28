import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionEquation
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionAffineComponent
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionDimension
import EnvelopeProperty.AlgGeom.SchemeCurveDimensions

/-! # Whole dimensions of actual original polynomial-cut components

Every nonempty original affine computes the entire integral field-finite-type
scheme dimension. The actual SAME pulled polynomial cut supplies its own
nonzero local equation, minimal component prime and true quotient section
ring, giving the whole component dimension without matching certificates.
-/
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry TopologicalSpace
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionSchemeDimension
variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- EVERY actual nonempty affine of the original integral field-finite-type scheme computes its WHOLE dimension. -/
theorem whole_dimension_eq_affine (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    topologicalKrullDim Y = ringKrullDim Γ(Y, U) := by
  apply le_antisymm
  · change Order.krullDim (IrreducibleCloseds Y) ≤ ringKrullDim Γ(Y, U)
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y)),
      Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun y => ?_
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ (⊤ : Y.Opens) from trivial)
    let : Nonempty V := ⟨⟨y, hyV⟩⟩
    let q : Spec Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩
    have hqy : hV.fromSpec q = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    rw [← hqy, coheight_eq_of_isOpenImmersion hV.fromSpec]
    have hspec : Order.krullDim (Spec Γ(Y, V)) = ringKrullDim Γ(Y, V) := by
      rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Spec Γ(Y, V)))]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(Y, V)
    exact (Order.coheight_le_krullDim q).trans
      (hspec.trans (FcSchemeCurveDimensions.ringKrullDim_affine_eq p hV hU)).le
  · exact (FcSchemeCurveDimensions.topologicalKrullDim_affine hU).symm.le.trans
      (topologicalKrullDim_subspace_le Y (U : Set Y))

/-- EVERY actual reduced component of the SAME proper original polynomial cut has the exact WHOLE dimension. -/
theorem original_cut_component_dimension_add_one
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [IsIntegral Y]
    {R : Type u} [CommRing R] {n : ℕ} (i : Y ⟶ NativeProjectiveScheme R n)
    {d : ℕ} (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d)
    (hproper : (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).support ≠ ⊤)
    (Z : Closeds (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).subscheme)
    (hZ : (Z : Set (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).subscheme) ∈
      irreducibleComponents (PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF).subscheme) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme + 1 =
      topologicalKrullDim Y := by
  let K := PLGaussVerticalCurveSurfaceSelectionSheaf.originalHypersurfaceCut i F hF
  let E := Scheme.IdealSheafData.vanishingIdeal Z
  let D : Scheme.{u} := E.subscheme
  let j : D ⟶ Y := E.subschemeι ≫ K.subschemeι
  let : IsIntegral D := FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme Z hZ.1
  let : IsClosedImmersion j := inferInstance
  obtain ⟨z, hz⟩ := hZ.1.nonempty
  let y : Y := K.subschemeι z
  have hcover : i y ∈ (⨆ a : Fin (n + 1), nativeCoordinateOpen (R := R) a) := by
    rw [iSup_nativeCoordinateOpen_eq_top]
    trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hcover
  obtain ⟨U, hU, hyU, hUa⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ i ⁻¹ᵁ nativeCoordinateOpen a from ha)
  let U' : Y.affineOpens := ⟨U, hU⟩
  let : Nonempty U := ⟨⟨y, hyU⟩⟩
  have hmeet : ((Z : Set K.subscheme) ∩ (K.subschemeι ⁻¹ᵁ U)).Nonempty := ⟨z, hz, hyU⟩
  let f : Γ(Y, U) := (i.appLE (nativeCoordinateOpen a) U hUa) (nativeFormSection a F)
  have hprincipal : K.ideal U' = Ideal.span {f} :=
    PLGaussVerticalCurveSurfaceSelectionEquation.originalHypersurfaceCut_affineIdeal i F hF U' a hUa
  have hfnz : f ≠ 0 := by
    intro hf
    have hzero : K.ideal U' = ⊥ := by rw [hprincipal, hf, Ideal.span_singleton_zero]
    have hsubset : (U : Set Y) ⊆ K.support := by
      intro x hx
      apply (Scheme.IdealSheafData.mem_support_iff_of_mem (I := K) (U := U') hx).mpr
      rw [Scheme.mem_zeroLocus_iff]
      intro s hs
      have hs0 : s = 0 := by
        have hs' : s ∈ K.ideal U' := hs
        rw [hzero] at hs'
        exact Ideal.mem_bot.mp hs'
      subst s
      simp
    have hclosure : closure (U : Set Y) ⊆ K.support := closure_minimal hsubset K.support.isClosed
    have hdense := U.isOpen.dense (show (U : Set Y).Nonempty from ⟨y, hyU⟩)
    apply hproper
    apply SetLike.coe_injective
    exact Set.Subset.antisymm (Set.subset_univ _) (fun x _ => hclosure (hdense x))
  let P := j.ker.ideal U'
  have hP : P ∈ (K.ideal U').minimalPrimes :=
    PLGaussVerticalCurveSurfaceSelectionAffineComponent.cut_component_affineIdeal_mem_minimalPrimes
      K Z hZ hU hmeet
  have hPf : P ∈ (Ideal.span {f}).minimalPrimes := by rwa [hprincipal] at hP
  let : Algebra k Γ(Y, U) := (FiniteTypePoint.affineBaseMap p hU).toAlgebra
  let : Algebra.FiniteType k Γ(Y, U) := FiniteTypePoint.affineBaseMap_finiteType p hU
  have hdimP := PLGaussVerticalCurveSurfaceSelectionDimension.principal_component_dimension_add_one
    k Γ(Y, U) f hfnz P hPf
  have hzrange : z ∈ Set.range E.subschemeι := by
    rw [E.range_subschemeι]
    exact hz
  obtain ⟨w, hw⟩ := hzrange
  have hwy : j w = y := by change K.subschemeι (E.subschemeι w) = K.subschemeι z; rw [hw]
  let V := j ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage j
  let : Nonempty V := ⟨⟨w, by change j w ∈ U; rw [hwy]; exact hyU⟩⟩
  have hquot : ringKrullDim Γ(D, V) = ringKrullDim (Γ(Y, U) ⧸ P) := by
    have hk : P = RingHom.ker (j.app U).hom := j.ker_apply U'
    rw [hk]
    exact (ringKrullDim_eq_of_ringEquiv
      ((j.app U).hom.quotientKerEquivOfSurjective (j.app_surjective U hU))).symm
  calc
    topologicalKrullDim D + 1 = ringKrullDim Γ(D, V) + 1 :=
      congrArg (fun q => q + 1) (whole_dimension_eq_affine (j ≫ p) hV)
    _ = ringKrullDim (Γ(Y, U) ⧸ P) + 1 := congrArg (fun q => q + 1) hquot
    _ = ringKrullDim Γ(Y, U) := hdimP
    _ = topologicalKrullDim Y := (whole_dimension_eq_affine p hU).symm

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionSchemeDimension
