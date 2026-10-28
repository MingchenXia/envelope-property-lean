import EnvelopeProperty.AffineDimension
import EnvelopeProperty.FiniteTypeFieldPoint
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Genuine dimensions and reduced closures of affine curves

Dimension at most one is local for open neighbourhoods. In an integral scheme
locally of finite type over a field, all nonempty affine coordinate rings have
the same dimension: a common principal affine open compares them using actual
localization dimension invariance. These facts will retain dimension one in
the actual reduced closed closure of every affine curve.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u

namespace EnvelopeProperty.FcSchemeCurveDimensions

/-- A neighbourhood cover by spaces of dimension at most one bounds the
dimension of the whole space. Restriction to an open meeting the smallest
member retains every strict step of a chain of irreducible closed subsets. -/
theorem topologicalKrullDim_le_one_of_open_neighbourhoods
    {T : Type*} [TopologicalSpace T]
    (h : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U ≤ 1) :
    topologicalKrullDim T ≤ 1 := by
  change Order.krullDim (IrreducibleCloseds T) ≤ 1
  rw [Order.krullDim_le_one_iff]
  intro Z
  by_cases hmin : IsMin Z
  · exact Or.inl hmin
  right
  rw [isMax_iff_forall_not_lt]
  intro Y hZY
  obtain ⟨W, hWZ⟩ := not_isMin_iff.mp hmin
  obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
  obtain ⟨U, hxU, hdim⟩ := h x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (Subtype.val : U → T)
    U.isOpen.isOpenEmbedding_subtypeVal
  let W' : {C : IrreducibleCloseds T | ((Subtype.val : U → T) ⁻¹' C).Nonempty} :=
    ⟨W, ⟨⟨x, hxU⟩, hx⟩⟩
  let Z' : {C : IrreducibleCloseds T | ((Subtype.val : U → T) ⁻¹' C).Nonempty} :=
    ⟨Z, ⟨⟨x, hxU⟩, hWZ.le hx⟩⟩
  let Y' : {C : IrreducibleCloseds T | ((Subtype.val : U → T) ⁻¹' C).Nonempty} :=
    ⟨Y, ⟨⟨x, hxU⟩, hZY.le (hWZ.le hx)⟩⟩
  have hwz : e.symm W' < e.symm Z' := e.symm.strictMono hWZ
  have hzy : e.symm Z' < e.symm Y' := e.symm.strictMono hZY
  obtain hzmin | hzmax := Order.krullDim_le_one_iff.mp hdim (e.symm Z')
  · exact hzmin.not_lt hwz
  · exact hzmax.not_lt hzy

variable {F : Type u} [Field F] {X : Scheme.{u}}

/-- The actual coordinate ring of a nonempty principal affine open has the
entire dimension of the original finite-type integral affine coordinate ring. -/
theorem ringKrullDim_basicOpen (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] (r : Γ(X, U)) (hr : r ≠ 0) :
    ringKrullDim Γ(X, X.basicOpen r) = ringKrullDim Γ(X, U) := by
  let : Algebra F Γ(X, U) := (FiniteTypePoint.affineBaseMap f hU).toAlgebra
  have : Algebra.FiniteType F Γ(X, U) := FiniteTypePoint.affineBaseMap_finiteType f hU
  let : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(X, X.basicOpen r) :=
    hU.isLocalization_of_eq_basicOpen r (homOfLE (X.basicOpen_le r)) rfl
  let e := IsLocalization.algEquiv (Submonoid.powers r)
    (Localization.Away r) Γ(X, X.basicOpen r)
  exact (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans
    (ringKrullDim_localizationAway_of_finiteType_domain F Γ(X, U) r hr)

/-- Every two nonempty affine opens of an integral finite-type scheme have the
same actual ring dimension, compared through a constructed common principal
open. No global dimension or equidimensionality assumption is an input. -/
theorem ringKrullDim_affine_eq (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] [IsIntegral X] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) [Nonempty U] [Nonempty V] :
    ringKrullDim Γ(X, U) = ringKrullDim Γ(X, V) := by
  have hUn : (U : Set X).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨x.1, x.2⟩
  have hVn : (V : Set X).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    exact ⟨x.1, x.2⟩
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen
    hUn hVn
  obtain ⟨r, s, hrs, hxr⟩ := exists_basicOpen_le_affine_inter hU hV x ⟨hxU, hxV⟩
  have hr : r ≠ 0 := by
    intro he
    simp only [he, Scheme.basicOpen_zero, Opens.mem_bot] at hxr
  have hs : s ≠ 0 := by
    intro he
    rw [hrs, he, Scheme.basicOpen_zero] at hxr
    exact hxr
  have hd := ringKrullDim_basicOpen f hU r hr
  rw [hrs] at hd
  exact hd.symm.trans (ringKrullDim_basicOpen f hV s hs)

/-- Actual affine scheme dimension is the dimension of its actual coordinate
ring, through the canonical spectrum isomorphism. -/
theorem topologicalKrullDim_affine {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim U = ringKrullDim Γ(X, U) := by
  calc
    topologicalKrullDim U = topologicalKrullDim (Spec Γ(X, U)) :=
      IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(X, U) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)

/-- An actual integral scheme locally of finite type over a field is a genuine
curve as soon as one nonempty actual affine coordinate ring has dimension one.
The global topological dimension is proved, rather than presumed. -/
theorem topologicalKrullDim_eq_one_of_affine (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] (hdim : ringKrullDim Γ(X, U) = 1) :
    topologicalKrullDim X = 1 := by
  apply le_antisymm
  · apply topologicalKrullDim_le_one_of_open_neighbourhoods
    intro x
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    let : Nonempty V := ⟨⟨x, hxV⟩⟩
    refine ⟨V, hxV, ?_⟩
    change topologicalKrullDim V.toScheme ≤ 1
    rw [topologicalKrullDim_affine hV, ← ringKrullDim_affine_eq f hU hV, hdim]
  · rw [← hdim, ← topologicalKrullDim_affine hU]
    exact topologicalKrullDim_subspace_le X (U : Set X)

/-- The actual closed subscheme constructed from a closed set's vanishing ideal
is reduced, including on charts where the closed set is empty. -/
theorem isReduced_vanishingIdeal_subscheme (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have : ∀ U : I.subschemeCover.openCover.I₀, IsReduced (I.subschemeCover.openCover.X U) := by
    intro U
    let V : X.affineOpens := U
    have := hred V
    exact inferInstanceAs (IsReduced (Spec (CommRingCat.of (Γ(X, V.1) ⧸ I.ideal V))))
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

/-- Every actual nonempty irreducible closed subset of a scheme has its
constructed integral reduced closed subscheme structure. -/
theorem isIntegral_vanishingIdeal_subscheme (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    isReduced_vanishingIdeal_subscheme Z
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Subtype.irreducibleSpace hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Close an actual affine prime curve in the ORIGINAL scheme, with its actual
integral reduced closed subscheme structure and its full global dimension one.
Its whole restriction to the original affine chart is exactly the given curve. -/
theorem exists_closed_integral_curve_of_affine_prime
    (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) (P : Ideal Γ(X, U))
    (hP : P.IsPrime) (hdim : ringKrullDim (Γ(X, U) ⧸ P) = 1) :
    ∃ I : X.IdealSheafData, IsIntegral I.subscheme ∧
      topologicalKrullDim I.subscheme = 1 ∧
      hU.fromSpec ⁻¹' (I.support : Set X) = PrimeSpectrum.zeroLocus (P : Set Γ(X, U)) := by
  let ι : PrimeSpectrum Γ(X, U) → X := hU.fromSpec
  have hι : Topology.IsOpenEmbedding ι := hU.fromSpec.isOpenEmbedding
  have hcurve : IsIrreducible (PrimeSpectrum.zeroLocus (P : Set Γ(X, U))) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical P hP.isRadical).mpr hP
  let Z : Closeds X := ⟨closure (ι '' PrimeSpectrum.zeroLocus (P : Set Γ(X, U))),
    isClosed_closure⟩
  have hZ : IsIrreducible (Z : Set X) :=
    (hcurve.image ι hι.continuous.continuousOn).closure
  have hpre : ι ⁻¹' (Z : Set X) = PrimeSpectrum.zeroLocus (P : Set Γ(X, U)) :=
    hι.isOpenMap.preimage_closure_image
      hι.injective hι.continuous _
      (PrimeSpectrum.isClosed_zeroLocus _)
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : IsIntegral I.subscheme := isIntegral_vanishingIdeal_subscheme Z hZ
  have hIP : I.ideal ⟨U, hU⟩ = P := by
    change PrimeSpectrum.vanishingIdeal (ι ⁻¹' (Z : Set X)) = P
    rw [hpre, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hP.isRadical.radical]
  let V := I.subschemeι ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage I.subschemeι
  obtain ⟨ξ, hξ⟩ := hcurve.nonempty
  have hξZ : ι ξ ∈ I.support := subset_closure ⟨ξ, hξ, rfl⟩
  have hξrange : ι ξ ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hξZ
  obtain ⟨c, hc⟩ := hξrange
  have hξU : ι ξ ∈ U := (hU.isoSpec.inv ξ).2
  have : Nonempty V := ⟨⟨c, by
    change I.subschemeι c ∈ U
    rw [hc]
    exact hξU⟩⟩
  have hVdim : ringKrullDim Γ(I.subscheme, V) = 1 := by
    have he := ringKrullDim_eq_of_ringEquiv
      (I.subschemeObjIso ⟨U, hU⟩).commRingCatIsoToRingEquiv
    change ringKrullDim Γ(I.subscheme, V) = ringKrullDim (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩) at he
    rw [hIP] at he
    exact he.trans hdim
  refine ⟨I, hI, topologicalKrullDim_eq_one_of_affine (I.subschemeι ≫ f) hV hVdim, ?_⟩
  exact hpre

end EnvelopeProperty.FcSchemeCurveDimensions
