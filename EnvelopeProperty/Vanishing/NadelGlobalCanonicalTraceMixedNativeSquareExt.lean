import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquareCoordinate

/-! # The original mixed native square commutes as a whole map

Let `k` be a field and `A` a `k`-algebra with étale coordinates `x: Fin n → A`, i.e.
`k[X₁, …, Xₙ] → A`, `Xⱼ ↦ xⱼ`, is étale. Let `B = A[t]/(tᵢ^{Nᵢ} - dᵢ)` be the mixed Kummer ring
(`mixedRing x N I σ u`), `S = A[sᵢ]/(sᵢ^{Nᵢ} - uᵢ)` the étale unit cover (`UnitCover N u`),
`C = S ⊗_A B` (`extendedMixedRing`) and `P` the pure Kummer ring over `S`
(`mixedPureRing`), with the purification `C ≃ P` over `S`. Write `Ω_R = Γ(Ω^n_{R/k})`.

The two native maps of the mixed square (`NadelGlobalCanonicalTraceMixedNativeSquareMaps`)
are `S`-linear maps `S ⊗_A Ω_A ⟶ Ω_P`:
* `originalMixedNativeSquareLeft`: `S ⊗ dφ_B`, then `S ⊗_A Ω_B ≅ Ω_C` and `Ω_C ≅ Ω_P`;
* `originalMixedNativeSquareRightAligned`: `S ⊗_A Ω_A ≅ Ω_S`, then the pure differential
  `Ω_S ⟶ Ω_P`.

The main result `originalMixedNativeSquareLeft_eq_rightAligned` says that they are equal.
Mathematically, both maps send `1 ⊗ dx₁ ∧ ⋯ ∧ dxₙ` to the coordinate wedge of the images of
the `xⱼ` in `P` (the two images agree by the ring square of the purification), and
`Ω_A` is free of rank one on `dx₁ ∧ ⋯ ∧ dxₙ` because the coordinates are étale; a morphism
out of a scalar extension of a cyclic module is determined by its value on the generator.

The value on the generator is accepted coordinate theorem
`mixedNativeCanonicalSquare_coordinate` (stated through module-restriction carriers); this file
only joins it with the source readback `mixedNativeCanonicalSquare_source_point_aligned_coordinate`
and the generation of `Ω_A`.

## Proof design

No concrete composite is written by hand: the abstract assembly lemma
`mixedNativeSquare_finish` reads every concrete map off the types of the accepted theorems and
of the two definitions by unification, so the kernel only performs structural comparisons. The
one exception is the restricted input section of the coordinate theorem, which is passed
literally: when it is assigned by unification it is unfolded, and the kernel then evaluates the
purification comparison (beyond 5 GB) to identify the two presentations. The identification of
the purification comparison with the iso of the coordinate theorem, and of the unit-cover
comparison with its native composite, are single definitional unfoldings.

This is, the normalization identity, of relative Nadel vanishing.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace

open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed NadelCanonicalMixed.Split
open scoped TensorProduct

/-! ### Abstract statements -/

section Abstract

variable {R S : Type u} [CommRing R] [CommRing S] (α : R →+* S)

/-- A morphism out of the scalar extension `S ⊗_R M` of a cyclic `R`-module `M = R • m₀` is
determined by its value on `1 ⊗ m₀ = unit m₀`. -/
theorem extendScalars_hom_ext_of_generator {M : ModuleCat.{u} R} {P : ModuleCat.{u} S}
    {f g : (ModuleCat.extendScalars α).obj M ⟶ P} (m₀ : M)
    (hgen : ∀ m : M, ∃ r : R, m = r • m₀)
    (h : f ((ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀) =
      g ((ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀)) :
    f = g := by
  apply ((ModuleCat.extendRestrictScalarsAdj α).homEquiv M P).injective
  ext m
  obtain ⟨r, rfl⟩ := hgen m
  have hf : ((ModuleCat.extendRestrictScalarsAdj α).homEquiv M P f) m₀ =
      f ((ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀) := rfl
  have hg : ((ModuleCat.extendRestrictScalarsAdj α).homEquiv M P g) m₀ =
      g ((ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀) := rfl
  simp only [map_smul, hf, hg, h]

/-- Abstract assembly of the whole square `F ≫ G ≫ H = U ≫ D` out of a scalar extension of a
cyclic module `M = R • m₀`: the source readback `hS`, `hI` identifies `G (F (unit m₀))` with `r`,
and the coordinate identity `hC` (stated through module-restriction carriers, as the accepted
coordinate theorem) identifies the two values at `unit m₀`. The identities `hH`, `hU`, `hv` are
the definitional unfoldings of the concrete comparisons. -/
theorem mixedNativeSquare_finish {T C : Type u} [CommRing T] [CommRing C]
    (β : S →+* T) (γ : S →+* C) {M M' : ModuleCat.{u} R} {Q : ModuleCat.{u} T}
    {Y : ModuleCat.{u} C} {X₃ : ModuleCat.{u} S}
    (Lf Rt : (ModuleCat.extendScalars α).obj M ⟶ (ModuleCat.restrictScalars β).obj Q)
    (F₀ : M ⟶ M') (G : (ModuleCat.extendScalars α).obj M' ⟶ (ModuleCat.restrictScalars γ).obj Y)
    (H H' : (ModuleCat.restrictScalars γ).obj Y ⟶ (ModuleCat.restrictScalars β).obj Q)
    (U U' : (ModuleCat.extendScalars α).obj M ⟶ X₃)
    (D : X₃ ⟶ (ModuleCat.restrictScalars β).obj Q)
    (hL : Lf = (ModuleCat.extendScalars α).map F₀ ≫ G ≫ H) (hR : Rt = U ≫ D)
    (m₀ : M) (hgen : ∀ m : M, ∃ r : R, m = r • m₀) (W : Y)
    (hS : ModuleRestrictionCarrier.toUnderlying (.of S) (.of C) γ Y
      (G (((ModuleCat.extendRestrictScalarsAdj α).unit.app M ≫
        (ModuleCat.extendScalars α ⋙ ModuleCat.restrictScalars α).map F₀) m₀)) = W)
    (r : (ModuleCat.restrictScalars γ).obj Y)
    (hI : ModuleRestrictionCarrier.toUnderlying (.of S) (.of C) γ Y r = W)
    (v : (ModuleCat.extendScalars α).obj M)
    (hC : ModuleRestrictionCarrier.toUnderlying (.of S) (.of T) β Q (H' r) =
      ModuleRestrictionCarrier.toUnderlying (.of S) (.of T) β Q (D.hom (U' v)))
    (hH : H = H') (hU : U = U')
    (hv : v = (ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀) :
    Lf = Rt := by
  subst hL hR hH hU hv
  apply extendScalars_hom_ext_of_generator α m₀ hgen
  have hGr : G ((ModuleCat.extendScalars α).map F₀
      ((ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀)) = r := hS.trans hI.symm
  change H (G ((ModuleCat.extendScalars α).map F₀
      ((ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀))) =
    D (U ((ModuleCat.extendRestrictScalarsAdj α).unit.app M m₀))
  rw [hGr]
  exact hC

end Abstract

/-! ### Generation of the base canonical sections -/

section Generation

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] {n : ℕ} (x : Fin n → A)

/-- Étale coordinates are formally étale. -/
private theorem coordinate_formallyEtale
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    (MvPolynomial.aeval (R := k) x).toRingHom.FormallyEtale := by
  let : Algebra (MvPolynomial (Fin n) k) A := (MvPolynomial.aeval (R := k) x).toRingHom.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) k) A := hx
  change Algebra.FormallyEtale (MvPolynomial (Fin n) k) A
  infer_instance

/-- The coordinate wedge `dx₁ ∧ ⋯ ∧ dxₙ` is the image of the frame generator under the affine
raw comparison of the base canonical sections. -/
private theorem baseCanonicalSectionsRawIso_inv_generator
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    (baseCanonicalSectionsRawIso (MvPolynomial.aeval (R := k) x)
        (coordinate_formallyEtale x hx)).inv
      (affineCanonicalGenerator (NadelCanonicalMixed.Split.baseDifferentialBasis
        (MvPolynomial.aeval (R := k) x) (coordinate_formallyEtale x hx))) =
      affineCanonicalCoordinateSection k (.of A) n x := by
  rw [baseCanonicalSectionsRawIso_inv_unit, baseGenerator_eq_wedge]
  have hc : originalCoordinates (MvPolynomial.aeval (R := k) x) = x :=
    funext fun j => MvPolynomial.aeval_X x j
  rw [hc]
  rfl

/-- **Generation.** Every top form on `Spec A` is an `A`-multiple of the coordinate wedge
`dx₁ ∧ ⋯ ∧ dxₙ` of étale coordinates. -/
theorem baseCanonicalSections_eq_smul_coordinate
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)) :
    ∃ r : A, w = r • affineCanonicalCoordinateSection k (.of A) n x := by
  let a := MvPolynomial.aeval (R := k) x
  let haF := coordinate_formallyEtale x hx
  let b := baseCanonicalSectionsRawIso a haF
  let bs := NadelCanonicalMixed.Split.baseDifferentialBasis a haF
  refine ⟨affineCanonicalTrivialization bs (b.hom w), ?_⟩
  have hw := affineCanonical_eq_smul_generator bs (b.hom w)
  have h₁ : w = b.inv (b.hom w) := (b.hom_inv_id_apply w).symm
  have h₂ := congrArg b.inv.hom hw
  have h₃ := b.inv.hom.map_smul (affineCanonicalTrivialization bs (b.hom w))
    (affineCanonicalGenerator bs)
  have h₄ := congrArg (fun z => affineCanonicalTrivialization bs (b.hom w) • z)
    (baseCanonicalSectionsRawIso_inv_generator x hx)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end Generation

/-! ### The whole mixed square -/

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

-- The accepted coordinate statements are deep terms (the canonical sheaves occur in the indices
-- of the module-restriction carriers); elaborating the assembly against them exceeds the default
-- recursion depth (512). Neither heartbeats nor memory are raised (peak below 0.5 GB).
set_option maxRecDepth 4000 in
/-- **The whole original mixed native square commutes** (R-mix-1):
`S ⊗ dφ_B` followed by `S ⊗_A Ω_B ≅ Ω_C ≅ Ω_P` equals `S ⊗_A Ω_A ≅ Ω_S` followed by the pure
differential `Ω_S ⟶ Ω_P`. -/
theorem originalMixedNativeSquareLeft_eq_rightAligned
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    originalMixedNativeSquareLeft (k := k) x N I σ u hx hN htame =
      originalMixedNativeSquareRightAligned (k := k) x N I σ u hx hN htame := by
  have hS := mixedNativeCanonicalSquare_source_point_aligned_coordinate (k := k) x N I σ u
    hx hN htame
  have hI := mixedNativeCanonicalSquare_restricted_input_original_coordinate (k := k) x N I σ u
    hx hN htame
  have hC := mixedNativeCanonicalSquare_coordinate (k := k) x N I σ u hx hN htame
  -- The two maps fix the composites; `hS`, `hC` fix the remaining data. The restricted input
  -- section is passed literally: unifying it through `hI` would unfold it, and the kernel would
  -- then evaluate the purification comparison to compare the two presentations. The three
  -- comparison identities are checked last, each by one unfolding.
  refine mixedNativeSquare_finish _ _ _
    (originalMixedNativeSquareLeft (k := k) x N I σ u hx hN htame)
    (originalMixedNativeSquareRightAligned (k := k) x N I σ u hx hN htame) _ _ _ _ _ _ _
    rfl rfl _ (baseCanonicalSections_eq_smul_coordinate x hx) _ hS
    (mixedNativeCanonicalSquare_restrictedInputValue (k := k) x N I σ u hx hN htame) hI _ hC
    ?hH ?hU ?hv
  case hH => exact rfl
  case hU => exact rfl
  case hv => exact rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
