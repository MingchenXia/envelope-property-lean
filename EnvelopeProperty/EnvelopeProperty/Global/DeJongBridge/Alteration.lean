import EnvelopeProperty.Global.DeJongBridge.QuotientScheme
import DeJongAlterations.Geometry.RegularSmoothConverse
import DeJongAlterations.Geometry.FiniteBirationalNormalGenericBaseChange

/-!
# Smooth projective alterations from de Jong's Theorem 4.1

Step 2 of the bridge (plan PLAN-DJ-MAIN §6.2). Let `X` be a variety over a perfect field `k`
which is proper over `k`. De Jong's Theorem 4.1 (`dejong96-alterations:page-0017`, in Codex's
form `DeJongAlterations.DeJongAlterationTheorem k`) applied with `Z = ∅` gives an alteration
`φ : X₁ → X` and an open immersion `j₁ : X₁ → X̄₁` into a regular projective variety. As `X` is
proper, `X₁` is proper over `k`, so `j₁` is proper and its image is closed and open in the
irreducible `X̄₁`: `j₁` is an isomorphism (`isIso_inclusion`). Hence `Y = X₁` is projective over
`k`, and smooth over `k` by de Jong 2.10 / Remark 4.2 (Codex's
`RegularSmoothConverse.smooth_of_isRegularScheme`, `k` perfect): this is
`nonempty_smoothProjectiveAlteration`.

`finiteDimensional_functionField`: for an alteration `f : X → S` of integral schemes, `k(X)` is
finite over `k(S)` (de Jong 2.20: `f` is finite over a nonempty open of `S`; Codex's
`FiniteBirationalNormal.finite_functionField` for finite dominant morphisms).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open DeJongAlterations

namespace DeJongEPBridge

universe u

variable {k : Type u} [Field k]

/-- A smooth projective alteration of a `k`-scheme `X` (with structure morphism `p`): a smooth
variety `Y` over `k`, an alteration `φ : Y → X` over `k`, and a closed immersion `Y → ℙ^{N'}`
over `k`. -/
structure SmoothProjectiveAlteration {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) where
  /-- The source `Y`. -/
  Y : Scheme.{u}
  /-- The structure morphism of `Y`. -/
  pY : Y ⟶ Spec (.of k)
  /-- The alteration `φ : Y → X`. -/
  φ : Y ⟶ X
  /-- The dimension of the ambient projective space of `Y`. -/
  N' : ℕ
  /-- The closed immersion `Y → ℙ^{N'}`. -/
  emb : Y ⟶ projectiveSpace k N'
  variety : IsVariety pY
  smooth : Smooth pY
  alteration : IsAlteration φ
  φ_comp : φ ≫ p = pY
  closedImmersion : IsClosedImmersion emb
  emb_comp : emb ≫ projectiveSpaceStructure k N' = pY

/-- In the output of 4.1 for a proper variety and `Z = ∅`, the open immersion into the
compactification is an isomorphism. -/
theorem isIso_inclusion {X : Scheme.{u}} {p : X ⟶ Spec (.of k)} [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) : IsIso d.inclusion := by
  have : IsVariety d.sourceStructure := d.sourceVariety
  have : IsVariety d.compactificationStructure := d.compactificationVariety
  have : IsAlteration d.alteration := d.isAlteration
  have : IsOpenImmersion d.inclusion := d.isOpenImmersion
  have : IsProper d.sourceStructure := by
    rw [← d.alterationOver]
    infer_instance
  have : IsProper (d.inclusion ≫ d.compactificationStructure) := by
    rw [d.inclusionOver]
    infer_instance
  have : IsProper d.inclusion := IsProper.of_comp _ d.compactificationStructure
  have hclopen : IsClopen (Set.range d.inclusion) :=
    ⟨d.inclusion.isClosedMap.isClosed_range, d.inclusion.isOpenEmbedding.isOpen_range⟩
  have : PreconnectedSpace d.compactification :=
    ⟨(IrreducibleSpace.isIrreducible_univ _).isPreirreducible.isPreconnected⟩
  have huniv := hclopen.eq_univ ⟨_, ⟨Classical.arbitrary d.source, rfl⟩⟩
  exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext huniv)

/-- **de Jong 4.1 with `Z = ∅` for a proper variety over a perfect field**: a smooth projective
alteration. -/
theorem nonempty_smoothProjectiveAlteration [PerfectField k] (h : DeJongAlterationTheorem k)
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety p] [IsProper p] :
    Nonempty (SmoothProjectiveAlteration p) := by
  have hne : (⊥ : TopologicalSpace.Closeds X) ≠ ⊤ := by
    intro hbot
    have hx : Classical.arbitrary X ∈ (⊤ : TopologicalSpace.Closeds X) := trivial
    rw [← hbot] at hx
    exact hx
  obtain ⟨d⟩ := h X p inferInstance ⊥ hne
  have : IsIso d.inclusion := isIso_inclusion d
  have : IsVariety d.sourceStructure := d.sourceVariety
  obtain ⟨n, i, hi, hcomp⟩ := d.projective
  refine ⟨{
    Y := d.source
    pY := d.sourceStructure
    φ := d.alteration
    N' := n
    emb := d.inclusion ≫ i
    variety := d.sourceVariety
    smooth := ?_
    alteration := d.isAlteration
    φ_comp := d.alterationOver
    closedImmersion := ?_
    emb_comp := ?_ }⟩
  · have : IsOpenImmersion d.inclusion := d.isOpenImmersion
    exact Geometry.RegularSmoothConverse.smooth_of_isRegularScheme _
      (d.regular.of_isOpenImmersion d.inclusion)
  · have := hi
    infer_instance
  · rw [Category.assoc, hcomp, d.inclusionOver]

/-- **The function field of an alteration is finite.** -/
theorem finiteDimensional_functionField {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [hf : IsAlteration f] :
    letI := Geometry.FiniteBirationalNormal.functionFieldAlgebra f
    FiniteDimensional S.functionField X.functionField := by
  obtain ⟨U, hU, hfin⟩ := hf.genericallyFinite
  have hV : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨⟨s, hs⟩⟩ := hU
    obtain ⟨x, rfl⟩ := f.surjective s
    exact ⟨⟨x, hs⟩⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  have : IsIntegral (f ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have : Surjective f := ⟨f.surjective⟩
  have : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense (by
    obtain ⟨⟨s, hs⟩⟩ := hU
    exact ⟨s, hs⟩))
  have : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι ((f ⁻¹ᵁ U).isOpen.dense (by
    obtain ⟨⟨s, hs⟩⟩ := hV
    exact ⟨s, hs⟩))
  have hfinU := Geometry.FiniteBirationalNormal.finite_functionField (f ∣_ U)
  have : IsIso (Geometry.NormalizationInExtension.functionFieldMap U.ι) :=
    Geometry.NormalizationInExtension.functionFieldMap_isIso U.ι
  have : IsIso (Geometry.NormalizationInExtension.functionFieldMap (f ⁻¹ᵁ U).ι) :=
    Geometry.NormalizationInExtension.functionFieldMap_isIso (f ⁻¹ᵁ U).ι
  let eU := asIso (Geometry.NormalizationInExtension.functionFieldMap U.ι)
  let eV := asIso (Geometry.NormalizationInExtension.functionFieldMap (f ⁻¹ᵁ U).ι)
  have hsq : eU.hom ≫ Geometry.NormalizationInExtension.functionFieldMap (f ∣_ U) =
      Geometry.NormalizationInExtension.functionFieldMap f ≫ eV.hom := by
    simp only [eU, eV, asIso_hom]
    rw [← Geometry.NormalizationInExtension.functionFieldMap_comp,
      ← Geometry.NormalizationInExtension.functionFieldMap_comp]
    congr 1
    exact morphismRestrict_ι f U
  have hsq' : eU.inv ≫ Geometry.NormalizationInExtension.functionFieldMap f =
      Geometry.NormalizationInExtension.functionFieldMap (f ∣_ U) ≫ eV.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let := Geometry.FiniteBirationalNormal.functionFieldAlgebra f
  let := Geometry.FiniteBirationalNormal.functionFieldAlgebra (f ∣_ U)
  refine Module.Finite.of_equiv_equiv eU.symm.commRingCatIsoToRingEquiv
    eV.symm.commRingCatIsoToRingEquiv ?_
  ext x
  exact congrArg (fun φ => φ.hom x) hsq'

end DeJongEPBridge
