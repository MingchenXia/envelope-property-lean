import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationFiniteCoefficientGluing
import ModularCurves.ForMathlib.FiniteAffineOpenCover

/-! # Literal whole Laurent reconstruction by actual finite descent

The genuine original Cartesian square, native original sheaves and actual
affine covers derive whole base-change bijectivity and unique finite Laurent
expansion. No whole H0 comparison or decomposition is an input.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Scheme.Modules

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of R[T;T⁻¹])) (g : Y ⟶ X)
  (H : IsPullback g q f (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))))
  (M : X.Modules)

include H

/-- The actual original scalar-extension natural transformation gives this
literal original section restriction identity on EVERY original tensor. -/
theorem originalBaseOpenChangeMap_restrict {U V : X.Opens} (hUV : U ≤ V)
    (z : (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).obj
      ((originalBaseOpenPresheaf f M).obj (op V))) :
    originalBaseOpenChangeMap f q g H.w M U
        ((ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map
          ((originalBaseOpenPresheaf f M).map (homOfLE hUV).op) z) =
      (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
        (homOfLE (g.preimage_mono hUV)).op
        (originalBaseOpenChangeMap f q g H.w M V z) :=
  ConcreteCategory.congr_hom
    ((originalBaseOpenChange f q g H.w M).naturality (homOfLE hUV).op) z

section FiniteCover
variable [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))
  (hUU : ∀ i j, IsAffineOpen (U i ⊓ U j)) (hCover : TopologicalSpace.IsOpenCover U)

include hU hCover

/-- Actual original affine injectivity, coefficient naturality and native
original sheaf separation DERIVE whole top-component injectivity. -/
theorem originalBaseOpenChangeMap_top_injective_of_affine_cover :
    Function.Injective (originalBaseOpenChangeMap f q g H.w M ⊤) := by
  let : Module.Free R R[T;T⁻¹] := Module.Free.of_basis (AddMonoidAlgebra.basis ℤ R)
  intro z w h
  apply (originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op ⊤))).injective
  ext n
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ U ⊤
    (fun _ => homOfLE le_top) (le_of_eq hCover.iSup_eq_top.symm)
  intro i
  let a := (originalBaseOpenPresheaf f M).map (homOfLE (le_top : U i ≤ ⊤)).op
  have hl : (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map a z =
      (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map a w := by
    apply (originalBaseOpenChangeMap_bijective_of_affine f q g H M (U i) (hU i)).1
    rw [originalBaseOpenChangeMap_restrict f q g H M,
      originalBaseOpenChangeMap_restrict f q g H M, h]
  have hc := congrArg
    (originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op (U i)))) hl
  rw [originalLaurentDomainCoefficients_map, originalLaurentDomainCoefficients_map] at hc
  exact congrArg (fun c => c n) hc

include hUU

/-- The produced finite ORIGINAL whole coefficients and actual inverse-image
cover separation DERIVE whole top-component surjectivity. -/
theorem originalBaseOpenChangeMap_top_surjective_of_finite_affine_cover [Fintype ι] :
    Function.Surjective (originalBaseOpenChangeMap f q g H.w M ⊤) := by
  intro s
  obtain ⟨C, hC, _⟩ := exists_unique_original_whole_laurent_finite_coefficients
    f q g H M U hU hUU hCover s
  refine ⟨(originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op ⊤))).symm C, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨((Scheme.Modules.pullback g).obj M).presheaf,
    ((Scheme.Modules.pullback g).obj M).isSheaf⟩ (fun i => g ⁻¹ᵁ U i) ⊤
    (fun _ => homOfLE le_top) (le_of_eq (g.iSup_preimage_eq_top hCover.iSup_eq_top).symm)
  intro i
  let a := (originalBaseOpenPresheaf f M).map (homOfLE (le_top : U i ≤ ⊤)).op
  have hn := originalBaseOpenChangeMap_restrict f q g H M (le_top : U i ≤ ⊤)
    ((originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op ⊤))).symm C)
  rw [originalLaurentDomainCoefficients_symm_map] at hn
  have hci : C.mapRange a.hom a.hom.map_zero =
      originalAffineOpenLaurentCoefficients f q g H M (U i) (hU i)
        ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
          (homOfLE (le_top : g ⁻¹ᵁ U i ≤ ⊤)).op s) := by
    ext n
    exact hC i n
  change originalBaseOpenChangeMap f q g H.w M (U i)
      ((originalLaurentDomainCoefficients _).symm (C.mapRange a.hom a.hom.map_zero)) = _ at hn
  rw [hci, originalAffineOpenLaurentCoefficients_map] at hn
  exact hn.symm

/-- The ACTUAL original top diagram transfers the derived top bijection
to the SAME frozen whole scalar-adjunction map, without a supplied comparison. -/
theorem originalBaseChangeMap_bijective_of_finite_affine_cover [Fintype ι] :
    Function.Bijective (originalBaseChangeMap f q g H.w M) := by
  have hb : Function.Bijective (originalBaseOpenChangeMap f q g H.w M ⊤) :=
    ⟨originalBaseOpenChangeMap_top_injective_of_affine_cover f q g H M U hU hCover,
      originalBaseOpenChangeMap_top_surjective_of_finite_affine_cover f q g H M U hU hUU hCover⟩
  let eD := (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).mapIso
    (originalBaseOpenTopIso f M)
  let eT := originalBaseOpenTopIso q ((Scheme.Modules.pullback g).obj M)
  have hmap : (fun z => eT.hom (originalBaseOpenChangeMap f q g H.w M ⊤ z)) =
      (fun z => originalBaseChangeMap f q g H.w M (eD.hom z)) := by
    funext z
    exact ConcreteCategory.congr_hom (originalBaseOpenChangeMap_top f q g H.w M) z
  have hcomp : Function.Bijective (fun z => originalBaseChangeMap f q g H.w M (eD.hom z)) := by
    rw [← hmap]
    exact (ConcreteCategory.bijective_of_isIso eT.hom).comp hb
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := (ConcreteCategory.bijective_of_isIso eD.hom).2 a
    obtain ⟨b', rfl⟩ := (ConcreteCategory.bijective_of_isIso eD.hom).2 b
    exact congrArg (fun z => eD.hom z) (hcomp.1 hab)
  · intro s
    obtain ⟨z, hz⟩ := hcomp.2 s
    exact ⟨eD.hom z, hz⟩

/-- EVERY original whole section has UNIQUE finite ORIGINAL whole Laurent
coefficients, by the genuine whole-map bijection and literal reconstruction. -/
theorem exists_unique_original_whole_laurent_expansion_of_finite_affine_cover [Fintype ι]
    (s : originalBaseSections q ((Scheme.Modules.pullback g).obj M)) :
    ∃! c : ℤ →₀ originalBaseSections f M,
      c.sum (fun n m => (LaurentPolynomial.T n : R[T;T⁻¹]) •
        (show originalBaseSections q ((Scheme.Modules.pullback g).obj M) from
          affinePullbackUnitTop g M m)) = s := by
  have hb := originalBaseChangeMap_bijective_of_finite_affine_cover f q g H M U hU hUU hCover
  obtain ⟨z, hz⟩ := hb.2 s
  let V := originalBaseSections f M
  refine ⟨originalLaurentDomainCoefficients V z, ?_, ?_⟩
  · have hc := originalBaseChangeMap_laurent_reconstruction f q g H.w M
      (originalLaurentDomainCoefficients V z)
    rw [(originalLaurentDomainCoefficients _).symm_apply_apply] at hc
    exact hc.symm.trans hz
  · intro c hc
    apply (originalLaurentDomainCoefficients V).symm.injective
    apply hb.1
    rw [(originalLaurentDomainCoefficients _).symm_apply_apply,
      originalBaseChangeMap_laurent_reconstruction f q g H.w M]
    exact hc.trans hz.symm

end FiniteCover

/-- Native compactness and the original separated diagonal PRODUCE the
actual finite affine cover/intersections, so no cover is an input. -/
theorem originalBaseChangeMap_bijective_of_compact_separated [M.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] :
    Function.Bijective (originalBaseChangeMap f q g H.w M) := by
  obtain ⟨ι, hι, U, hCover, hU⟩ := X.exists_finite_affine_openCover
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  exact originalBaseChangeMap_bijective_of_finite_affine_cover f q g H M U hU
    (fun i j => (hU i).inf (hU j)) hCover

/-- Actual properness over the SAME original affine base derives the
native compact/separated hypotheses and the SAME original whole H0 bijection. -/
theorem originalBaseChangeMap_bijective_of_isProper [M.IsQuasicoherent] [IsProper f] :
    Function.Bijective (originalBaseChangeMap f q g H.w M) := by
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  exact originalBaseChangeMap_bijective_of_compact_separated f q g H M

/-- Actual properness DERIVES the finite original whole Laurent expansion
for EVERY original whole pulled-back section, without a cover/decomposition input. -/
theorem exists_unique_original_whole_laurent_expansion_of_isProper
    [M.IsQuasicoherent] [IsProper f]
    (s : originalBaseSections q ((Scheme.Modules.pullback g).obj M)) :
    ∃! c : ℤ →₀ originalBaseSections f M,
      c.sum (fun n m => (LaurentPolynomial.T n : R[T;T⁻¹]) •
        (show originalBaseSections q ((Scheme.Modules.pullback g).obj M) from
          affinePullbackUnitTop g M m)) = s := by
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨ι, hι, U, hCover, hU⟩ := X.exists_finite_affine_openCover
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  exact exists_unique_original_whole_laurent_expansion_of_finite_affine_cover
    f q g H M U hU (fun i j => (hU i).inf (hU j)) hCover s

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
