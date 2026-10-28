import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationCartesianAffine
import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationCoefficientNaturality

/-! # Derived overlap matching of actual original Laurent coefficients

The actual Cartesian affine-open theorem produces the coefficients. The
proved original open map and coefficient naturality derive their restrictions
and matching from original sections, without a decomposition or matching input.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  (q : Y ⟶ Spec (CommRingCat.of R[T;T⁻¹])) (g : Y ⟶ X)
  (H : IsPullback g q f (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))))
  (M : X.Modules) [M.IsQuasicoherent]

/-- The actual affine-open theorem produces this finite family from the
SAME original section. No Laurent decomposition is an input. -/
def originalAffineOpenLaurentCoefficients (U : X.Opens) (hU : IsAffineOpen U)
    (s : (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj
      (op (g ⁻¹ᵁ U))) : ℤ →₀ (originalBaseOpenPresheaf f M).obj (op U) :=
  Classical.choose
    (exists_unique_original_affine_open_laurent_expansion f q g H M U hU s).exists

/-- The produced coefficients reconstruct exactly the original section
by the literal monomials and original pullback-unit sections. -/
theorem originalAffineOpenLaurentCoefficients_reconstruction (U : X.Opens)
    (hU : IsAffineOpen U)
    (s : (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj
      (op (g ⁻¹ᵁ U))) :
    (originalAffineOpenLaurentCoefficients f q g H M U hU s).sum
      (fun n m => (LaurentPolynomial.T n : R[T;T⁻¹]) •
        (show (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj
            (op (g ⁻¹ᵁ U)) from pullbackOpenRestrictMap g M U m)) = s :=
  Classical.choose_spec
    (exists_unique_original_affine_open_laurent_expansion f q g H M U hU s).exists

/-- The actual original map sends the inverse coefficient tensor of the
produced family to the SAME original section. -/
theorem originalAffineOpenLaurentCoefficients_map (U : X.Opens)
    (hU : IsAffineOpen U)
    (s : (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj
      (op (g ⁻¹ᵁ U))) :
    originalBaseOpenChangeMap f q g H.w M U
        ((originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op U))).symm
          (originalAffineOpenLaurentCoefficients f q g H M U hU s)) = s := by
  rw [originalBaseOpenChangeMap_laurent_reconstruction]
  exact originalAffineOpenLaurentCoefficients_reconstruction f q g H M U hU s

/-- Actual affine-open coefficients commute with the literal ORIGINAL
section restriction, derived from original map naturality and injectivity. -/
theorem originalAffineOpenLaurentCoefficients_restrict {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
    (s : (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj
      (op (g ⁻¹ᵁ V))) :
    originalAffineOpenLaurentCoefficients f q g H M U hU
        ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
          (homOfLE (g.preimage_mono hUV)).op s) =
      (originalAffineOpenLaurentCoefficients f q g H M V hV s).mapRange
        (fun m => (show (originalBaseOpenPresheaf f M).obj (op U) from
          M.presheaf.map (homOfLE hUV).op m))
        (by exact (M.presheaf.map (homOfLE hUV).op).hom.map_zero) := by
  let a := (originalBaseOpenPresheaf f M).map (homOfLE hUV).op
  let c := originalAffineOpenLaurentCoefficients f q g H M V hV s
  let z := (originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op V))).symm c
  have hn := ConcreteCategory.congr_hom
    ((originalBaseOpenChange f q g H.w M).naturality (homOfLE hUV).op) z
  change originalBaseOpenChangeMap f q g H.w M U
      ((ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map a z) =
    (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
      (homOfLE (g.preimage_mono hUV)).op
      (originalBaseOpenChangeMap f q g H.w M V z) at hn
  change originalBaseOpenChangeMap f q g H.w M U
      ((ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map a
        ((originalLaurentDomainCoefficients _).symm c)) = _ at hn
  rw [originalLaurentDomainCoefficients_symm_map] at hn
  change originalBaseOpenChangeMap f q g H.w M U
      ((originalLaurentDomainCoefficients _).symm (c.mapRange a.hom a.hom.map_zero)) =
    (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
      (homOfLE (g.preimage_mono hUV)).op
      (originalBaseOpenChangeMap f q g H.w M V
        ((originalLaurentDomainCoefficients _).symm
          (originalAffineOpenLaurentCoefficients f q g H M V hV s))) at hn
  rw [originalAffineOpenLaurentCoefficients_map] at hn
  let : Module.Free R R[T;T⁻¹] := Module.Free.of_basis (AddMonoidAlgebra.basis ℤ R)
  apply (originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op U))).symm.injective
  apply (originalBaseOpenChangeMap_bijective_of_affine f q g H M U hU).1
  rw [originalAffineOpenLaurentCoefficients_map]
  exact hn.symm

private theorem originalBaseOpenPresheaf_restrict_top {A : Type u} [CommRing A]
    {Z : Scheme.{u}} (b : Z ⟶ Spec (CommRingCat.of A)) (N : Z.Modules)
    {U V : Z.Opens} (hUV : U ≤ V)
    (s : (originalBaseOpenPresheaf b N).obj (op ⊤)) :
    (originalBaseOpenPresheaf b N).map (homOfLE hUV).op
        ((originalBaseOpenPresheaf b N).map (homOfLE (le_top : V ≤ ⊤)).op s) =
      (originalBaseOpenPresheaf b N).map (homOfLE (le_top : U ≤ ⊤)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Coefficients derived from an original whole section genuinely match
on every actual affine intersection, with the SAME original restrictions. -/
theorem originalAffineOpenLaurentCoefficients_match_global
    (s : (originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).obj (op ⊤))
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (n : ℤ) :
    M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
        ((originalAffineOpenLaurentCoefficients f q g H M U hU
          ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
            (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op s)) n) =
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
        ((originalAffineOpenLaurentCoefficients f q g H M V hV
          ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
            (homOfLE (le_top : g ⁻¹ᵁ V ≤ ⊤)).op s)) n) := by
  have hu := originalAffineOpenLaurentCoefficients_restrict f q g H M hUV hU
    (inf_le_left : U ⊓ V ≤ U)
    ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
      (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op s)
  have hv := originalAffineOpenLaurentCoefficients_restrict f q g H M hUV hV
    (inf_le_right : U ⊓ V ≤ V)
    ((originalBaseOpenPresheaf q ((Scheme.Modules.pullback g).obj M)).map
      (homOfLE (le_top : g ⁻¹ᵁ V ≤ ⊤)).op s)
  rw [originalBaseOpenPresheaf_restrict_top] at hu hv
  exact congrArg (fun c => c n) (hu.symm.trans hv)

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
