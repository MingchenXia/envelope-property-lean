import SGPT.Okounkov.SchemeNativeStalkFlatness
import Hironaka.Algebra.Local.CompletionEtale

/-!
# Completions of the same original algebraic and native holomorphic stalks

The actual centered algebraic generators and original Hadamard decomposition
give equality of the whole maximal ideals. Original scalar germs supply the
residue-field surjection. Together with the previously proved actual flatness,
the existing flat-local completion theorem applies to the original stalk map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeStalkCompletion

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter
open TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open SGPT.Okounkov HironakaHolomorphicJetMonomialSpan
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance completionAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The original stalk map expressed in the actual preferred centered model. -/
def modelStalkGerm :
    X.presheaf.stalk (schemeComplexPointImage f p) →+* HolGerm (ComplexModel n) :=
  (schemeCoordinateModelGermEquiv n).toRingHom.comp (schemeCoordinateStalkRegularGerm f n p)

instance modelStalkGerm_isLocalHom : IsLocalHom (modelStalkGerm f n p) := by
  let e := schemeCoordinateModelGermEquiv n
  let : IsLocalHom e.toRingHom := by
    refine ⟨fun a ha => ?_⟩
    have h := ha.map e.symm.toRingHom
    change IsUnit (e.symm (e a)) at h
    rwa [RingEquiv.symm_apply_apply] at h
  exact RingHom.isLocalHom_comp e.toRingHom (schemeCoordinateStalkRegularGerm f n p)

/-- Actual original centered algebraic elements give every literal model coordinate. -/
theorem modelStalkGerm_centered (i : Fin n) :
    modelStalkGerm f n p (schemeCoordinateStalkEquiv f n p
      (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p)
        (schemeCoordinateCenteredFreeGenerator f n p i))) = coordinateGerm i := by
  change schemeCoordinateModelGermEquiv n (schemeCoordinateStalkRegularGerm f n p _) = _
  rw [schemeCoordinateStalkRegularGerm_regular, schemeCoordinateCenteredFreeGenerator_germ,
    schemeCoordinateModelGermEquiv_coordinate]
  rfl

/-- Every literal complex constant is the germ of its original algebraic scalar. -/
theorem modelStalkGerm_scalar (c : ℂ) :
    modelStalkGerm f n p (schemeCoordinateStalkEquiv f n p
      (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p)
        (algebraMap ℂ (SchemeCoordinateAffineRing f n p) c))) = HolGerm.constHom c := by
  change schemeCoordinateModelGermEquiv n (schemeCoordinateStalkRegularGerm f n p _) = _
  rw [schemeCoordinateStalkRegularGerm_regular, schemeCoordinateRegularGerm_scalar,
    schemeCoordinateModelGermEquiv_const]

/-- The WHOLE original maximal ideal generates the whole actual analytic maximal ideal. -/
theorem modelStalkGerm_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (schemeComplexPointImage f p))).map
        (modelStalkGerm f n p) = IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le _)
  have hi (i : Fin n) : coordinateGerm i ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (schemeComplexPointImage f p))).map
        (modelStalkGerm f n p) := by
    rw [← modelStalkGerm_centered f n p i]
    apply Ideal.mem_map_of_mem
    rw [← IsLocalRing.maximalIdeal_comap (modelStalkGerm f n p)]
    change modelStalkGerm f n p _ ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))
    rw [modelStalkGerm_centered, HolGerm.mem_maximalIdeal_iff]
    rfl
  intro g hg
  obtain ⟨h, he⟩ := exists_coordinate_decomposition g
  rw [(HolGerm.mem_maximalIdeal_iff g).mp hg, map_zero, zero_add] at he
  rw [he]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hi i)

/-- The actual original scalar action makes the induced residue-field map bijective. -/
theorem modelStalkGerm_residue_bijective :
    Function.Bijective (IsLocalRing.ResidueField.map (modelStalkGerm f n p)) := by
  refine ⟨(IsLocalRing.ResidueField.map (modelStalkGerm f n p)).injective, ?_⟩
  intro y
  obtain ⟨g, rfl⟩ := IsLocalRing.residue_surjective y
  let a := schemeCoordinateStalkEquiv f n p
    (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p)
      (algebraMap ℂ (SchemeCoordinateAffineRing f n p) (HolGerm.eval g)))
  refine ⟨IsLocalRing.residue _ a, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  apply Ideal.Quotient.eq.mpr
  rw [HolGerm.mem_maximalIdeal_iff, map_sub]
  change HolGerm.eval (modelStalkGerm f n p a) - HolGerm.eval g = 0
  rw [show modelStalkGerm f n p a = HolGerm.constHom (HolGerm.eval g) from
    modelStalkGerm_scalar f n p _]
  exact sub_self _

section Native

variable [IsSeparated f] [QuasiCompact f]

local instance completionPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance completionPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance completionPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The comparison uses the SAME original native map and actual preferred chart. -/
theorem nativeStalkGerm_eq_model :
    schemeNativeStalkGerm f n p = (NativeHolGerm.chartEquiv p).symm.toRingHom.comp
      (modelStalkGerm f n p) := rfl

/-- The whole original maximal ideal generates the whole original native maximal ideal. -/
theorem nativeStalkGerm_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (schemeComplexPointImage f p))).map
        (schemeNativeStalkGerm f n p) =
      IsLocalRing.maximalIdeal (NativeHolGerm n (SchemeComplexPoint f) p) := by
  rw [nativeStalkGerm_eq_model, ← Ideal.map_map, modelStalkGerm_map_maximalIdeal]
  exact IsLocalRing.map_ringEquiv_maximalIdeal (NativeHolGerm.chartEquiv p).symm

/-- No residue extension is hidden in passage to the actual native analytic stalk. -/
theorem nativeStalkGerm_residue_bijective :
    Function.Bijective (IsLocalRing.ResidueField.map (schemeNativeStalkGerm f n p)) := by
  let e := (NativeHolGerm.chartEquiv (n := n) p).symm
  let : IsLocalHom e.toRingHom := by
    refine ⟨fun a ha => ?_⟩
    have h := ha.map e.symm.toRingHom
    change IsUnit (e.symm (e a)) at h
    rwa [RingEquiv.symm_apply_apply] at h
  change Function.Bijective (IsLocalRing.ResidueField.map
    (e.toRingHom.comp (modelStalkGerm f n p)))
  rw [IsLocalRing.ResidueField.map_comp]
  exact (IsLocalRing.ResidueField.mapEquiv e).bijective.comp
    (modelStalkGerm_residue_bijective f n p)

/-- The canonical map on completions of the actual ORIGINAL stalks is an isomorphism. -/
def nativeCompletionEquiv :
    AdicCompletion
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (schemeComplexPointImage f p)))
        (X.presheaf.stalk (schemeComplexPointImage f p)) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (NativeHolGerm n (SchemeComplexPoint f) p))
        (NativeHolGerm n (SchemeComplexPoint f) p) :=
  RingEquiv.ofBijective (IsLocalRing.completionMap (schemeNativeStalkGerm f n p))
    (IsLocalRing.bijective_completionMap_of_flat_of_map_maximalIdeal
      (schemeNativeStalkGerm f n p) (schemeNativeStalkGerm_flat f n p)
      (nativeStalkGerm_map_maximalIdeal f n p) (nativeStalkGerm_residue_bijective f n p))

/-- Every original coefficient has its literal image in the completed native stalk. -/
theorem nativeCompletionEquiv_algebraMap
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    nativeCompletionEquiv f n p (algebraMap _ _ a) =
      algebraMap _ _ (schemeNativeStalkGerm f n p a) :=
  IsLocalRing.completionMap_algebraMap (schemeNativeStalkGerm f n p) a

/-- The original completion comparison carries the WHOLE extension of every original ideal. -/
theorem nativeCompletionEquiv_map_ideal
    (I : Ideal (X.presheaf.stalk (schemeComplexPointImage f p))) :
    (I.map (algebraMap _
      (AdicCompletion (IsLocalRing.maximalIdeal
        (X.presheaf.stalk (schemeComplexPointImage f p)))
          (X.presheaf.stalk (schemeComplexPointImage f p))))).map
            (nativeCompletionEquiv f n p).toRingHom =
      (I.map (schemeNativeStalkGerm f n p)).map (algebraMap _
        (AdicCompletion (IsLocalRing.maximalIdeal (NativeHolGerm n (SchemeComplexPoint f) p))
          (NativeHolGerm n (SchemeComplexPoint f) p))) :=
  IsLocalRing.map_completionMap_map (schemeNativeStalkGerm f n p) I

end Native

end EnvelopeProperty.Char0.NativeStalkCompletion
