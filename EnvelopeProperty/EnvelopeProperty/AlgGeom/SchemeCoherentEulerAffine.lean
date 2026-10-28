import EnvelopeProperty.AlgGeom.SchemeCoherentEulerCharacteristic
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward

/-! # Genuine affine and pushforward formulas for original coherent Euler characteristics -/
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules TopCat TopCat.Sheaf
noncomputable section
universe u
namespace EnvelopeProperty.SchemeCoherentEulerAffine
open SchemeCoherentEulerIndex SchemeCoherentEulerExact SchemeCoherentEulerCharacteristic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Actual pushforward retains the WHOLE original field-linear Cech homology,
with the SAME literal original composite structure morphism. -/
def fieldCechPushforwardIso (g : X ⟶ Y) (f : Y ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (n : ℕ) :
    fieldCech (g ≫ f) M (fun i => g ⁻¹ᵁ U i) n ≅
      fieldCech f ((pushforward g).obj M) U n :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).mapIso
    (baseCechOrderedHomologyIso (g ≫ f) M (fun i => g ⁻¹ᵁ U i) n ≪≫
      HomologicalComplex.homologyMapIso (orderedBaseCechComplexPushforwardIso g f M U) n ≪≫
      (baseCechOrderedHomologyIso f ((pushforward g).obj M) U n).symm)

/-- Genuine actual affine cohomology makes the intrinsic Euler characteristic
EXACTLY the original field dimension of SAME original global sections. -/
theorem eulerCharacteristic_eq_finrank_sections [IsAffine X]
    (f : X ⟶ Spec (.of k)) (M : X.Modules) [M.IsQuasicoherent] :
    eulerCharacteristic f M = (Module.finrank k (fieldSections f M) : ℤ) := by
  let U : ULift.{u} PUnit → X.Opens := fun _ => ⊤
  have hU : IsOpenCover U := by simp [U, IsOpenCover]
  have hUa : ∀ i, IsAffineOpen (U i) := fun _ => isAffineOpen_top X
  have hcard : Nat.card (ULift.{u} PUnit) = 1 := by simp
  have hz : Module.finrank k (fieldCech f M U 1) = 0 := by
    let : Subsingleton (fieldCech f M U 1) :=
      ModuleCat.subsingleton_of_isZero (fieldCech_isZero_of_card_le f M U 1 (by rw [hcard]))
    exact Module.finrank_zero_of_subsingleton
  rw [eulerCharacteristic_eq_on_cover f M U hU hUa, hcard]
  unfold coverEuler
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    pow_one, hz, Nat.cast_zero, mul_zero, add_zero]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (fieldSectionsCechZeroIso f M U hU).toLinearEquiv.finrank_eq.symm

/-- The actual coherent Euler characteristic commutes with the genuine
original affine pushforward, preserving the literal original coefficient map. -/
theorem eulerCharacteristic_pushforward [CompactSpace X] [CompactSpace Y]
    [X.IsSeparated] [Y.IsSeparated] (g : X ⟶ Y) [IsAffineHom g]
    (f : Y ⟶ Spec (.of k)) (M : X.Modules) [M.IsQuasicoherent] :
    eulerCharacteristic (g ≫ f) M = eulerCharacteristic f ((pushforward g).obj M) := by
  let : ((pushforward g).obj M).IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom g
  let U := finiteAffineOpens Y
  let : Fintype (finiteAffineCover Y).I₀ := Fintype.ofFinite _
  let : LinearOrder (finiteAffineCover Y).I₀ :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have hU := finiteAffineOpens_cover Y
  have hUa := finiteAffineOpens_isAffine Y
  let V := fun i => g ⁻¹ᵁ U i
  have hV : IsOpenCover V := g.iSup_preimage_eq_top hU
  have hVa : ∀ i, IsAffineOpen (V i) := fun i => (hUa i).preimage g
  rw [eulerCharacteristic_eq_on_cover (g ≫ f) M V hV hVa,
    eulerCharacteristic_eq_on_cover f ((pushforward g).obj M) U hU hUa]
  unfold coverEuler
  apply Finset.sum_congr rfl
  intro n _
  rw [(fieldCechPushforwardIso g f M U n).toLinearEquiv.finrank_eq]

end EnvelopeProperty.SchemeCoherentEulerAffine
