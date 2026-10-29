import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorFiniteType
/-! # Actual eventual global generation for every original finite-type quasicoherent twist -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelAmpleCoherentGeneration
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- ANY SAME original finite-type quasicoherent twist of an original geometrically ample
line has finite genuine global generators at EVERY sufficiently large actual exponent. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (B : X.Modules) [B.IsQuasicoherent] [B.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (bundleTensorPower A m ⊗ B).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨r, hr, n, i, hi, _hip, ⟨e⟩⟩ := hA.2
  let : IsClosedImmersion i := hi
  have hh (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : ((B ⊗ bundleTensorPower A a.val) ⊗ (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (d : ℤ))).GeneratingSections,
        G.IsFiniteType := by
    let M := B ⊗ bundleTensorPower A a.val
    let L := bundleTensorPower A a.val
    let hL := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible a.val
    let : M.IsQuasicoherent := SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight B L hL
    let : M.IsFiniteType := SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight B L hL
    exact @ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections R _ (Fin (n + 1)) _ X
      i hi M inferInstance inferInstance (0 : Fin (n + 1))
  choose N hN using hh
  let T := Finset.univ.sup N
  refine ⟨T * r, fun m hm => ?_⟩
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  have hd : T ≤ m / r := (Nat.le_div_iff_mul_le hr).mpr hm
  obtain ⟨G, hG⟩ := hN a (m / r) ((Finset.le_sup (f := N) (Finset.mem_univ a)).trans hd)
  let : G.IsFiniteType := hG
  let E : ((B ⊗ bundleTensorPower A a.val) ⊗ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) ((m / r : ℕ) : ℤ))) ≅
      bundleTensorPower A m ⊗ B :=
    (Iso.refl (B ⊗ bundleTensorPower A a.val) ⊗ᵢ
      (PositivePowerProjectiveGeneration.blockTwistIso i A r (0 : Fin (n + 1)) e (m / r)).symm) ≪≫
      (α_ B (bundleTensorPower A a.val) (bundleTensorPower A (r * (m / r)))) ≪≫
      (Iso.refl B ⊗ᵢ
        (TensorPowerBaseIdealGrading.tensorPowerAddIso A a.val (r * (m / r)) ≪≫
          eqToIso (congrArg (bundleTensorPower A) (Nat.mod_add_div m r)))) ≪≫
      (β_ B (bundleTensorPower A m))
  let hE : Epi E.hom :=
    @CategoryTheory.IsIso.epi_of_iso X.Modules _ _ _ E.hom E.isIso_hom
  let H := @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ G E.hom hE
  exact ⟨H, ⟨hG.finite⟩⟩


end EnvelopeProperty.Vanishing.NadelAmpleCoherentGeneration
