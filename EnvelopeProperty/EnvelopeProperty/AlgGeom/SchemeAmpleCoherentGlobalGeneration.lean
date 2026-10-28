import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.OriginalAmpleSerreVanishing
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # Genuine finite global generation for the SAME original ample powers

The actual positive-power embedding is unpacked internally. Existing closed
projective global generation supplies the finite residue modules; the original
whole power comparison transports their actual generators to every large power.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MvPolynomial
universe u
namespace EnvelopeProperty.SchemeAmpleCoherentGlobalGeneration
open CanonicalGeometry
attribute [local instance] MvPolynomial.gradedAlgebra Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine native ampleness internally produces actual finite generating
sections of EVERY sufficiently large original coherent twist. No ambient
integrality, Noetherian hypothesis, auxiliary twist or generator certificate
is supplied; both modules, the powers and actual free evaluation are original. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (E L : X.Modules) [E.IsQuasicoherent] [E.IsFiniteType]
    (h : SchemeLineAmpleness.IsAmple p L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (E ⊗ bundleTensorPower L m).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨hL, r, hr, n, i, hi, _hbase, ⟨η⟩⟩ := h
  let : IsClosedImmersion i := hi
  let A : Fin r → X.Modules := fun a => E ⊗ bundleTensorPower L a.val
  have hqc (a : Fin r) : (A a).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight E _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL a.val)
  have hft (a : Fin r) : (A a).IsFiniteType :=
    SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight E _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL a.val)
  have hex (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : (A a ⊗ (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (d : ℤ))).GeneratingSections,
        G.IsFiniteType := by
    let : (A a).IsQuasicoherent := hqc a
    let : (A a).IsFiniteType := hft a
    exact ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections i (A a) (0 : Fin (n + 1))
  choose N hN using hex
  let B := Finset.univ.sup N
  refine ⟨r * B, ?_⟩
  intro m hm
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  let d := m / r
  have hBd : B ≤ d := (Nat.le_div_iff_mul_le hr).mpr
    (by simpa only [Nat.mul_comm] using hm)
  have hd : N a ≤ d := (Finset.le_sup (f := N) (Finset.mem_univ a)).trans hBd
  obtain ⟨G, hG⟩ := hN a d hd
  let : G.IsFiniteType := hG
  let γ : A a ⊗ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (d : ℤ)) ≅
        E ⊗ bundleTensorPower L m :=
    (Iso.refl (A a) ⊗ᵢ
      (OriginalAmpleSerreVanishing.powerMulPullbackTwistIso i L r (0 : Fin (n + 1)) η.symm d).symm) ≪≫
      α_ E (bundleTensorPower L a.val) (bundleTensorPower L (r * d)) ≪≫
      (Iso.refl E ⊗ᵢ TensorPowerBaseIdealGrading.tensorPowerAddIso L a.val (r * d)) ≪≫
      (Iso.refl E ⊗ᵢ eqToIso (congrArg (bundleTensorPower L)
        (show a.val + r * d = m from Nat.mod_add_div m r)))
  exact ⟨G.ofEpi γ.hom, inferInstance⟩

#print axioms exists_eventual_generatingSections
end EnvelopeProperty.SchemeAmpleCoherentGlobalGeneration
