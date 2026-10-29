import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration

/-! # Genuine eventual generation of ALL powers from original positive-power projective data -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.PositivePowerProjectiveGeneration
open Scheme.Modules CanonicalGeometry

@[instance_reducible] private noncomputable def originalSchemeMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
attribute [local instance] originalSchemeMonoidal MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

/-- The original first twist is the SAME original hyperplane pole line. -/
def twistOneIso (j : σ) :
    coordinateHyperplaneTwist (R := R) j (1 : ℤ) ≅ coordinateHyperplanePoleSheaf (R := R) j :=
  λ_ (coordinateHyperplanePoleSheaf (R := R) j)

/-- ALL actual original first-twist powers give the SAME original projective twists. -/
def twistPowerIso (j : σ) : (d : ℕ) →
    bundleTensorPower (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) d ≅
      coordinateHyperplaneTwist (R := R) j (d : ℤ)
  | 0 => (ModularCurves.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).symm
  | d + 1 =>
    (ModularCurves.monoidalTensorObjIso
      (bundleTensorPower (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) d)
      (coordinateHyperplaneTwist (R := R) j (1 : ℤ))).symm ≪≫
      (twistPowerIso j d ⊗ᵢ twistOneIso j)

/-- Original positive-power geometric data DERIVE the whole original exponent-block comparison. -/
def blockTwistIso {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule σ R))
    (L : X.Modules) (r : ℕ) (j : σ)
    (e : (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) ≅
      bundleTensorPower L r) (d : ℕ) :
    bundleTensorPower L (r * d) ≅
      (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j (d : ℤ)) :=
  (BundleTensorPowerPullback.powerMulIso L r d).symm ≪≫
    BundleTensorPowerPullback.powerIso e.symm d ≪≫
      (BundleTensorPowerPullback.pullbackIso i
        (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) d).symm ≪≫
          (Scheme.Modules.pullback i).mapIso (twistPowerIso j d)

/-- Genuine original positive-power closed-projective data give finite global
generation of EVERY sufficiently large original power, not just divisible powers. -/
theorem exists_eventual_generatingSections {X : Scheme.{u}}
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ) (hr : 0 < r) (j : σ)
    (e : (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) ≅
      bundleTensorPower L r) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (bundleTensorPower L m).GeneratingSections, G.IsFiniteType := by
  classical
  have hh (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : (bundleTensorPower L a.val ⊗ (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) j (d : ℤ))).GeneratingSections, G.IsFiniteType := by
    let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL a.val
    let : (bundleTensorPower L a.val).IsQuasicoherent := hA.isQuasicoherent
    let : (bundleTensorPower L a.val).IsFinitePresentation := hA.isFinitePresentation
    let : (bundleTensorPower L a.val).IsFiniteType :=
      @SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _ _ _ _ _ _
        (bundleTensorPower L a.val) hA.isFinitePresentation
    exact ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections i (bundleTensorPower L a.val) j
  choose N hN using hh
  let T := Finset.univ.sup N
  refine ⟨T * r, ?_⟩
  intro m hm
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  have hd : T ≤ m / r := (Nat.le_div_iff_mul_le hr).mpr hm
  obtain ⟨G, hG⟩ := hN a (m / r) ((Finset.le_sup (f := N) (Finset.mem_univ a)).trans hd)
  let : G.IsFiniteType := hG
  let E : bundleTensorPower L a.val ⊗ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) j ((m / r : ℕ) : ℤ)) ≅ bundleTensorPower L m :=
    (Iso.refl (bundleTensorPower L a.val) ⊗ᵢ (blockTwistIso i L r j e (m / r)).symm) ≪≫
      TensorPowerBaseIdealGrading.tensorPowerAddIso L a.val (r * (m / r)) ≪≫
        eqToIso (congrArg (bundleTensorPower L) (Nat.mod_add_div m r))
  let : IsIso E.hom := E.isIso_hom
  let hE : Epi E.hom :=
    @CategoryTheory.IsIso.epi_of_iso X.Modules _ _ _ E.hom E.isIso_hom
  let H := @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ G E.hom hE
  exact ⟨H, ⟨hG.finite⟩⟩

end EnvelopeProperty.PositivePowerProjectiveGeneration
