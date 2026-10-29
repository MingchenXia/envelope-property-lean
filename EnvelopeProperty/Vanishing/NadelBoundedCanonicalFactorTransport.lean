import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareTensor
import EnvelopeProperty.AlgGeom.SchemeTensorIdealPullback

/-! # Transport an actual map factor through the same tensor-ideal inclusion

The factor is a morphism, not an isomorphism. This is a bounded composition
of existing tensor-inclusion naturality, for the actual canonical-chart
consumer. It supplies no original ramification bound or new gluing theorem.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalFactorTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME actual local factor and SAME compatible source/target isos
produce a factor of the SAME original pulled map. No invertibility of the
factor or geometric ideal is assumed. The original application must produce
its actual local factor and compatible comparisons independently. -/
theorem pullback_factor_of_compatible {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (J : X.IdealSheafData)
    {C B : X.Modules} {A N : Y.Modules} (D : C ⟶ B) (P : A ⟶ N)
    (eA : (pullback j).obj C ≅ A) (eB : (pullback j).obj B ≅ N)
    (hs : (pullback j).map D ≫ eB.hom = eA.hom ≫ P)
    (θ : A ⟶ Scheme.Modules.tensorObj N (J.comap j).toModules)
    (hθ : θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap N
      (J.comap j).toModules (J.comap j).toModulesInclusion = P) :
    ∃ θ' : (pullback j).obj C ⟶
        (pullback j).obj (Scheme.Modules.tensorObj B J.toModules),
      θ' ≫ (pullback j).map
        (SchemeTensorObjMorphisms.tensorObjIdealMap B J.toModules J.toModulesInclusion) =
        (pullback j).map D := by
  let E := SchemeTensorIdealPullback.idealTensorOpenPullbackIso j B J
  let H := tensorObjCongr eB.symm (Iso.refl (J.comap j).toModules)
  let inc := SchemeTensorObjMorphisms.tensorObjIdealMap B J.toModules J.toModulesInclusion
  let incF := SchemeTensorObjMorphisms.tensorObjIdealMap ((pullback j).obj B)
    (J.comap j).toModules (J.comap j).toModulesInclusion
  let incN := SchemeTensorObjMorphisms.tensorObjIdealMap N
    (J.comap j).toModules (J.comap j).toModulesInclusion
  have hE : E.inv ≫ (pullback j).map inc = incF := by
    have h := SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion j B J
    calc
      _ = E.inv ≫ (E.hom ≫ incF) := congrArg (fun q => E.inv ≫ q) h.symm
      _ = incF := E.inv_hom_id_assoc _
  have hH : H.hom ≫ incF = incN ≫ eB.inv :=
    NadelBlowupCanonicalSquareTensor.tensorLeftIso_inclusion eB.symm (J.comap j)
  refine ⟨eA.hom ≫ θ ≫ H.hom ≫ E.inv, ?_⟩
  calc
    (eA.hom ≫ θ ≫ H.hom ≫ E.inv) ≫ (pullback j).map inc =
        eA.hom ≫ θ ≫ H.hom ≫ incF := by
      simp only [Category.assoc, hE]
    _ = eA.hom ≫ θ ≫ incN ≫ eB.inv := by rw [hH]
    _ = (eA.hom ≫ P) ≫ eB.inv := by
      rw [← Category.assoc θ, hθ]
      exact (Category.assoc _ _ _).symm
    _ = (pullback j).map D := by
      have h := congrArg (fun q => q ≫ eB.inv) hs
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalFactorTransport
