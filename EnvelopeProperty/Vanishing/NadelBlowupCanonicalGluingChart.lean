import EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingIdeals
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingDescent
import EnvelopeProperty.AlgGeom.CartierCanonicalTensorPullback

/-! # Actual canonical Cartier factors on the original native blowup model charts -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingChart
open CoordinateSubspace CanonicalGeometry
open NadelBlowupCanonicalGluingIdeals

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem tensorLeftIso_inclusion {X : Scheme.{u}} {B N : X.Modules}
    (e : B ≅ N) (I : X.IdealSheafData) :
    (tensorObjCongr e (Iso.refl I.toModules)).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap N I.toModules I.toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap B I.toModules I.toModulesInclusion ≫ e.hom := by
  apply (cancel_epi (ModularCurves.monoidalTensorObjIso B I.toModules).hom).mp
  rw [← Category.assoc, ModularCurves.cartierMonoidalTensorObjIso_hom_natural]
  simp only [Iso.refl_hom, tensorHom_id, Category.assoc]
  rw [SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  rw [← Category.assoc (ModularCurves.monoidalTensorObjIso B I.toModules).hom,
    SchemeTensorObjMorphisms.tensorObjIdealMap_monoidal]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]
  exact (Category.assoc _ _ _).symm

private theorem factor_transport {k : Type u} [Field k] {X B U : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (π : B ⟶ X) (q : U ⟶ B) [IsOpenImmersion q]
    (n : ℕ) (I : U.IdealSheafData) (J : B.IdealSheafData)
    (t : (pullback q).obj (Scheme.Modules.tensorObj (canonicalLineSheaf (π ≫ f) n) J.toModules) ≅
      Scheme.Modules.tensorObj ((pullback q).obj (canonicalLineSheaf (π ≫ f) n)) I.toModules)
    (ht : t.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion =
      (pullback q).map (SchemeTensorObjMorphisms.tensorObjIdealMap _ _ J.toModulesInclusion))
    (hc : ∃ c : (pullback (q ≫ π)).obj (canonicalLineSheaf f n) ≅
        Scheme.Modules.tensorObj (canonicalLineSheaf ((q ≫ π) ≫ f) n) I.toModules,
      c.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion =
        exteriorCotangentSheafPullbackMap f (q ≫ π) n) :
    ∃ e : (pullback q).obj ((pullback π).obj (canonicalLineSheaf f n)) ≅
        (pullback q).obj (Scheme.Modules.tensorObj (canonicalLineSheaf (π ≫ f) n) J.toModules),
      e.hom ≫ (pullback q).map
          (SchemeTensorObjMorphisms.tensorObjIdealMap _ _ J.toModulesInclusion) =
        (pullback q).map (exteriorCotangentSheafPullbackMap f π n) := by
  obtain ⟨c, hc⟩ := hc
  let s := (pullbackComp q π).app (canonicalLineSheaf f n)
  let : IsIso (exteriorCotangentSheafPullbackMap (π ≫ f) q n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion (π ≫ f) q n
  let v : (pullback q).obj (canonicalLineSheaf (π ≫ f) n) ≅
      canonicalLineSheaf ((q ≫ π) ≫ f) n :=
    asIso (exteriorCotangentSheafPullbackMap (π ≫ f) q n) ≪≫
      eqToIso (congrArg (fun b => canonicalLineSheaf b n) (Category.assoc q π f).symm)
  let u := tensorObjCongr v.symm (Iso.refl I.toModules)
  have hu : u.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion ≫
      v.hom = SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion := by
    rw [← Category.assoc, tensorLeftIso_inclusion v.symm I]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hs : s.hom ≫ exteriorCotangentSheafPullbackMap f (q ≫ π) n =
      (pullback q).map (exteriorCotangentSheafPullbackMap f π n) ≫ v.hom := by
    have h := congrArg (fun a => s.hom ≫ a)
      (exteriorCotangentSheafPullbackMap_comp f π q n)
    change s.hom ≫ exteriorCotangentSheafPullbackMap f (q ≫ π) n =
      s.hom ≫ s.inv ≫ (pullback q).map (exteriorCotangentSheafPullbackMap f π n) ≫
        exteriorCotangentSheafPullbackMap (π ≫ f) q n ≫
          eqToHom (congrArg (fun b => canonicalLineSheaf b n) (Category.assoc q π f).symm) at h
    simpa only [v, Iso.trans_hom, asIso_hom, eqToIso.hom, Iso.hom_inv_id_assoc] using h
  refine ⟨s ≪≫ c ≪≫ u ≪≫ t.symm, ?_⟩
  apply (cancel_mono v.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hu]
  exact (congrArg (fun a => s.hom ≫ a) hc).trans hs

variable (k : Type u) [Field k] (n r : ℕ) (j : Fin n) (hj : j.val < r) (hrn : r ≤ n)

include hrn

/-- The actual model chart internally produces a whole canonical
isomorphism factor through the SAME original exceptional-power tensor.
All literal-coordinate, ideal and whole-differential comparisons are consumed
from proved producers; no local factorization certificate is supplied. -/
theorem exists_modelChart_factor_iso :
    let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
    let π := affineBlowUp.π (centerIdeal k n r)
    let q := modelChart k n r j hj
    let J := (affineBlowUp.exceptionalIdeal (centerIdeal k n r)) ^ (r - 1)
    ∃ e : (pullback q).obj ((pullback π).obj (canonicalLineSheaf f n)) ≅
        (pullback q).obj (Scheme.Modules.tensorObj (canonicalLineSheaf (π ≫ f) n) J.toModules),
      e.hom ≫ (pullback q).map
          (SchemeTensorObjMorphisms.tensorObjIdealMap _ _ J.toModulesInclusion) =
        (pullback q).map (exteriorCotangentSheafPullbackMap f π n) := by
  let f := affineStructuralMap k (.of (MvPolynomial (Fin n) k))
  let π := affineBlowUp.π (centerIdeal k n r)
  let q := modelChart k n r j hj
  let I := NadelBlowupCanonicalSheafChart.imageIdeal k n r j
  let J := (affineBlowUp.exceptionalIdeal (centerIdeal k n r)) ^ (r - 1)
  apply factor_transport f π q n I J
    (exceptionalTensorChartIso k n r j hj (canonicalLineSheaf (π ≫ f) n))
    (exceptionalTensorChartIso_inclusion k n r j hj (canonicalLineSheaf (π ≫ f) n))
  let Q (g : Spec (.of (MvPolynomial (Fin n) k)) ⟶ Spec (.of (MvPolynomial (Fin n) k))) :=
    ∃ c : (pullback g).obj (canonicalLineSheaf f n) ≅
        Scheme.Modules.tensorObj (canonicalLineSheaf (g ≫ f) n) I.toModules,
      c.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion =
        exteriorCotangentSheafPullbackMap f g n
  exact Eq.mpr (congrArg Q (modelChart_π k n r j hj))
    (NadelBlowupCanonicalSheafOriginal.exists_original_canonical_ideal_iso k n r j hj hrn)

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalGluingChart
