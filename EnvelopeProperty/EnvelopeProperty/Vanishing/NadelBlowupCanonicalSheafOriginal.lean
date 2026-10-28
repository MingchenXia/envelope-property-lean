import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafChart
import EnvelopeProperty.AlgGeom.Canonical.ExteriorPullbackComposition

/-! # Restore the original polynomial source and actual coordinate chart differential -/

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafOriginal
open CoordinateSubspace affineBlowUpAlgebra CanonicalGeometry
open NadelBlowupCanonicalSheafCoordinates NadelBlowupCanonicalSheafChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorIdeal_transport {X : Scheme.{u}} {M N : X.Modules} (h : M = N)
    (I : X.IdealSheafData) :
    (eqToIso (congrArg (fun L => tensorObj L I.toModules) h)).hom ≫
        SchemeTensorObjMorphisms.tensorObjIdealMap N I.toModules I.toModulesInclusion =
      SchemeTensorObjMorphisms.tensorObjIdealMap M I.toModules I.toModulesInclusion ≫ eqToHom h := by
  subst N
  simp only [eqToIso_refl, Iso.refl_hom, eqToHom_refl, Category.id_comp, Category.comp_id]

variable (k : Type u) [Field k] (n r : ℕ) (j : Fin n)

theorem sourceBase_original :
    (sourceSpectrumIso k n).hom ≫ affineStructuralMap k (targetRing k n) = sourceBase k n := by
  change Spec.map (CommRingCat.ofHom (sourceAlgebraEquiv k n).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (ULift.{0} (MvPolynomial (Fin n) k))))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  rfl

/-- On the LITERAL ORIGINAL polynomial chart, the actual native canonical
line comparison and its ENTIRE actual differential are produced internally.
The temporary source copy has been removed through its actual native
open-immersion differential, whole composition law and original scheme triangle. -/
theorem exists_original_canonical_ideal_iso (hj : j.val < r) (hrn : r ≤ n) :
    let f := affineStructuralMap k (targetRing k n)
    let g := Spec.map (CommRingCat.ofHom (chartSubst k (center n r) j).toRingHom)
    ∃ e : (pullback g).obj (canonicalLineSheaf f n) ≅
        tensorObj (canonicalLineSheaf (g ≫ f) n) (imageIdeal k n r j).toModules,
      e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _
          (imageIdeal k n r j).toModulesInclusion = exteriorCotangentSheafPullbackMap f g n := by
  let f := affineStructuralMap k (targetRing k n)
  let g := chartMap k n r j
  let s := sourceSpectrumIso k n
  let I := imageIdeal k n r j
  let Q (b : Spec (sourceRing k n) ⟶ Spec (.of k)) : Prop :=
    ∃ e : (pullback g).obj (canonicalLineSheaf b n) ≅
        tensorObj (canonicalLineSheaf (g ≫ b) n) I.toModules,
      e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion =
        exteriorCotangentSheafPullbackMap b g n
  have hcopy : Q (s.hom ≫ f) := Eq.mpr (congrArg Q (sourceBase_original k n))
    (exists_canonical_ideal_iso k n r j hj hrn)
  obtain ⟨c, hc⟩ := hcopy
  let : IsIso (exteriorCotangentSheafPullbackMap f s.hom n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f s.hom n
  let p : (pullback (g ≫ s.hom)).obj (canonicalLineSheaf f n) ≅
      (pullback g).obj (canonicalLineSheaf (s.hom ≫ f) n) :=
    (pullbackComp g s.hom).symm.app (canonicalLineSheaf f n) ≪≫
      (pullback g).mapIso (asIso (exteriorCotangentSheafPullbackMap f s.hom n))
  let hN := congrArg (fun b => canonicalLineSheaf b n) (Category.assoc g s.hom f).symm
  let t := eqToIso (congrArg (fun N => tensorObj N I.toModules) hN)
  have hwhole :
      ∃ e : (pullback (g ≫ s.hom)).obj (canonicalLineSheaf f n) ≅
          tensorObj (canonicalLineSheaf ((g ≫ s.hom) ≫ f) n) I.toModules,
        e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion =
          exteriorCotangentSheafPullbackMap f (g ≫ s.hom) n := by
    refine ⟨p ≪≫ c ≪≫ t, ?_⟩
    simp only [Iso.trans_hom, Category.assoc]
    rw [tensorIdeal_transport hN I]
    rw [← Category.assoc c.hom, hc]
    exact (exteriorCotangentSheafPullbackMap_comp f s.hom g n).symm
  have hmap : g ≫ s.hom =
      Spec.map (CommRingCat.ofHom (chartSubst k (center n r) j).toRingHom) :=
    chartAlgebraMap_original k n r j
  exact Eq.mp (congrArg (fun a =>
    ∃ e : (pullback a).obj (canonicalLineSheaf f n) ≅
        tensorObj (canonicalLineSheaf (a ≫ f) n) I.toModules,
      e.hom ≫ SchemeTensorObjMorphisms.tensorObjIdealMap _ _ I.toModulesInclusion =
        exteriorCotangentSheafPullbackMap f a n) hmap) hwhole

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalSheafOriginal
