import EnvelopeProperty.Vanishing.RelativeArithmeticSmoothAmpleModel
import EnvelopeProperty.Vanishing.RelativeCanonicalSpecializationWitt

/-! # Kodaira vanishing for the original relative ample line in characteristic zero

The original finite-type affine base is arbitrary.  Its separate arithmetic
model, the actual original line, the genuine free Witt point, and all
cohomology/canonical comparisons are supplied by proved constructions.
There is no properness over the original field, domain hypothesis on the
original relative base, or externally supplied vanishing certificate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u

namespace EnvelopeProperty.Vanishing.RelativeKodairaCharacteristicZero
open Cartier CanonicalGeometry ArithmeticCanonicalGlobalComparison
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem subsingleton_H_of_moduleIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (j : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H M.sheaf j)) :
    Subsingleton (CategoryTheory.Sheaf.H N.sheaf j) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) j).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  let : Subsingleton ((CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology X) j).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := h
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩

/-- Positive Kodaira vanishing on the same original smooth separated total
space and same original relatively ample line over the arbitrary finite-type
affine base, in the actual sheafified tensor object. -/
theorem kodaira_tensorObj
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (g : X ⟶ Spec (.of R))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple g L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf f n) L).sheaf (q + 1)) := by
  obtain ⟨A, hSmoothA, hFTA, B, hB, hAB, hFPB, _, Y, a, p, gB, M,
      H, hn, hsep, hqc, hgp, hAmp, ⟨eM⟩⟩ :=
    RelativeArithmeticSmoothAmpleModel.exists_original_smooth_ample_model f g hg n L hL
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Algebra.FinitePresentation A B := hFPB
  let : Algebra.FiniteType ℤ A := hFTA
  let : Algebra.Smooth ℤ A := hSmoothA
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : SmoothOfRelativeDimension n p := hn
  let : IsSeparated p := hsep
  let : QuasiCompact p := hqc
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hNative := RelativeCanonicalSpecializationWitt.nativeCanonicalTensor_subsingleton
    p gB hgp hAmp.isProjectiveFactorization n M hAmp.isInvertible q
    (by
      intro P ell hp hnell hc hf
      let : Fact ell.Prime := hp
      let : Field (A ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
      let : CharP (A ⧸ P.asIdeal) ell := hc
      let : Finite (A ⧸ P.asIdeal) := hf
      intro lifted hred
      have hclosed := RelativeArithmeticWittComparison.kodaira_on_residue_fibre
        ell p (Ideal.Quotient.mk P.asIdeal) lifted hred gB hgp n hnell M hAmp q
      exact subsingleton_H_of_moduleIso (ModularCurves.monoidalTensorObjIso _ _)
        (q + 1) hclosed)
    k Subtype.val_injective
  have hModel := subsingleton_H_of_moduleIso (fieldCanonicalTensorIso p n k M).symm
    (q + 1) hNative
  have hOriginal := (RelativeCanonicalSpecialization.squareCanonicalTensor_subsingleton_H_iff
    p (CommRingCat.ofHom (algebraMap A k)) a f H g hL.isProjectiveFactorization
    n M hAmp.isInvertible q).mpr hModel
  exact subsingleton_H_of_moduleIso
    ((ModularCurves.monoidalTensorObjIso _ _).symm ≪≫
      (Iso.refl _ ⊗ᵢ eM) ≪≫ ModularCurves.monoidalTensorObjIso _ _)
    (q + 1) hOriginal

/-- Relative Kodaira for the original absolute canonical module and original
relatively ample line.  Disconnected smooth total spaces and arbitrary
finite-type affine bases are included. -/
theorem kodaira
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (g : X ⟶ Spec (.of R))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple g L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf f n ⊗ L : X.Modules).sheaf (q + 1)) :=
  subsingleton_H_of_moduleIso (ModularCurves.monoidalTensorObjIso _ _).symm (q + 1)
    (kodaira_tensorObj f g hg n L hL q)

end EnvelopeProperty.Vanishing.RelativeKodairaCharacteristicZero
