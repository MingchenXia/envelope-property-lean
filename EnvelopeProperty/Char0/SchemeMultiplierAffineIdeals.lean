/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.SmoothFunctionFieldSubalgebras
import EnvelopeProperty.Char0.MultiplierAwayLocalization
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-!
# Full intrinsic multiplier ideals of the ORIGINAL scheme affine section rings

The actual generic germ into the actual original function field supplies the
literal sources required by the full valuative construction. Every nonzero
ideal and every smoothness and fraction-field property is derived internally.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Classical
universe u
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k))

/-- A genuinely nonzero original generic stalk gives a nonzero ideal on
every original nonempty affine open. -/
theorem affineIdeal_ne_bot_of_generic_stalk_ne_bot
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (U : X.affineOpens) [Nonempty U.1] : I.ideal U ≠ ⊥ := by
  intro hzero
  apply hI
  rw [I.stalkIdeal_eq_map_germ U
    (((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U.1))), hzero, Ideal.map_bot]

/-- On every original affine open, transport the FULL original-source
multiplier ideal through the ACTUAL generic-germ range equivalence.
The empty open has its unique unit ideal. -/
def schemeMultiplierAffineIdeal
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (q : ℚ) (U : X.affineOpens) : Ideal Γ(X, U) :=
  if hU : Nonempty U.1 then by
    let _ := hU
    let _ := f.stalkAlgebra (genericPoint X)
    let _ := f.sectionsAlgebra U.1
    let C := f.sectionsFunctionFieldSubalgebra U.1
    let e := f.sectionsFunctionFieldEquiv U.1
    have : IsFractionRing C X.functionField := f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
    exact (valuativeMultiplierIdeal C ((I.ideal U).map e.toRingHom)
      ((Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
        (affineIdeal_ne_bot_of_generic_stalk_ne_bot I hI U)) q).comap e.toRingHom
  else ⊤

private theorem schemeMultiplier_ideal_equiv_square
    {R S T P : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing P]
    (e : R ≃+* S) (d : T ≃+* P) (a : R →+* T) (b : S →+* P)
    (h : ∀ r, d (a r) = b (e r)) (J : Ideal S) :
    (J.comap e.toRingHom).map a = (J.map b).comap d.toRingHom := by
  have hs : a.comp e.symm.toRingHom = d.symm.toRingHom.comp b := by
    ext x
    apply d.injective
    change d (a (e.symm x)) = d (d.symm (b x))
    rw [d.apply_symm_apply, h, e.apply_symm_apply]
  have he : J.comap e.toRingHom = J.map e.symm.toRingHom :=
    (Ideal.map_comap_of_equiv e.symm).symm
  rw [he, Ideal.map_map, hs, ← Ideal.map_map]
  exact Ideal.map_comap_of_equiv d.symm

/-- Every actual nonempty principal restriction of the original smooth scheme
preserves the ENTIRE full intrinsic multiplier ideal of its original ideal sheaf. -/
theorem map_schemeMultiplierAffineIdeal_basicOpen_nonempty [Smooth f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (q : ℚ) (U : X.affineOpens) (s : Γ(X, U))
    [Nonempty U.1] [Nonempty (X.basicOpen s)] :
    (schemeMultiplierAffineIdeal f I hI q U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      schemeMultiplierAffineIdeal f I hI q (X.affineBasicOpen s) := by
  let _ := f.stalkAlgebra (genericPoint X)
  let _ := f.sectionsAlgebra U.1
  let _ := f.sectionsAlgebra (X.basicOpen s)
  let C := f.sectionsFunctionFieldSubalgebra U.1
  let D := f.sectionsFunctionFieldSubalgebra (X.basicOpen s)
  let e := f.sectionsFunctionFieldEquiv U.1
  let d := f.sectionsFunctionFieldEquiv (X.basicOpen s)
  let hCD := f.sectionsFunctionFieldSubalgebra_le (X.basicOpen_le s)
  let _ : Algebra C D := (Subalgebra.inclusion hCD).toAlgebra
  have : IsFractionRing C X.functionField := f.sectionsFunctionFieldSubalgebra_isFractionRing U.1 U.2
  have : IsFractionRing D X.functionField :=
    f.sectionsFunctionFieldSubalgebra_isFractionRing (X.basicOpen s) (U.2.basicOpen s)
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    f.smooth_sectionsFunctionFieldSubalgebra U.1 U.2
  have hlocal : IsLocalization.Away (e s) D :=
    f.sectionsFunctionFieldSubalgebra_isLocalization_basicOpen U.1 U.2 s
  let a := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  let b := (Subalgebra.inclusion hCD).toRingHom
  have hsq (r : Γ(X, U)) : d (a r) = b (e r) :=
    (f.sectionsFunctionFieldEquiv_restriction (X.basicOpen_le s) r).symm
  have hcomp : b.comp e.toRingHom = d.toRingHom.comp a := by
    apply RingHom.ext
    intro r
    exact (hsq r).symm
  have hIeq : ((I.ideal U).map e.toRingHom).map b =
      (I.ideal (X.affineBasicOpen s)).map d.toRingHom := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
    exact congrArg (fun J : Ideal Γ(X, X.basicOpen s) => J.map d.toRingHom)
      (I.map_ideal_basicOpen U s)
  have hIC : (I.ideal U).map e.toRingHom ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
      (affineIdeal_ne_bot_of_generic_stalk_ne_bot I hI U)
  have hJ := map_valuativeMultiplierIdeal_source_away C D hCD (e s) hlocal
    ((I.ideal U).map e.toRingHom) hIC q
  dsimp only [b] at hIeq
  simp only [hIeq] at hJ
  simp only [schemeMultiplierAffineIdeal, Scheme.affineBasicOpen_coe,
    dif_pos (inferInstance : Nonempty U.1), dif_pos (inferInstance : Nonempty (X.basicOpen s))]
  rw [schemeMultiplier_ideal_equiv_square e.toRingEquiv d.toRingEquiv a b hsq, hJ]
  rfl

/-- The actual affine multiplier ideals satisfy the COMPLETE original
ideal-sheaf basic-open restriction axiom, including empty opens. -/
theorem map_schemeMultiplierAffineIdeal_basicOpen [Smooth f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (q : ℚ) (U : X.affineOpens) (s : Γ(X, U)) :
    (schemeMultiplierAffineIdeal f I hI q U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      schemeMultiplierAffineIdeal f I hI q (X.affineBasicOpen s) := by
  by_cases hD : Nonempty (X.basicOpen s)
  · let _ := hD
    have : Nonempty U.1 := hD.map (fun x => ⟨x.val, X.basicOpen_le s x.property⟩)
    exact map_schemeMultiplierAffineIdeal_basicOpen_nonempty f I hI q U s
  · have hDbot : X.basicOpen s = ⊥ :=
      (Opens.not_nonempty_iff_eq_bot _).mp (by simpa using hD)
    have : Subsingleton Γ(X, X.basicOpen s) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hDbot)
    exact Subsingleton.elim _ _

end EnvelopeProperty.Char0
