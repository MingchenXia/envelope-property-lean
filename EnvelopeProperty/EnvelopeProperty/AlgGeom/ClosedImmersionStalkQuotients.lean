import EnvelopeProperty.AlgGeom.SchemeOrderLocalLength
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Localization.Algebra

/-! # Actual closed-immersion stalk quotients and original native orders -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
noncomputable section
universe u
namespace EnvelopeProperty.ClosedImmersionStalkQuotients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem ker_localization_square
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] (q : Ideal S) [q.IsPrime]
    (f : R →+* S) (hf : Function.Surjective f)
    [IsLocalization (q.comap f).primeCompl A] [IsLocalization q.primeCompl B]
    (h : A →+* B) (hs : h.comp (algebraMap R A) = (algebraMap S B).comp f) :
    RingHom.ker h = (RingHom.ker f).map (algebraMap R A) := by
  have hT := Ideal.map_primeCompl_comap_of_surjective f hf q
  let h' : A →+* B := IsLocalization.map B f (hT.symm ▸ Submonoid.le_comap_map _)
  have hh : h = h' := by
    apply IsLocalization.ringHom_ext (q.comap f).primeCompl
    exact hs.trans (by ext r; simp [h'])
  rw [hh]
  exact IsLocalization.ker_map B f hT

variable {X D : Scheme.{u}} (g : D ⟶ X) [IsClosedImmersion g]

/-- The kernel of the SAME actual stalk map is the localization of the
SAME original affine kernel ideal through the actual original germ. -/
theorem stalkMap_ker_eq_map (U : X.Opens) (hU : IsAffineOpen U)
    (y : D) (hy : g y ∈ U) :
    RingHom.ker (g.stalkMap y).hom =
      (g.ker.ideal ⟨U, hU⟩).map (X.presheaf.germ U (g y) hy).hom := by
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  let := X.presheaf.algebra_section_stalk ⟨g y, hy⟩
  let := D.presheaf.algebra_section_stalk (⟨y, hy⟩ : g ⁻¹ᵁ U)
  have hsource := hU.isLocalization_stalk ⟨g y, hy⟩
  have htarget := hV.isLocalization_stalk ⟨y, hy⟩
  have hp : (hV.primeIdealOf ⟨y, hy⟩).comap (g.app U).hom =
      hU.primeIdealOf ⟨g y, hy⟩ := by
    have hp := IsAffineOpen.comap_primeIdealOf_appLE U hU (g ⁻¹ᵁ U) hV le_rfl hy
    have happ : g.appLE U (g ⁻¹ᵁ U) le_rfl = g.app U := by
      dsimp [Scheme.Hom.appLE]
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    simpa only [happ] using hp
  have hpc : ((hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap (g.app U).hom).primeCompl =
      (hU.primeIdealOf ⟨g y, hy⟩).asIdeal.primeCompl :=
    congrArg (fun p : PrimeSpectrum Γ(X, U) => p.asIdeal.primeCompl) hp
  have : IsLocalization
      ((hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap (g.app U).hom).primeCompl
      (X.presheaf.stalk (g y)) := hpc.symm ▸ hsource
  rw [g.ker_apply]
  exact ker_localization_square (hV.primeIdealOf ⟨y, hy⟩).asIdeal
    (g.app U).hom (g.app_surjective U hU) (g.stalkMap y).hom
    (by ext r; exact g.germ_stalkMap_apply U y hy r)

/-- A true original affine principal kernel gives the actual principal
quotient of the ambient stalk, identified with the SAME closed-scheme stalk. -/
def principalStalkQuotientEquiv (U : X.Opens) (hU : IsAffineOpen U)
    (c : Γ(X, U)) (hc : g.ker.ideal ⟨U, hU⟩ = Ideal.span {c})
    (y : D) (hy : g y ∈ U) :
    (X.presheaf.stalk (g y)) ⧸ Ideal.span {X.presheaf.germ U (g y) hy c} ≃+*
      D.presheaf.stalk y := by
  have hk : RingHom.ker (g.stalkMap y).hom =
      Ideal.span {X.presheaf.germ U (g y) hy c} := by
    rw [stalkMap_ker_eq_map g U hU y hy, hc, Ideal.map_span]
    simp
  exact (Ideal.quotEquivOfEq hk.symm).trans
    ((g.stalkMap y).hom.quotientKerEquivOfSurjective (g.stalkMap_surjective y))

/-- The whole quotient identification retains the literal original stalk map on every element. -/
@[simp] theorem principalStalkQuotientEquiv_mk (U : X.Opens) (hU : IsAffineOpen U)
    (c : Γ(X, U)) (hc : g.ker.ideal ⟨U, hU⟩ = Ideal.span {c})
    (y : D) (hy : g y ∈ U) (a : X.presheaf.stalk (g y)) :
    principalStalkQuotientEquiv g U hU c hc y hy (Ideal.Quotient.mk _ a) =
      g.stalkMap y a := by
  simp [principalStalkQuotientEquiv]

private theorem quotientKer_length {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Module.length R (R ⧸ RingHom.ker f) = Module.length S S := by
  let : Algebra R S := f.toAlgebra
  let e : (R ⧸ RingHom.ker f) ≃ₐ[R] S :=
    { f.quotientKerEquivOfSurjective hf with
      commutes' := fun r => f.quotientKerEquivOfSurjective_apply_mk hf r }
  exact e.toLinearEquiv.length_eq.trans (Module.length_eq_of_surjective hf)

/-- The true ambient principal quotient length equals the length of the
SAME original closed-scheme stalk over itself. -/
theorem principalStalkQuotient_length (U : X.Opens) (hU : IsAffineOpen U)
    (c : Γ(X, U)) (hc : g.ker.ideal ⟨U, hU⟩ = Ideal.span {c})
    (y : D) (hy : g y ∈ U) :
    Module.length (X.presheaf.stalk (g y))
      ((X.presheaf.stalk (g y)) ⧸ Ideal.span {X.presheaf.germ U (g y) hy c}) =
      Module.length (D.presheaf.stalk y) (D.presheaf.stalk y) := by
  have hk : RingHom.ker (g.stalkMap y).hom =
      Ideal.span {X.presheaf.germ U (g y) hy c} := by
    rw [stalkMap_ker_eq_map g U hU y hy, hc, Ideal.map_span]
    simp
  rw [← hk]
  exact quotientKer_length (g.stalkMap y).hom (g.stalkMap_surjective y)

/-- The native ORIGINAL ambient order is the actual local length of the
SAME original closed subscheme cut out by the original local equation. -/
theorem ord_eq_closedStalk_length [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (c : Γ(X, U)) (hc : c ≠ 0)
    (hker : g.ker.ideal ⟨U, hU⟩ = Ideal.span {c})
    (y : D) (hy : g y ∈ U) (hcodim : coheight (g y) = 1) :
    X.ord (X.germToFunctionField U c) (g y) =
      ((Module.length (D.presheaf.stalk y) (D.presheaf.stalk y)).toNat : ℤ) := by
  rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length (g y) hcodim U hy c hc,
    principalStalkQuotient_length g U hU c hker y hy]

/-- The ACTUAL original residue-field map of any closed immersion is an isomorphism. -/
theorem residueFieldMap_isIso (y : D) : IsIso (g.residueFieldMap y) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(g.residueFieldMap y).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨c, rfl⟩ := g.stalkMap_surjective y b
  exact ⟨IsLocalRing.residue _ c, rfl⟩

end EnvelopeProperty.ClosedImmersionStalkQuotients
