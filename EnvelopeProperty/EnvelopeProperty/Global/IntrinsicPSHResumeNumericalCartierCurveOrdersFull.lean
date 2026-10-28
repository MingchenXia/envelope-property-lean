import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalCartierCurveOrders

/-! # The native original spectrum coefficients for Cartier fibre projection

Actual spectrum stalk and residue isomorphisms preserve the original scalar
action and principal equation. No order/residue matching data is supplied.
Whole original Cartier fibre projection is the subsequent assembly target.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.NumericalCartierCurveOrders
open CurveCartierLocalOrders

/-- The actual native spectrum residue isomorphism preserves the SAME original k action. -/
def specResidueAlgEquiv {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (x : PrimeSpectrum A) :
    let s : Spec (CommRingCat.of A) := x
    letI := AffineSchemeLocalDegrees.residueAlgebra
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) s
    (Spec (CommRingCat.of A)).residueField s ≃ₐ[k]
      IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal) := by
  let s : Spec (CommRingCat.of A) := x
  let q := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let := AffineSchemeLocalDegrees.residueAlgebra q s
  let e := (Scheme.Spec.residueFieldIso (CommRingCat.of A) s).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro c
  apply e.symm.injective
  change e.symm (e (algebraMap k ((Spec (CommRingCat.of A)).residueField s) c)) = _
  rw [e.symm_apply_apply]
  change (Spec (CommRingCat.of A)).Γevaluation s
      (q.appTop (SchemeCoherentEulerIndex.baseScalar c)) =
    (Scheme.Spec.residueFieldIso (CommRingCat.of A) s).inv
      (algebraMap k (IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal)) c)
  have hs : q.appTop (SchemeCoherentEulerIndex.baseScalar c) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
    exact (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))) c).symm
  rw [hs]
  change (Spec (CommRingCat.of A)).Γevaluation s
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c)) =
    (Scheme.Spec.residueFieldIso (CommRingCat.of A) s).inv
      (algebraMap A (IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal)) (algebraMap k A c))
  exact (ConcreteCategory.congr_hom
    (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of A) s) (algebraMap k A c)).symm

/-- An actual original principal Cartier equation has its SAME native local spectrum weight. -/
theorem weightedLocalOrder_principal_spec {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    (x : PrimeSpectrum A) (hx : x ≠ ⊥) (a : A) (ha : a ≠ 0)
    (I : (Spec (CommRingCat.of A)).IdealSheafData) (hI : I.IsInvertible)
    (hgen : I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv a}) :
    let s : Spec (CommRingCat.of A) := x
    weightedLocalOrder (Spec.map (CommRingCat.ofHom (algebraMap k A))) I hI s =
      ((Ring.ord (Localization.AtPrime x.asIdeal)
          (algebraMap A (Localization.AtPrime x.asIdeal) a)).toNat : ℤ) *
        (Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal)) : ℤ) := by
  let C := Spec (CommRingCat.of A)
  let s : C := x
  let q := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let c : Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv a
  let : Nonempty (⊤ : C.Opens) := ⟨⟨s, trivial⟩⟩
  let := AffineSchemeLocalDegrees.residueAlgebra q s
  have hc : c ≠ 0 := by
    simpa only [map_zero] using
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).injective.ne ha
  have hdim : topologicalKrullDim C ≤ 1 := by
    change topologicalKrullDim (PrimeSpectrum A) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
  have hngx : s ≠ genericPoint C := by
    intro hs
    exact hx (hs.trans (genericPoint_eq_bot_of_affine (R := CommRingCat.of A)))
  have hcx := CurveFiniteClosedSubschemes.coheight_eq_one
    (X := C) hdim s hngx
  have hg : (Spec.stalkIso (CommRingCat.of A) s).hom (C.presheaf.germ ⊤ s trivial c) =
      algebraMap A (Localization.AtPrime x.asIdeal) a := by
    have hh : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ C.presheaf.germ ⊤ s trivial ≫
        (Spec.stalkIso (CommRingCat.of A) s).hom =
        CommRingCat.ofHom (algebraMap A (Localization.AtPrime x.asIdeal)) := by
      rw [Spec.germ_stalkMapIso_hom, Iso.inv_hom_id_assoc]
    have hha := ConcreteCategory.congr_hom hh a
    simpa only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom, c] using hha
  have ho := SemilinearPrincipalLengths.ord_ringEquiv
    (Spec.stalkIso (CommRingCat.of A) s).commRingCatIsoToRingEquiv
    (C.presheaf.germ ⊤ s trivial c)
  change Ring.ord (C.presheaf.stalk s) (C.presheaf.germ ⊤ s trivial c) =
    Ring.ord (Localization.AtPrime x.asIdeal)
      ((Spec.stalkIso (CommRingCat.of A) s).hom (C.presheaf.germ ⊤ s trivial c)) at ho
  rw [hg] at ho
  have hr := (specResidueAlgEquiv (k := k) x).toLinearEquiv.finrank_eq
  change weightedLocalOrder q I hI s = _
  unfold weightedLocalOrder
  rw [localOrder_eq_ord_of_local_equation I hI ⟨⊤, isAffineOpen_top C⟩ c hc hgen s trivial,
    SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length s hcx ⊤ trivial c hc]
  change ((Ring.ord (C.presheaf.stalk s) (C.presheaf.germ ⊤ s trivial c)).toNat : ℤ) *
      (Module.finrank k (C.residueField s) : ℤ) = _
  rw [ho, hr]

end EnvelopeProperty.NumericalCartierCurveOrders
