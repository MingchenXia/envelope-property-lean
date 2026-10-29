import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalCurveFieldDegree
import EnvelopeProperty.AlgGeom.CurveCartierLocalOrders
import EnvelopeProperty.AlgGeom.SchemeStalkMapLocalOrders
import EnvelopeProperty.AlgGeom.NormalizationCartierModulePullback
import EnvelopeProperty.AlgGeom.FiniteFibrePrincipalOrders
import EnvelopeProperty.AlgGeom.ClosedImmersionResidueDegrees

/-! # The actual original Cartier order under genuine geometric transport

Open restriction internally preserves the native local Cartier order and
the original residue-field coefficient weight, through the actual stalk map.
The whole nonflat finite-fibre projection is the subsequent assembly target.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors
universe u
namespace EnvelopeProperty.NumericalCartierCurveOrders
open CurveCartierLocalOrders

/-- Actual open restriction preserves the original weighted Cartier order, without matching data. -/
theorem weightedLocalOrder_comap_open {k : Type u} [Field k]
    {X V : Scheme.{u}} [IsIntegral X] [IsIntegral V]
    [IsLocallyNoetherian X] [IsLocallyNoetherian V]
    (a : V ⟶ X) [IsOpenImmersion a] (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (hI : I.IsInvertible) (v : V) :
    weightedLocalOrder p I hI (a v) =
      weightedLocalOrder (a ≫ p) (I.comap a) (hI.comap_of_flat a) v := by
  let J := I.comap a
  let hJ : J.IsInvertible := hI.comap_of_flat a
  let U := equationChart I hI (a v)
  let c := equation I hI (a v)
  have hav : a v ∈ U.1 := mem_equationChart I hI (a v)
  let : Nonempty U.1 := ⟨⟨a v, hav⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hc : c ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (equation_mem_nonZeroDivisors I hI (a v))
  obtain ⟨W, hW, hv, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show v ∈ a ⁻¹ᵁ U.1 from hav)
  let Z : V.affineOpens := ⟨W, hW⟩
  let : Nonempty Z.1 := ⟨⟨v, hv⟩⟩
  let : IsDomain Γ(V, Z.1) := IsIntegral.component_integral Z.1
  let d : Γ(V, Z.1) := a.appLE U.1 Z.1 hWU c
  have hgen : J.ideal Z = Ideal.span {d} := by
    rw [Scheme.IdealSheafData.comap_ideal_of_affine_opens I a Z U hWU,
      equation_span I hI (a v), Ideal.map_span, Set.image_singleton]
  have hd : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp
    (hJ.generator_mem_nonZeroDivisors Z d hgen)
  have hlocal : localOrder I hI (a v) = localOrder J hJ v := by
    rw [localOrder_eq_ord_of_local_equation I hI U c hc (equation_span I hI (a v)) (a v) hav,
      localOrder_eq_ord_of_local_equation J hJ Z d hd hgen v hv]
    by_cases hx : Order.coheight (a v) = 1
    · have hy : Order.coheight v = 1 := by
        simpa only [coheight_eq_of_isOpenImmersion a] using hx
      rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length (a v) hx U.1 hav c hc,
        SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length v hy Z.1 hv d hd]
      change ((Ring.ord (X.presheaf.stalk (a v))
          (X.presheaf.germ U.1 (a v) hav c)).toNat : ℤ) =
        ((Ring.ord (V.presheaf.stalk v) (V.presheaf.germ Z.1 v hv d)).toNat : ℤ)
      have hg : V.presheaf.germ Z.1 v hv d =
          a.stalkMap v (X.presheaf.germ U.1 (a v) hav c) :=
        a.germ_appLE_apply U.1 Z.1 hWU hv hav c
      rw [hg, SchemeStalkMapLocalOrders.ord_stalkMap a v]
    · have hy : Order.coheight v ≠ 1 := by
        simpa only [coheight_eq_of_isOpenImmersion a] using hx
      rw [X.ord_eq_zero_of_coheight_neq_one hx,
        V.ord_eq_zero_of_coheight_neq_one hy]
  unfold weightedLocalOrder
  rw [hlocal, SchemeStalkMapLocalOrders.residue_finrank_eq a v p]

/-- The original whole affine coefficient algebra has the SAME canonical field degree. -/
theorem degree_eq_sectionsRank {A : Type u} [CommRing A] [IsDomain A]
    {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of A)) [IsFinite f] [IsDominant f] :
    NumericalCurveFieldDegree.degree f =
      letI := FlatGlobalSections.sectionsAlgebra f
      Module.finrank A Γ(Y, ⊤) := by
  let := FlatGlobalSections.sectionsAlgebra f
  let U : (Spec (CommRingCat.of A)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩
  let : Nonempty U.1 := ⟨⟨genericPoint (Spec (CommRingCat.of A)), trivial⟩⟩
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  have hN : NumericalCurveFieldDegree.degree f =
      Module.finrank Γ(Spec (CommRingCat.of A), ⊤) Γ(Y, ⊤) := by
    exact NumericalCurveFieldDegree.degree_eq_affineRank f U
  apply hN.trans
  apply Algebra.finrank_eq_of_equiv_equiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    (RingEquiv.refl Γ(Y, ⊤))
  ext c
  change ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop)) c = f.appTop c
  rw [Iso.hom_inv_id_assoc]

/-- Actual original finite schemes have finite native residue extensions over the SAME field. -/
theorem residueField_finite_of_isFinite {k : Type u} [Field k] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (CommRingCat.of k)) [IsFinite q] (z : Z) :
    letI := AffineSchemeLocalDegrees.residueAlgebra q z
    Module.Finite k (Z.residueField z) := by
  let : IsAffine Z := isAffine_of_isAffineHom q
  let := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra q
  let := AffineSchemeLocalDegrees.residueAlgebra q z
  let : Module.Finite k Γ(Z, ⊤) := SchemeLocalizedFiniteAlgebras.sections_module_finite q
  let : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite k Γ(Z, ⊤)
  let P := (isAffineOpen_top Z).primeIdealOf ⟨z, trivial⟩
  let S := Localization.AtPrime P.asIdeal
  let : Module.Finite k S :=
    Module.Finite.of_surjective (Algebra.algHom k Γ(Z, ⊤) S).toLinearMap
      (IsArtinianRing.localization_surjective P.asIdeal.primeCompl S)
  let : Module.Finite k (IsLocalRing.ResidueField S) := inferInstance
  exact Module.Finite.equiv
    (AffineSchemeLocalDegrees.residueLocalizationAlgEquiv q z).symm.toLinearEquiv

/-- Actual original Cartier support internally gives finite original ambient residue coefficients. -/
theorem residueField_finite_of_mem_support {k : Type u} [Field k]
    {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C ≤ 1) (I : C.IdealSheafData) (hI : I.IsInvertible)
    (x : C) (hx : x ∈ I.support) :
    letI := AffineSchemeLocalDegrees.residueAlgebra q x
    Module.Finite k (C.residueField x) := by
  let : IsProper q := hq.isProper
  let : IsFinite (I.subschemeι ≫ q) :=
    CurveCartierIdealDegrees.subscheme_comp_isFinite q hdim I hI
  let y : I.subscheme := ⟨x, hx⟩
  change letI := AffineSchemeLocalDegrees.residueAlgebra q (I.subschemeι y)
    Module.Finite k (C.residueField (I.subschemeι y))
  let := AffineSchemeLocalDegrees.residueAlgebra q (I.subschemeι y)
  let := AffineSchemeLocalDegrees.residueAlgebra (I.subschemeι ≫ q) y
  let : Module.Finite k (I.subscheme.residueField y) :=
    residueField_finite_of_isFinite (I.subschemeι ≫ q) y
  exact Module.Finite.equiv
    (ClosedImmersionResidueDegrees.residueFieldAlgEquiv I.subschemeι q y).symm.toLinearEquiv

end EnvelopeProperty.NumericalCartierCurveOrders
