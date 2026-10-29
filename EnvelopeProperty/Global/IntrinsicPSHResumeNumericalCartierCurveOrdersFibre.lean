import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalCartierCurveOrdersFull
import EnvelopeProperty.AlgGeom.IntegralSchemeDimension

/-! # Whole actual finite fibres of original principal Cartier charts

The original geometric ideal comap supplies the actual source equation;
native section orders and the same canonical field degree then project
the entire original fibre. No order or residue matching data is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors
universe u
namespace EnvelopeProperty.NumericalCartierCurveOrders
open CurveCartierLocalOrders

/-- An actual principal original Cartier chart projects its whole finite fibre,
with all source geometry and the SAME canonical field degree derived internally. -/
theorem finsum_fibre_weightedLocalOrder_principal_spec
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of A)) [IsFinite f] [IsDominant f]
    (x : PrimeSpectrum A) (hx : x ≠ ⊥)
    [Module.Finite k (IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal))]
    (a : A) (ha : a ≠ 0)
    (I : (Spec (CommRingCat.of A)).IdealSheafData) (hI : I.IsInvertible)
    (hgen : I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv a}) :
    let s : Spec (CommRingCat.of A) := x
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    (∑ᶠ y : {y : Y // f y = s}, weightedLocalOrder
      (f ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (I.comap f) (hI.comap_of_dominant_integral f) y.1) =
      (NumericalCurveFieldDegree.degree f : ℤ) *
        weightedLocalOrder (Spec.map (CommRingCat.ofHom (algebraMap k A))) I hI s := by
  let s : Spec (CommRingCat.of A) := x
  let q := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let : IsAffine Y := isAffine_of_isAffineHom f
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let : IsDomain Γ(Y, ⊤) := IsIntegral.component_integral ⊤
  let J := I.comap f
  let hJ : J.IsInvertible := hI.comap_of_dominant_integral f
  let c : Γ(Y, ⊤) := ProperBirationalSections.coefficientMap f a
  have hgenJ : J.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {c} := by
    rw [Scheme.IdealSheafData.comap_ideal_top_of_isAffine_native, hgen,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hc : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp
    (hJ.generator_mem_nonZeroDivisors ⟨⊤, isAffineOpen_top Y⟩ c hgenJ)
  have hdimA : topologicalKrullDim (Spec (CommRingCat.of A)) ≤ 1 := by
    change topologicalKrullDim (PrimeSpectrum A) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
  have hdimY : topologicalKrullDim Y ≤ 1 :=
    IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom f 1 hdimA
  have hleft (y : Y) : weightedLocalOrder (f ≫ q) J hJ y =
      SchemeRegularSectionOrders.weightedOrder (f ≫ q) c y := by
    unfold weightedLocalOrder SchemeRegularSectionOrders.weightedOrder
    rw [localOrder_eq_ord_of_local_equation J hJ ⟨⊤, isAffineOpen_top Y⟩
      c hc hgenJ y trivial]
  have hsum := FiniteFibrePrincipalOrders.finsum_fibre_principal_orders
    (k := k) f x hdimY hx a ha
  change (∑ᶠ y : {y : Y // f y = s}, weightedLocalOrder (f ≫ q) J hJ y.1) = _
  simp_rw [hleft]
  change (∑ᶠ y : {y : Y // f y = x}, SchemeRegularSectionOrders.weightedOrder
    (FiniteFibrePrincipalOrders.sourceFieldStructure (k := k) f)
    (ProperBirationalSections.coefficientMap f a) y.1) = _
  rw [hsum, weightedLocalOrder_principal_spec (k := k) x hx a ha I hI hgen]
  let := FlatGlobalSections.sectionsAlgebra f
  rw [degree_eq_sectionsRank f]
  ring

private theorem affine_structureMap_spec {k : Type u} [Field k]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (CommRingCat.of k)) :
    letI := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra p
    X.isoSpec.inv ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤))) := by
  change X.isoSpec.inv ≫ p =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop)
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  exact (Scheme.isoSpec_inv_naturality p).symm

private def restrictFibreEquiv {C D : Scheme.{u}} (g : D ⟶ C)
    (U : C.Opens) (u : U.toScheme) :
    {y : D // g y = U.ι u} ≃
      {v : (g ⁻¹ᵁ U).toScheme // g.resLE U (g ⁻¹ᵁ U) le_rfl v = u} where
  toFun y := by
    let v : (g ⁻¹ᵁ U).toScheme :=
      ⟨y.1, by change g y.1 ∈ U; rw [y.2]; exact u.2⟩
    refine ⟨v, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    have ht := congrArg (fun a : (g ⁻¹ᵁ U).toScheme ⟶ C => a v)
      (g.resLE_comp_ι (U := U) (V := g ⁻¹ᵁ U) le_rfl)
    change U.ι (g.resLE U (g ⁻¹ᵁ U) le_rfl v) = g ((g ⁻¹ᵁ U).ι v) at ht
    exact ht.trans y.2
  invFun v := ⟨v.1.1, by
    have ht := congrArg (fun a : (g ⁻¹ᵁ U).toScheme ⟶ C => a v.1)
      (g.resLE_comp_ι (U := U) (V := g ⁻¹ᵁ U) le_rfl)
    change U.ι (g.resLE U (g ⁻¹ᵁ U) le_rfl v.1) = g ((g ⁻¹ᵁ U).ι v.1) at ht
    have h := congrArg U.ι v.2
    exact ht.symm.trans h⟩
  left_inv y := Subtype.ext rfl
  right_inv v := Subtype.ext (Subtype.ext rfl)

private def fibreIsoTargetEquiv {Y C C' : Scheme.{u}}
    (f : Y ⟶ C) (e : C ≅ C') (x : C) :
    {y : Y // f y = x} ≃ {y : Y // (f ≫ e.hom) y = e.hom x} where
  toFun y := ⟨y.1, by
    change e.hom (f y.1) = e.hom x
    exact congrArg e.hom y.2⟩
  invFun y := ⟨y.1, by
    have h : e.hom (f y.1) = e.hom x := y.2
    exact (Scheme.homeoOfIso e).injective h⟩
  left_inv y := Subtype.ext rfl
  right_inv y := Subtype.ext rfl

private def chartMap {C D : Scheme.{u}} (g : D ⟶ C) (U : C.affineOpens) :
    (g ⁻¹ᵁ U.1).toScheme ⟶ Spec Γ(U.1.toScheme, ⊤) :=
  letI : IsAffine U.1.toScheme := U.2
  g.resLE U.1 (g ⁻¹ᵁ U.1) le_rfl ≫ U.1.toScheme.isoSpec.hom

private instance chartMap_isFinite {C D : Scheme.{u}} (g : D ⟶ C)
    [IsFinite g] (U : C.affineOpens) : IsFinite (chartMap g U) := by
  let : IsAffine U.1.toScheme := U.2
  let r := g.resLE U.1 (g ⁻¹ᵁ U.1) le_rfl
  let : IsFinite r := by
    dsimp only [r]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  change IsFinite (r ≫ U.1.toScheme.isoSpec.hom)
  infer_instance

private instance chartMap_isDominant {C D : Scheme.{u}}
    [IsIntegral C] [IsIntegral D] (g : D ⟶ C) [IsDominant g]
    (U : C.affineOpens) [Nonempty U.1] : IsDominant (chartMap g U) := by
  let : IsAffine U.1.toScheme := U.2
  let V := g ⁻¹ᵁ U.1
  let : Nonempty V := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
  let v : V := Classical.choice (SchemeFinitePrincipalDegrees.nonempty_preimage g U.1)
  let : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨v.1, v.2⟩)
  let r := g.resLE U.1 V le_rfl
  have : IsDominant (r ≫ U.1.ι) := by
    change IsDominant (g.resLE U.1 V le_rfl ≫ U.1.ι)
    rw [g.resLE_comp_ι]
    infer_instance
  let : IsDominant r := IsDominant.of_comp_of_isOpenImmersion r U.1.ι
  change IsDominant (r ≫ U.1.toScheme.isoSpec.hom)
  infer_instance

private theorem chartMap_degree {C D : Scheme.{u}}
    [IsIntegral C] [IsIntegral D] (g : D ⟶ C) [IsDominant g] [IsFinite g]
    (U : C.affineOpens) [Nonempty U.1] :
    letI := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
    NumericalCurveFieldDegree.degree (chartMap g U) = NumericalCurveFieldDegree.degree g := by
  let : IsAffine U.1.toScheme := U.2
  let V := g ⁻¹ᵁ U.1
  let : Nonempty V := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
  let : Nonempty U.1.toScheme := inferInstanceAs (Nonempty U.1)
  let : Nonempty V.toScheme := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
  let : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let hdomU : IsDomain Γ(U.1.toScheme, ⊤) := IsIntegral.component_integral ⊤
  let : IsDomain Γ(U.1.toScheme, ⊤) := hdomU
  let : Algebra Γ(C, U.1) Γ(D, V) := (g.app U.1).hom.toAlgebra
  let : Algebra Γ(U.1.toScheme, ⊤) Γ(V.toScheme, ⊤) :=
    FlatGlobalSections.sectionsAlgebra (chartMap g U)
  have hleft := @degree_eq_sectionsRank Γ(U.1.toScheme, ⊤) inferInstance hdomU
    V.toScheme inferInstance (chartMap g U) inferInstance inferInstance
  have hright := NumericalCurveFieldDegree.degree_eq_affineRank g U
  apply hleft.trans
  apply Eq.trans _ hright.symm
  apply Algebra.finrank_eq_of_equiv_equiv U.1.topIso.commRingCatIsoToRingEquiv
    V.topIso.commRingCatIsoToRingEquiv
  ext c
  change (g.app U.1) (U.1.topIso.hom c) =
    V.topIso.hom (ProperBirationalSections.coefficientMap (chartMap g U) c)
  have hc : (Scheme.ΓSpecIso Γ(U.1.toScheme, ⊤)).inv ≫ (chartMap g U).appTop =
      U.1.topIso.hom ≫ g.app U.1 ≫ V.topIso.inv := by
    change (Scheme.ΓSpecIso Γ(U.1.toScheme, ⊤)).inv ≫
      (g.resLE U.1 V le_rfl ≫ U.1.toScheme.toSpecΓ).appTop = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
    change (g.resLE U.1 V le_rfl).app ⊤ = _
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
  have hcc := ConcreteCategory.congr_hom hc c
  change ProperBirationalSections.coefficientMap (chartMap g U) c =
    (U.1.topIso.hom ≫ g.app U.1 ≫ V.topIso.inv) c at hcc
  rw [hcc]
  change (U.1.topIso.hom ≫ g.app U.1) c =
    (U.1.topIso.hom ≫ g.app U.1 ≫ V.topIso.inv ≫ V.topIso.hom) c
  rw [Iso.inv_hom_id, Category.comp_id]

private theorem isoSpec_inv_appTop_native (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, ⊤)).hom, Iso.inv_hom_id,
    ← Scheme.toSpecΓ_appTop X]
  change X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 Γ(X, ⊤)
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
  rfl

private theorem open_principalTop {C : Scheme.{u}} (I : C.IdealSheafData)
    (U : C.affineOpens) (c : Γ(C, U.1)) (hgen : I.ideal U = Ideal.span {c}) :
    letI : IsAffine U.1.toScheme := U.2
    (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
      Ideal.span {U.1.topIso.inv c} := by
  let : IsAffine U.1.toScheme := U.2
  have h := I.comap_open_ideal_top_map U.2
  rw [hgen] at h
  have hh := congrArg (Ideal.map U.1.topIso.inv.hom) h
  rw [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id,
    CommRingCat.hom_id, Ideal.map_id, Ideal.map_span, Set.image_singleton] at hh
  exact hh

private theorem isoSpec_principalTop {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (a : Γ(X, ⊤))
    (hgen : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a}) :
    (I.comap X.isoSpec.inv).ideal ⟨⊤, isAffineOpen_top (Spec Γ(X, ⊤))⟩ =
      Ideal.span {(Scheme.ΓSpecIso Γ(X, ⊤)).inv a} := by
  rw [Scheme.IdealSheafData.comap_ideal_top_of_isAffine_native, hgen,
    Ideal.map_span, Set.image_singleton, isoSpec_inv_appTop_native]

private theorem affine_residue_finite {k : Type u} [Field k]
    {C : Scheme.{u}} [IsAffine C] (q : C ⟶ Spec (CommRingCat.of k)) (x : C)
    (hfinite : letI := AffineSchemeLocalDegrees.residueAlgebra q x
      Module.Finite k (C.residueField x)) :
    letI := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra q
    let P : PrimeSpectrum Γ(C, ⊤) := C.isoSpec.hom x
    Module.Finite k (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal)) := by
  let R := Γ(C, ⊤)
  let : Algebra k R := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra q
  let P : PrimeSpectrum R := C.isoSpec.hom x
  let p : Spec (CommRingCat.of R) := P
  let qR := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hqR : C.isoSpec.inv ≫ q = qR := affine_structureMap_spec q
  have hpx : C.isoSpec.inv p = x := by
    change (C.isoSpec.hom ≫ C.isoSpec.inv) x = x
    rw [Iso.hom_inv_id]
    rfl
  have e := SchemeStalkMapLocalOrders.residueFieldAlgEquiv C.isoSpec.inv p q
  rw [hqR, hpx] at e
  let := AffineSchemeLocalDegrees.residueAlgebra q x
  let := AffineSchemeLocalDegrees.residueAlgebra qR p
  let : Module.Finite k (C.residueField x) := hfinite
  let : Module.Finite k ((Spec (CommRingCat.of R)).residueField p) :=
    Module.Finite.equiv e.toLinearEquiv
  exact Module.Finite.equiv (specResidueAlgEquiv (k := k) (A := R) P).toLinearEquiv

/-- The ENTIRE actual original fibre projects the SAME native Cartier weight.
All residue finiteness comes from original projective Cartier support, and the
actual degree is the canonical finite function-field extension degree. -/
theorem finsum_fibre_weightedLocalOrder {k : Type u} [Field k]
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (g : D ⟶ C) [IsFinite g] [IsDominant g]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C ≤ 1)
    (I : C.IdealSheafData) (hI : I.IsInvertible) (x : C) :
    letI : IsProper q := hq.isProper
    letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian q
    letI : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian g
    (∑ᶠ y : {y : D // g y = x}, weightedLocalOrder (g ≫ q)
      (I.comap g) (hI.comap_of_dominant_integral g) y.1) =
      (NumericalCurveFieldDegree.degree g : ℤ) * weightedLocalOrder q I hI x := by
  let : IsProper q := hq.isProper
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian g
  let J := I.comap g
  let hJ : J.IsInvertible := hI.comap_of_dominant_integral g
  change (∑ᶠ y : {y : D // g y = x}, weightedLocalOrder (g ≫ q) J hJ y.1) = _
  by_cases hx : x ∈ I.support
  · obtain ⟨U, hxU, c, hc, hgen⟩ := hI x
    obtain ⟨u, hu⟩ : ∃ u : U.1.toScheme, U.1.ι u = x := ⟨⟨x, hxU⟩, rfl⟩
    subst x
    let : Nonempty U.1 := ⟨u⟩
    let : IsAffine U.1.toScheme := U.2
    let : Nonempty U.1.toScheme := ⟨u⟩
    let : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
    let V := g ⁻¹ᵁ U.1
    let : Nonempty V := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
    let : Nonempty V.toScheme := SchemeFinitePrincipalDegrees.nonempty_preimage g U.1
    let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
    let R := Γ(U.1.toScheme, ⊤)
    let hdomR : IsDomain R := IsIntegral.component_integral ⊤
    let : IsDomain R := hdomR
    let : IsNoetherianRing R :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
    have hdimU : topologicalKrullDim U.1.toScheme ≤ 1 :=
      U.1.ι.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
    let : Ring.KrullDimLE 1 R := SchemeFinitePrincipalDegrees.sections_krullDimLE
      hdimU ⟨⊤, isAffineOpen_top U.1.toScheme⟩
    let qU := U.1.ι ≫ q
    let : Algebra k R := FiniteClosedIdealLocalDegrees.structureSectionsAlgebra qU
    let qR := Spec.map (CommRingCat.ofHom (algebraMap k R))
    let P : PrimeSpectrum R := U.1.toScheme.isoSpec.hom u
    let p : Spec (CommRingCat.of R) := P
    have hpx : U.1.toScheme.isoSpec.inv p = u := by
      change (U.1.toScheme.isoSpec.hom ≫ U.1.toScheme.isoSpec.inv) u = u
      rw [Iso.hom_inv_id]
      rfl
    have hqR : U.1.toScheme.isoSpec.inv ≫ qU = qR := affine_structureMap_spec qU
    let IU := I.comap U.1.ι
    let hIU : IU.IsInvertible := hI.comap_of_flat U.1.ι
    let IR := IU.comap U.1.toScheme.isoSpec.inv
    let hIR : IR.IsInvertible := hIU.comap_of_flat U.1.toScheme.isoSpec.inv
    let a : R := U.1.topIso.inv c
    have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
    have ha : a ≠ 0 := by
      simpa only [map_zero] using
        (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).injective.ne hc0
    have hgenU := open_principalTop I U c hgen
    have hgenR := isoSpec_principalTop IU a hgenU
    have hpMem : p ∈ IR.support := by
      rw [Scheme.IdealSheafData.support_comap]
      change U.1.toScheme.isoSpec.inv p ∈ IU.support
      rw [hpx, Scheme.IdealSheafData.support_comap]
      change U.1.ι u ∈ I.support
      exact hx
    have hpNonGeneric : p ≠ genericPoint (Spec (CommRingCat.of R)) := by
      intro h
      exact CurveFiniteClosedSubschemes.genericPoint_not_mem IR.support
        (CurveCartierIdealDegrees.support_ne_top IR hIR) (h ▸ hpMem)
    have hP : P ≠ ⊥ := by
      intro h
      apply hpNonGeneric
      exact h.trans (genericPoint_eq_bot_of_affine (R := CommRingCat.of R)).symm
    have hfiniteU : letI := AffineSchemeLocalDegrees.residueAlgebra qU u
        Module.Finite k (U.1.toScheme.residueField u) := by
      let := AffineSchemeLocalDegrees.residueAlgebra q (U.1.ι u)
      let := AffineSchemeLocalDegrees.residueAlgebra qU u
      let : Module.Finite k (C.residueField (U.1.ι u)) :=
        residueField_finite_of_mem_support q hq hdim I hI (U.1.ι u) hx
      exact Module.Finite.equiv
        (SchemeStalkMapLocalOrders.residueFieldAlgEquiv U.1.ι u q).toLinearEquiv
    let : Module.Finite k (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal)) :=
      affine_residue_finite qU u hfiniteU
    let f : V.toScheme ⟶ Spec (CommRingCat.of R) := chartMap g U
    have hsum := finsum_fibre_weightedLocalOrder_principal_spec
      (k := k) (A := R) (Y := V.toScheme) f P hP a ha IR hIR hgenR
    change (∑ᶠ y : {y : V.toScheme // f y = p}, weightedLocalOrder
      (f ≫ qR) (IR.comap f) (hIR.comap_of_dominant_integral f) y.1) =
      (NumericalCurveFieldDegree.degree f : ℤ) * weightedLocalOrder qR IR hIR p at hsum
    have hstruct : f ≫ qR = V.ι ≫ g ≫ q := by
      rw [← hqR]
      change (g.resLE U.1 V le_rfl ≫ U.1.toScheme.isoSpec.hom) ≫
        U.1.toScheme.isoSpec.inv ≫ (U.1.ι ≫ q) = _
      rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
        Scheme.Hom.resLE_comp_ι, Category.assoc]
    have hIdeals : IR.comap f = J.comap V.ι := by
      change ((I.comap U.1.ι).comap U.1.toScheme.isoSpec.inv).comap f =
        (I.comap g).comap V.ι
      simp only [← Scheme.IdealSheafData.comap_comp]
      congr 1
      change (g.resLE U.1 V le_rfl ≫ U.1.toScheme.isoSpec.hom) ≫
        U.1.toScheme.isoSpec.inv ≫ U.1.ι = V.ι ≫ g
      rw [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι]
    have hright : weightedLocalOrder q I hI (U.1.ι u) =
        weightedLocalOrder qR IR hIR p := by
      have ho := weightedLocalOrder_comap_open U.1.ι q I hI u
      have hs := weightedLocalOrder_comap_open U.1.toScheme.isoSpec.inv qU IU hIU p
      rw [hpx, hqR] at hs
      exact ho.trans hs
    rw [hstruct] at hsum
    simp only [hIdeals] at hsum
    have hN : NumericalCurveFieldDegree.degree f = NumericalCurveFieldDegree.degree g :=
      chartMap_degree g U
    rw [hN, ← hright] at hsum
    let e := (restrictFibreEquiv g U.1 u).trans
      (fibreIsoTargetEquiv (g.resLE U.1 V le_rfl) U.1.toScheme.isoSpec u)
    apply (finsum_eq_of_bijective e e.bijective ?_).trans hsum
    intro y
    exact weightedLocalOrder_comap_open V.ι (g ≫ q) J hJ (e y).1
  · have hz : weightedLocalOrder q I hI x = 0 := by
      unfold weightedLocalOrder
      rw [localOrder_eq_zero_of_not_mem_support I hI x hx, zero_mul]
    rw [hz, mul_zero]
    apply finsum_eq_zero_of_forall_eq_zero
    intro y
    have hy : y.1 ∉ J.support := by
      rw [Scheme.IdealSheafData.support_comap]
      change g y.1 ∉ I.support
      simpa only [y.2] using hx
    unfold weightedLocalOrder
    rw [localOrder_eq_zero_of_not_mem_support J hJ y.1 hy, zero_mul]

end EnvelopeProperty.NumericalCartierCurveOrders
