import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionPrimeFiltration
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionSingleCutStability
import EnvelopeProperty.AlgGeom.SchemeAmpleCoherentGlobalGeneration
import EnvelopeProperty.AlgGeom.SchemeCoherentEulerAffine
import EnvelopeProperty.Projective.TestConfigurationSectionTransport
import EnvelopeProperty.AlgGeom.SchemeModuleGlobalSections
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Conditional reduction along the SAME original reduced point strata

The intended ordinary hypothesis is genuine native ampleness of the original
L on each literal reduced closure of an original point. Actual finite coherent
prime filtrations and actual maps are produced internally. The integral Nakai
induction is separate: its generic-point case is not assumed away here.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules CategoryTheory.MonoidalCategory TopCat TopCat.Sheaf
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionStrataReduction
open CanonicalGeometry SchemeCoherentEulerIndex SchemeCoherentEulerExact
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem fieldComplex_isZero_of_native {k : Type u} [Field k]
    {X : Scheme.{u}} [X.IsSeparated] (p : X ⟶ Spec (.of k))
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1))) :
    IsZero (((fieldComplexFunctor p U).obj M).homology (q + 1)) := by
  have hn := cechComplex_exactAt_succ_of_affine_openCover M U hU hUa q h
  have hb := (baseCechComplex_exactAt_iff p M U (q + 1)).mpr hn
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hb
  exact IsZero.of_iso ((ModuleCat.restrictScalars (baseScalar (k := k))).map_isZero hz)
    (fieldComplexHomologyIso p M U (q + 1))

private theorem closedPushforward_fieldComplex_isZero_of_native {k : Type u} [Field k]
    {X D : Scheme.{u}} [X.IsSeparated] (g : D ⟶ X) [IsClosedImmersion g]
    (p : X ⟶ Spec (.of k)) (P : D.Modules) [P.IsQuasicoherent]
    {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H P.sheaf (q + 1))) :
    IsZero (((fieldComplexFunctor p U).obj ((pushforward g).obj P)).homology (q + 1)) := by
  let : D.IsSeparated := ⟨by
    have hsep : IsSeparated (g ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let V := fun i => g ⁻¹ᵁ U i
  have hV : IsOpenCover V := g.iSup_preimage_eq_top hU
  have hVa : ∀ i, IsAffineOpen (V i) := fun i => (hUa i).preimage g
  have hz := fieldComplex_isZero_of_native (g ≫ p) P V hV hVa q h
  have hz' : IsZero (fieldCech (g ≫ p) P V (q + 1)) :=
    IsZero.of_iso hz (fieldComplexHomologyIso (g ≫ p) P V (q + 1)).symm
  have hz'' : IsZero (fieldCech p ((pushforward g).obj P) U (q + 1)) :=
    IsZero.of_iso hz' (SchemeCoherentEulerAffine.fieldCechPushforwardIso g p P U (q + 1)).symm
  exact IsZero.of_iso hz'' (fieldComplexHomologyIso p ((pushforward g).obj P) U (q + 1))

private def closedPieceTwistIso {X D : Scheme.{u}}
    (g : D ⟶ X) (T : D.Modules) (L : X.Modules) (hL : IsInvertible L) (m : ℕ) :
    (pushforward g).obj T ⊗ bundleTensorPower L m ≅
      (pushforward g).obj (T ⊗ bundleTensorPower ((Scheme.Modules.pullback g).obj L) m) :=
  SchemeLineProjectionFormula.lineProjectionFormulaObj g (bundleTensorPower L m)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m) T ≪≫
    (pushforward g).mapIso (Iso.refl T ⊗ᵢ
      TestConfigurationSectionTransport.tensorPowerPullbackIso g L m)

private theorem exists_closedPiece_powerCohomology_vanishing_of_ample
    {k : Type u} [Field k] {X D : Scheme.{u}} [X.IsSeparated]
    (g : D ⟶ X) [IsClosedImmersion g] (p : X ⟶ Spec (.of k))
    (T : D.Modules) [T.IsQuasicoherent] [T.IsFiniteType]
    {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (L : X.Modules) (hL : IsInvertible L)
    (hA : SchemeLineAmpleness.IsAmple (g ≫ p) ((Scheme.Modules.pullback g).obj L)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      IsZero (((fieldComplexFunctor p U).obj
        ((pushforward g).obj T ⊗ bundleTensorPower L m)).homology (q + 1)) := by
  obtain ⟨hM, r, hr, d, i, hi, _hbase, ⟨η⟩⟩ := hA
  let : IsClosedImmersion i := hi
  obtain ⟨N, hN⟩ := OriginalAmpleSerreVanishing.exists_sheafCohomology_bound i
    T ((Scheme.Modules.pullback g).obj L) hM r hr (0 : Fin (d + 1)) η.symm
  refine ⟨N, fun m hm q => ?_⟩
  let P := T ⊗ bundleTensorPower ((Scheme.Modules.pullback g).obj L) m
  let : P.IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight T _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m)
  have hz := closedPushforward_fieldComplex_isZero_of_native g p P U hU hUa q (hN m hm q)
  let eH := HomologicalComplex.homologyMapIso
    ((fieldComplexFunctor p U).mapIso (closedPieceTwistIso g T L hL m)) (q + 1)
  exact IsZero.of_iso hz eH

private theorem powerCohomology_vanishing_of_actualFiltration
    {k : Type u} [Field k] {X : Scheme.{u}} [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (L : X.Modules) (hL : IsInvertible L)
    (hstrata : ∀ eta : X,
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p) ((Scheme.Modules.pullback I.subschemeι).obj L))
    {n : ℕ} {M : X.Modules}
    (fil : SeshadriAmplenessCriterion.ActualCoherentPrimeFiltration n M) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      IsZero (((fieldComplexFunctor p U).obj (M ⊗ bundleTensorPower L m)).homology (q + 1)) := by
  induction fil with
  | zero M hM =>
      refine ⟨0, fun m _hm q => ?_⟩
      let P := bundleTensorPower L m
      let : (tensorRight P).IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence
        P (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)
      exact (tensorRight P ⋙ fieldComplexFunctor p U ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℕ) (q + 1)).map_isZero hM
  | iso e fil ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N, fun m hm q => ?_⟩
      let eH := HomologicalComplex.homologyMapIso ((fieldComplexFunctor p U).mapIso
        ((tensorRight (bundleTensorPower L m)).mapIso e)) (q + 1)
      exact IsZero.of_iso (hN m hm q) eH.symm
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e fil ih =>
      let : S.X₁.IsQuasicoherent := hQ₁
      let : S.X₂.IsQuasicoherent := hQ₂
      let : S.X₃.IsQuasicoherent := hQ₃
      let : S.X₁.IsFiniteType := hF₁
      let : S.X₂.IsFiniteType := hF₂
      let : S.X₃.IsFiniteType := hF₃
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      let : T.IsQuasicoherent := hT.isQuasicoherent
      let : T.IsFinitePresentation := hT.isFinitePresentation
      let : T.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
        (R := I.subscheme.ringCatSheaf) T
      obtain ⟨N₁, hN₁⟩ := ih
      obtain ⟨N₃, hN₃⟩ := exists_closedPiece_powerCohomology_vanishing_of_ample
        I.subschemeι p T U hU hUa L hL (hstrata eta)
      refine ⟨max N₁ N₃, fun m hm q => ?_⟩
      let P := bundleTensorPower L m
      have hP := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m
      let : (tensorRight P).IsEquivalence :=
        SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence P hP
      let S' := S.map (tensorRight P)
      have hS' : S'.ShortExact := SchemeInvertibleTensorEquivalence.tensorRight_shortExact P hP S hS
      let : S'.X₁.IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₁ P hP
      let : S'.X₂.IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₂ P hP
      let : S'.X₃.IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₃ P hP
      let C := S'.map (fieldComplexFunctor p U)
      have hC : C.ShortExact :=
        (hS'.map_baseCechComplexFunctor_of_affine_openCover p U hUa).map_of_exact
          ((ModuleCat.restrictScalars (baseScalar (k := k))).mapHomologicalComplex (.up ℕ))
      have hzero₁ : IsZero (C.X₁.homology (q + 1)) :=
        hN₁ m ((le_max_left N₁ N₃).trans hm) q
      let eH := HomologicalComplex.homologyMapIso ((fieldComplexFunctor p U).mapIso
        ((tensorRight P).mapIso e)) (q + 1)
      have hzero₃ : IsZero (C.X₃.homology (q + 1)) := IsZero.of_iso
        (hN₃ m ((le_max_right N₁ N₃).trans hm) q) eH
      have : Mono (HomologicalComplex.homologyMap C.g (q + 1)) :=
        (hC.homology_exact₂ (q + 1)).mono_g (hzero₁.eq_of_src _ _)
      change IsZero (C.X₂.homology (q + 1))
      apply (IsZero.iff_id_eq_zero _).mpr
      apply (cancel_mono (HomologicalComplex.homologyMap C.g (q + 1))).mp
      exact hzero₃.eq_of_tgt _ _

/-- Every SAME original coherent twist has eventually zero positive actual
field-complex cohomology when the SAME original L is genuinely ample on every
literal reduced original point closure. The actual finite filtration is produced
internally; no integral ambient, incoming filtration or vanishing certificate. -/
theorem exists_eventual_fieldCohomology_vanishing_of_strataAmple
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hL : IsInvertible L)
    (hstrata : ∀ eta : X,
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p) ((Scheme.Modules.pullback I.subschemeι).obj L)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      IsZero (((fieldComplexFunctor p U).obj (F ⊗ bundleTensorPower L m)).homology (q + 1)) := by
  classical
  let hp := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : X.IsSeparated := ⟨by
    have hsep : IsSeparated (p ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain ⟨n, fil⟩ := SeshadriAmplenessCriterion.exists_finite_coherent_primeFiltration p F
  exact powerCohomology_vanishing_of_actualFiltration p U hU hUa L hL hstrata fil

private theorem pushforward_epi_of_isAffineHom {X D : Scheme.{u}}
    (g : D ⟶ X) [IsAffineHom g] {M N : D.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (v : M ⟶ N) [Epi v] :
    Epi ((pushforward g).map v) := by
  have hloc : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map ((pushforward g).map v)) := by
    constructor
    intro W s x hx
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := W) (x := x) hx
    refine ⟨V, homOfLE hVW, ?_, hxV⟩
    exact isQuasicoherent_app_surjective_of_epi (g ⁻¹ᵁ V) (hV.preimage g) v _
  let := hloc
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map inferInstance

private theorem exists_generatingSections_closedPushforward {X D : Scheme.{u}}
    (g : D ⟶ X) [IsClosedImmersion g] (T : D.Modules) [T.IsQuasicoherent]
    (G : T.GeneratingSections) (hG : G.IsFiniteType) :
    ∃ H : ((pushforward g).obj T).GeneratingSections, H.IsFiniteType := by
  let : G.IsFiniteType := hG
  let GP := pushforward g
  let : PreservesBiproductsOfShape G.I GP :=
    preservesBiproductsOfShape_of_preservesProductsOfShape GP
  let : PreservesColimitsOfShape (Discrete G.I) GP :=
    preservesCoproductsOfShape_of_preservesBiproductsOfShape GP
  let q := FiniteClosedIdealEuler.quotientMap g
  let q₀ : SheafOfModules.free (R := X.ringCatSheaf) G.I ⟶
      ∐ (fun _ : G.I => GP.obj (unitObj D)) := Limits.Sigma.map (fun _ : G.I => q)
  have hq₀ : Epi q₀ := by
    constructor
    intro Q a b hab
    apply Sigma.hom_ext
    intro i
    apply (cancel_epi q).mp
    have hi : Sigma.ι (fun _ : G.I => unitObj X) i ≫ q₀ =
        q ≫ Sigma.ι (fun _ : G.I => GP.obj (unitObj D)) i :=
      Sigma.ι_map (fun _ : G.I => q) i
    have hh := congrArg (fun z => Sigma.ι (fun _ : G.I => unitObj X) i ≫ z) hab
    calc
      q ≫ (Sigma.ι (fun _ : G.I => GP.obj (unitObj D)) i ≫ a) =
          (Sigma.ι (fun _ : G.I => unitObj X) i ≫ q₀) ≫ a := by rw [hi, Category.assoc]
      _ = (Sigma.ι (fun _ : G.I => unitObj X) i ≫ q₀) ≫ b := by
        simpa only [Category.assoc] using hh
      _ = _ := by rw [hi, Category.assoc]
  let : (SheafOfModules.free (R := D.ringCatSheaf) G.I).IsQuasicoherent := inferInstance
  let : Epi G.π := G.epi
  have hπ : Epi (GP.map G.π) := pushforward_epi_of_isAffineHom g G.π
  let t : SheafOfModules.free (R := X.ringCatSheaf) G.I ⟶ GP.obj T :=
    q₀ ≫ (PreservesCoproduct.iso GP (fun _ : G.I => unitObj D)).inv ≫ GP.map G.π
  have ht : Epi t := by
    let := hq₀
    let := hπ
    infer_instance
  let H : (GP.obj T).GeneratingSections :=
    { I := G.I
      s := (GP.obj T).freeHomEquiv t
      epi := by simpa only [Equiv.symm_apply_apply] using ht }
  refine ⟨H, ?_⟩
  constructor
  change Finite G.I
  infer_instance

private theorem sectionHom_of_top {X : Scheme.{u}} {M : X.Modules}
    (a : unitObj X ⟶ M) :
    SchemeModuleGlobalSections.sectionHom M
      (a.val.app (.op (⊤ : X.Opens)) (1 : Γ(X, ⊤))) = a := by
  apply M.unitHomEquiv.injective
  rw [SchemeModuleGlobalSections.sectionHom, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro V
  change M.val.map (homOfLE (show V.unop ≤ (⊤ : X.Opens) from le_top)).op
      ((M.unitHomEquiv a).val (.op ⊤)) = (M.unitHomEquiv a).val V
  exact PresheafOfModules.sections_property (M.unitHomEquiv a)
    (homOfLE (show V.unop ≤ (⊤ : X.Opens) from le_top)).op

private theorem exists_generatingSections_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (A : S.X₁.GeneratingSections) (hA : A.IsFiniteType)
    (C : S.X₃.GeneratingSections) (hC : C.IsFiniteType)
    (hsurj : Function.Surjective (S.g.app (⊤ : X.Opens))) :
    ∃ G : S.X₂.GeneratingSections, G.IsFiniteType := by
  classical
  let : A.IsFiniteType := hA
  let : C.IsFiniteType := hC
  have hex (j : C.I) : ∃ x : Γ(S.X₂, (⊤ : X.Opens)),
      S.g.app (⊤ : X.Opens) x =
        (SchemeGeneratingSectionsUnit.generatorHom C j).val.app (.op ⊤) (1 : Γ(X, ⊤)) :=
    hsurj _
  choose x hx using hex
  let β (j : C.I) : unitObj X ⟶ S.X₂ := SchemeModuleGlobalSections.sectionHom S.X₂ (x j)
  have hβ (j : C.I) : β j ≫ S.g = SchemeGeneratingSectionsUnit.generatorHom C j := by
    change SchemeModuleGlobalSections.sectionHom S.X₂ (x j) ≫ S.g = _
    rw [SchemeModuleGlobalSections.sectionHom_comp]
    exact (congrArg (SchemeModuleGlobalSections.sectionHom S.X₃) (hx j)).trans
      (sectionHom_of_top (SchemeGeneratingSectionsUnit.generatorHom C j))
  let fam : A.I ⊕ C.I → (unitObj X ⟶ S.X₂) :=
    Sum.elim (fun i => SchemeGeneratingSectionsUnit.generatorHom A i ≫ S.f) β
  let t : SheafOfModules.free (R := X.ringCatSheaf) (A.I ⊕ C.I) ⟶ S.X₂ := Sigma.desc fam
  have hleft (i : A.I) : SheafOfModules.ιFree (Sum.inl i) ≫ t =
      SchemeGeneratingSectionsUnit.generatorHom A i ≫ S.f := Sigma.ι_desc fam (Sum.inl i)
  have hright (j : C.I) : SheafOfModules.ιFree (Sum.inr j) ≫ t = β j :=
    Sigma.ι_desc fam (Sum.inr j)
  have ht : Epi t := by
    constructor
    intro Q a b hab
    have ha : S.f ≫ a = S.f ≫ b := by
      apply A.epi.left_cancellation
      apply Sigma.hom_ext
      intro i
      have hh := congrArg (fun v => SheafOfModules.ιFree (Sum.inl i) ≫ v) hab
      have hh' : (SchemeGeneratingSectionsUnit.generatorHom A i ≫ S.f) ≫ a =
          (SchemeGeneratingSectionsUnit.generatorHom A i ≫ S.f) ≫ b := by
        simpa only [← Category.assoc, hleft] using hh
      simpa only [SchemeGeneratingSectionsUnit.generatorHom, SheafOfModules.ιFree,
        Category.assoc] using hh'
    have hd : S.f ≫ (a - b) = 0 := by rw [Preadditive.comp_sub, ha, sub_self]
    let fac := CokernelCofork.IsColimit.desc' hS.gIsCokernel (a - b) hd
    have hz : S.g ≫ fac.val = a - b := fac.property
    have hz₀ : fac.val = 0 := by
      apply C.epi.left_cancellation
      apply Sigma.hom_ext
      intro j
      have hh := congrArg (fun v => SheafOfModules.ιFree (Sum.inr j) ≫ v) hab
      have hb : β j ≫ a = β j ≫ b := by
        simpa only [← Category.assoc, hright] using hh
      have hj : SchemeGeneratingSectionsUnit.generatorHom C j ≫ fac.val = 0 := by
        calc
          _ = β j ≫ (S.g ≫ fac.val) := by
            simpa only [Category.assoc] using congrArg (fun v => v ≫ fac.val) (hβ j).symm
          _ = β j ≫ (a - b) := by rw [hz]
          _ = 0 := by rw [Preadditive.comp_sub, hb, sub_self]
      simpa only [SchemeGeneratingSectionsUnit.generatorHom, SheafOfModules.ιFree,
        Category.assoc, comp_zero] using hj
    apply sub_eq_zero.mp
    calc
      a - b = S.g ≫ fac.val := hz.symm
      _ = 0 := by rw [hz₀, comp_zero]
  let G : S.X₂.GeneratingSections :=
    { I := A.I ⊕ C.I
      s := S.X₂.freeHomEquiv t
      epi := by simpa only [Equiv.symm_apply_apply] using ht }
  refine ⟨G, ?_⟩
  constructor
  change Finite (A.I ⊕ C.I)
  infer_instance

private theorem generatingSections_of_actualFiltration
    {k : Type u} [Field k] {X : Scheme.{u}} [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (L : X.Modules) (hL : IsInvertible L)
    (hstrata : ∀ eta : X,
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p) ((Scheme.Modules.pullback I.subschemeι).obj L))
    {n : ℕ} {M : X.Modules}
    (fil : SeshadriAmplenessCriterion.ActualCoherentPrimeFiltration n M) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (M ⊗ bundleTensorPower L m).GeneratingSections, G.IsFiniteType := by
  induction fil with
  | zero M hM =>
      refine ⟨0, fun m _hm => ?_⟩
      let P := bundleTensorPower L m
      let : (tensorRight P).IsEquivalence := SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence
        P (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)
      have hz : IsZero (M ⊗ P) := (tensorRight P).map_isZero hM
      let G : (M ⊗ P).GeneratingSections :=
        { I := ULift.{u} Empty
          s := fun i => Empty.elim i.down
          epi := hz.epi _ }
      refine ⟨G, ?_⟩
      constructor
      change Finite (ULift.{u} Empty)
      infer_instance
  | iso e fil ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N, fun m hm => ?_⟩
      obtain ⟨G, hG⟩ := hN m hm
      let : G.IsFiniteType := hG
      exact ⟨G.ofEpi ((tensorRight (bundleTensorPower L m)).mapIso e).hom, inferInstance⟩
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e fil ih =>
      let : S.X₁.IsQuasicoherent := hQ₁
      let : S.X₂.IsQuasicoherent := hQ₂
      let : S.X₃.IsQuasicoherent := hQ₃
      let : S.X₁.IsFiniteType := hF₁
      let : S.X₂.IsFiniteType := hF₂
      let : S.X₃.IsFiniteType := hF₃
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      let : T.IsQuasicoherent := hT.isQuasicoherent
      let : T.IsFinitePresentation := hT.isFinitePresentation
      let : T.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
        (R := I.subscheme.ringCatSheaf) T
      obtain ⟨N₀, hN₀⟩ := powerCohomology_vanishing_of_actualFiltration p U hU hUa L hL hstrata fil
      obtain ⟨N₁, hN₁⟩ := ih
      obtain ⟨N₃, hN₃⟩ := SchemeAmpleCoherentGlobalGeneration.exists_eventual_generatingSections
        (I.subschemeι ≫ p) T ((Scheme.Modules.pullback I.subschemeι).obj L) (hstrata eta)
      refine ⟨max N₀ (max N₁ N₃), fun m hm => ?_⟩
      have hm₀ : N₀ ≤ m := (le_max_left N₀ (max N₁ N₃)).trans hm
      have hm₁ : N₁ ≤ m := (le_max_left N₁ N₃).trans
        ((le_max_right N₀ (max N₁ N₃)).trans hm)
      have hm₃ : N₃ ≤ m := (le_max_right N₁ N₃).trans
        ((le_max_right N₀ (max N₁ N₃)).trans hm)
      let P := bundleTensorPower L m
      have hP := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m
      let : (tensorRight P).IsEquivalence :=
        SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence P hP
      let S' := S.map (tensorRight P)
      have hS' : S'.ShortExact := SchemeInvertibleTensorEquivalence.tensorRight_shortExact P hP S hS
      let : S'.X₁.IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₁ P hP
      let : S'.X₂.IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₂ P hP
      let : S'.X₃.IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₃ P hP
      obtain ⟨G₁, hG₁⟩ := hN₁ m hm₁
      obtain ⟨GT, hGT⟩ := hN₃ m hm₃
      let Tm := T ⊗ bundleTensorPower ((Scheme.Modules.pullback I.subschemeι).obj L) m
      let : Tm.IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight T _
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible (hL.pullback I.subschemeι) m)
      obtain ⟨GP, hGP⟩ := exists_generatingSections_closedPushforward I.subschemeι Tm GT hGT
      let : GP.IsFiniteType := hGP
      let γ : S'.X₃ ≅ (pushforward I.subschemeι).obj Tm :=
        (tensorRight P).mapIso e ≪≫ closedPieceTwistIso I.subschemeι T L hL m
      let G₃ : S'.X₃.GeneratingSections := GP.ofEpi γ.inv
      have hG₃ : G₃.IsFiniteType := by dsimp only [G₃]; infer_instance
      have hz : IsZero (((fieldComplexFunctor p U).obj S'.X₁).homology 1) := hN₀ m hm₀ 0
      have hmono : Mono (HomologicalComplex.homologyMap ((fieldComplexFunctor p U).map S'.f) 1) :=
        hz.mono _
      have hsurj := SeshadriAmplenessCriterionSingleCutStability.sections_surjective_of_hOne_mono
        p U hU hUa S' hS' hmono
      exact exists_generatingSections_of_shortExact S' hS' G₁ hG₁ G₃ hG₃ hsurj

/-- Ordinary genuine ampleness of SAME L on each literal reduced original point
closure internally produces finite generators of EVERY sufficiently large SAME
original coherent twist. The actual filtration, all quotient generators and all
section lifts are constructed inside; no integral ambient or lifting certificate. -/
theorem exists_eventual_generatingSections_of_strataAmple
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p]
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (hL : IsInvertible L)
    (hstrata : ∀ eta : X,
      let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
      SchemeLineAmpleness.IsAmple (I.subschemeι ≫ p) ((Scheme.Modules.pullback I.subschemeι).obj L)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (F ⊗ bundleTensorPower L m).GeneratingSections, G.IsFiniteType := by
  classical
  let hp := ProjectiveFactorizationRingIso.of_isProjective p
  let : IsProper p := hp.isProper
  let : X.IsSeparated := ⟨by
    have hsep : IsSeparated (p ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let U := finiteAffineOpens X
  let : Fintype (finiteAffineCover X).I₀ := Fintype.ofFinite _
  let : LinearOrder (finiteAffineCover X).I₀ :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  obtain ⟨n, fil⟩ := SeshadriAmplenessCriterion.exists_finite_coherent_primeFiltration p F
  exact generatingSections_of_actualFiltration p U (finiteAffineOpens_cover X)
    (finiteAffineOpens_isAffine X) L hL hstrata fil

#print axioms generatingSections_of_actualFiltration
#print axioms exists_eventual_generatingSections_of_strataAmple
#print axioms exists_generatingSections_of_shortExact
#print axioms pushforward_epi_of_isAffineHom
#print axioms exists_generatingSections_closedPushforward
#print axioms sectionHom_of_top
#print axioms powerCohomology_vanishing_of_actualFiltration
#print axioms exists_eventual_fieldCohomology_vanishing_of_strataAmple
#print axioms closedPieceTwistIso
#print axioms exists_closedPiece_powerCohomology_vanishing_of_ample
end EnvelopeProperty.SeshadriAmplenessCriterionStrataReduction
