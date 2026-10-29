import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhood
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodAlgebra
import Mathlib.RingTheory.Localization.Away.Basic

/-! # The actual original finite-chart maps and their entire central quotients -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodCharts
open ProjectiveCentralFiberSectionLifting ProjectiveCentralFiberEmbeddingNeighborhood

private theorem sectionsHom_comp {R : Type u} [CommRing R] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of R)) (q : Z ⟶ Spec (CommRingCat.of R))
    (f : Y ⟶ Z) (hf : f ≫ q = p) (U : Z.Opens) :
    (f.app U).hom.comp (sectionsHom q U) = sectionsHom p (f ⁻¹ᵁ U) := by
  subst p
  have h₁ : q.appLE ⊤ U le_top ≫ f.appLE U (f ⁻¹ᵁ U) le_rfl =
      (f ≫ q).appLE ⊤ (f ⁻¹ᵁ U) le_top :=
    Scheme.Hom.appLE_comp_appLE f q ⊤ U (f ⁻¹ᵁ U) le_top le_rfl
  have h₂ : q.appLE ⊤ U le_top ≫ f.app U =
      q.appLE ⊤ U le_top ≫ f.appLE U (f ⁻¹ᵁ U) le_rfl :=
    congrArg (fun a : Γ(Z,U) ⟶ Γ(Y,f ⁻¹ᵁ U) => q.appLE ⊤ U le_top ≫ a)
      (f.app_eq_appLE (U := U))
  exact congrArg
    (fun a : Γ(Spec (CommRingCat.of R),⊤) ⟶ Γ(Y,f ⁻¹ᵁ U) =>
      a.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (h₂.trans h₁)

/-- On EVERY original affine target chart, the actual finite original map
surjects onto its SAME actual central quotient, internally from the genuine central
closed immersion and actual original parameter ideal. -/
theorem central_quotient_surjective {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) [IsFinite f] (hf : f ≫ q = p)
    [IsClosedImmersion (centralMap p q f hf)] (U : Z.affineOpens) :
    Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span {(f.app U.1).hom (sectionsHom q U.1 Polynomial.X)})).comp
        (f.app U.1).hom) := by
  let φ := (f.app U.1).hom
  let ψ := ((zeroInclusion p).app (f ⁻¹ᵁ U.1)).hom
  have hclosed : IsClosedImmersion (zeroInclusion p ≫ f) := by
    rw [← centralMap_inclusion p q f hf]
    infer_instance
  have hs := (isClosedImmersion_iff_isAffineHom.mp hclosed).2 U.1 U.2
  change Function.Surjective (ψ.comp φ) at hs
  have hV : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  have hker : RingHom.ker ψ = Ideal.span {φ (sectionsHom q U.1 Polynomial.X)} := by
    change RingHom.ker (((zeroInclusion p).app (f ⁻¹ᵁ U.1)).hom) = _
    rw [← Scheme.Hom.ker_apply (zeroInclusion p) ⟨f ⁻¹ᵁ U.1,hV⟩,
      zeroInclusion_ideal p ⟨f ⁻¹ᵁ U.1,hV⟩]
    exact congrArg (fun z : Γ(Y,f ⁻¹ᵁ U.1) => Ideal.span {z})
      (RingHom.congr_fun (sectionsHom_comp p q f hf U.1) Polynomial.X).symm
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := hs (ψ b)
  change ψ (φ a) = ψ b at ha
  refine ⟨a, ?_⟩
  have hmem : φ a - b ∈ Ideal.span {φ (sectionsHom q U.1 Polynomial.X)} := by
    rw [← hker]
    change ψ (φ a - b) = 0
    rw [map_sub, ha, sub_self]
  change Ideal.Quotient.mk (Ideal.span {φ (sectionsHom q U.1 Polynomial.X)}) (φ a) =
    Ideal.Quotient.mk (Ideal.span {φ (sectionsHom q U.1 Polynomial.X)}) b
  exact sub_eq_zero.mp (by simpa only [map_sub] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem))

private theorem closedImmersion_on_basicOpen_of_localization {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) (U : Z.affineOpens) (hV : IsAffineOpen (f ⁻¹ᵁ U.1))
    (r : Γ(Z,U.1)) (hs : Function.Surjective (Localization.awayMap (f.app U.1).hom r)) :
    IsClosedImmersion (f ∣_ Z.basicOpen r) := by
  let φ := (f.app U.1).hom
  let W := Z.basicOpen r
  let T := Y.basicOpen (φ r)
  have eT : T = f ⁻¹ᵁ W := (Scheme.preimage_basicOpen f r).symm
  have he : T ≤ f ⁻¹ᵁ W := eT.le
  let β : Γ(Z,W) →+* Γ(Y,T) := (f.appLE W T he).hom
  let : IsLocalization.Away r Γ(Z,W) := U.2.isLocalization_basicOpen r
  let : IsLocalization.Away (φ r) Γ(Y,T) := hV.isLocalization_basicOpen (φ r)
  have hn : Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op ≫ f.appLE W T he =
      f.app U.1 ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le (φ r))).op := by
    have hl : Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op ≫ f.appLE W T he =
        f.appLE U.1 T (Y.basicOpen_le (φ r)) :=
      f.map_appLE he (homOfLE (Z.basicOpen_le r)).op
    have hr : f.app U.1 ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le (φ r))).op =
        f.appLE U.1 T (Y.basicOpen_le (φ r)) :=
      (congrArg (fun a : Γ(Z,U.1) ⟶ Γ(Y,f ⁻¹ᵁ U.1) =>
        a ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le (φ r))).op)
        (f.app_eq_appLE (U := U.1))).trans
          (f.appLE_map le_rfl (homOfLE (Y.basicOpen_le (φ r))).op)
    exact hl.trans hr.symm
  have hβ : β = IsLocalization.Away.map Γ(Z,W) Γ(Y,T) φ r := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext a
    have h₁ : β (algebraMap Γ(Z,U.1) Γ(Z,W) a) =
        algebraMap Γ(Y,f ⁻¹ᵁ U.1) Γ(Y,T) (φ a) :=
      ConcreteCategory.congr_hom hn a
    have h₂ : (IsLocalization.Away.map Γ(Z,W) Γ(Y,T) φ r)
        (algebraMap Γ(Z,U.1) Γ(Z,W) a) =
          algebraMap Γ(Y,f ⁻¹ᵁ U.1) Γ(Y,T) (φ a) :=
      IsLocalization.map_eq _ a
    exact h₁.trans h₂.symm
  have hsurj : Function.Surjective β := by
    rw [hβ]
    exact (IsLocalization.Away.map_surjective_iff Γ(Z,W) Γ(Y,T) φ r).mpr
      (Localization.awayMap_surjective_iff.mp hs)
  have hW : IsAffineOpen W := U.2.basicOpen r
  have hT : IsAffineOpen T := hV.basicOpen (φ r)
  let g := f.resLE W T he
  have hambient : Spec.map (CommRingCat.ofHom β) ≫ hW.fromSpec = hT.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hW hT he
  have hsquare : Spec.map (CommRingCat.ofHom β) ≫ hW.isoSpec.inv =
      hT.isoSpec.inv ≫ g := by
    apply (cancel_mono W.ι).mp
    calc
      (Spec.map (CommRingCat.ofHom β) ≫ hW.isoSpec.inv) ≫ W.ι =
          Spec.map (CommRingCat.ofHom β) ≫ hW.fromSpec := Category.assoc _ _ _
      _ = hT.fromSpec ≫ f := hambient
      _ = (hT.isoSpec.inv ≫ g) ≫ W.ι := by
        dsimp only [g, IsAffineOpen.fromSpec]
        simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom β)) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have hcomp : IsClosedImmersion (hT.isoSpec.inv ≫ g) := by
    rw [← hsquare]
    infer_instance
  have hg : IsClosedImmersion g :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) hT.isoSpec.inv g).mp hcomp
  have hfull := (f.resLE_congr he rfl eT @IsClosedImmersion).mp hg
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hfull

/-- The SAME actual finite original morphism is a closed immersion on actual
internally chosen target basic opens covering ALL original central target points. -/
theorem exists_closedImmersion_chart {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    (q : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    (f : Y ⟶ Z) [IsFinite f] (hf : f ≫ q = p)
    [IsClosedImmersion (centralMap p q f hf)] (U : Z.affineOpens) :
    ∃ r : Γ(Z,U.1), r - 1 ∈ Ideal.span {sectionsHom q U.1 Polynomial.X} ∧
      IsClosedImmersion (f ∣_ Z.basicOpen r) ∧
      ∀ z : zeroFiber q, zeroInclusion q z ∈ U.1 → zeroInclusion q z ∈ Z.basicOpen r := by
  obtain ⟨r, hr, hs⟩ :=
    ProjectiveCentralFiberEmbeddingNeighborhoodAlgebra.exists_localization_surjective
      (f.app U.1).hom (f.finite_app U.1 U.2) (sectionsHom q U.1 Polynomial.X)
      (central_quotient_surjective p q f hf U)
  have hclosed := closedImmersion_on_basicOpen_of_localization f U (U.2.preimage f) r hs
  refine ⟨r, hr, hclosed, ?_⟩
  have hker : r - 1 ∈ RingHom.ker (((zeroInclusion q).app U.1).hom) := by
    rw [← Scheme.Hom.ker_apply (zeroInclusion q) U, zeroInclusion_ideal q U]
    exact hr
  have hr₁ : ((zeroInclusion q).app U.1).hom r = 1 := by
    have hh : ((zeroInclusion q).app U.1).hom (r - 1) = 0 := hker
    exact sub_eq_zero.mp (by simpa only [map_sub, map_one] using hh)
  have hpre : zeroInclusion q ⁻¹ᵁ Z.basicOpen r = zeroInclusion q ⁻¹ᵁ U.1 := by
    rw [Scheme.preimage_basicOpen, hr₁, Scheme.basicOpen_one]
  intro z hz
  change z ∈ zeroInclusion q ⁻¹ᵁ Z.basicOpen r
  rw [hpre]
  exact hz

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodCharts
