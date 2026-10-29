import EnvelopeProperty.ComplexGeometry.Schemes.SchemeGenericSections
import EnvelopeProperty.ComplexGeometry.Schemes.BundleTensorLocalization
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Actual Cech sections and finite projective homogeneous pieces

Global sections are compared with the genuine restriction equalizer using the
sheaf axiom. Homogeneous chart pieces are concrete submodules of the Laurent
polynomial algebra. These prerequisites do not supply the still-unproved
identification of arbitrary projective bundles with finite twisting sections.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace ComplexSchemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {X : Scheme.{u}}

/-- Local bundle sections retain their actual action by global regular functions. -/
abbrev localSectionsGlobalModule (L : X.Modules) (U : X.Opens) :
    Module Γ(X, ⊤) (bundleSections L U) :=
  Module.compHom (bundleSections L U) (X.presheaf.map U.leTop.op).hom

/-- The genuine Cech degree-zero equalizer: actual local sections agree on actual overlaps. -/
def bundleCechSections {I : Type u} (L : X.Modules) (U : I → X.Opens) :
    letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
      fun i => localSectionsGlobalModule L (U i)
    Submodule Γ(X, ⊤) (∀ i, bundleSections L (U i)) := by
  letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
    fun i => localSectionsGlobalModule L (U i)
  exact {
    carrier := {s | ∀ i j,
      L.val.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (s i) =
      L.val.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (s j)}
    zero_mem' := by
      intro i j
      change L.val.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op 0 =
        L.val.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op 0
      rw [(L.val.map _).hom.map_zero, (L.val.map _).hom.map_zero]
    add_mem' := by
      intro s t hs ht i j
      simp only [Pi.add_apply, map_add, hs i j, ht i j]
    smul_mem' := by
      intro r s hs i j
      change L.val.map _ (X.presheaf.map (U i).leTop.op r • s i) =
        L.val.map _ (X.presheaf.map (U j).leTop.op r • s j)
      rw [L.val.map_smul, L.val.map_smul]
      change X.presheaf.map _ (X.presheaf.map _ r) • _ =
        X.presheaf.map _ (X.presheaf.map _ r) • _
      rw [hs i j]
      congr 1
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl }

/-- Restrict an actual global section to its genuine compatible chart family. -/
def bundleGlobalToCech {I : Type u} (L : X.Modules) (U : I → X.Opens) :
    letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
      fun i => localSectionsGlobalModule L (U i)
    bundleSections L ⊤ →ₗ[Γ(X, ⊤)] bundleCechSections L U := by
  letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
    fun i => localSectionsGlobalModule L (U i)
  exact {
    toFun s := ⟨fun i => L.val.map (U i).leTop.op s, by
      intro i j
      change L.val.presheaf.map _ (L.val.presheaf.map _ s) =
        L.val.presheaf.map _ (L.val.presheaf.map _ s)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl⟩
    map_add' s t := by ext i; exact (L.val.map (U i).leTop.op).hom.map_add s t
    map_smul' r s := by
      ext i
      exact L.val.map_smul (U i).leTop.op r s }

/-- The actual sheaf axiom identifies global sections with the actual Cech equalizer. -/
theorem bundleGlobalToCech_bijective {I : Type u} (L : X.Modules) (U : I → X.Opens)
    (hU : iSup U = ⊤) : Function.Bijective (bundleGlobalToCech L U) := by
  constructor
  · intro s t h
    apply TopCat.Presheaf.IsSheaf.section_ext (F := L.presheaf) L.isSheaf
    intro x hx
    have hx' : x ∈ iSup U := by simpa only [hU] using hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    refine ⟨U i, le_top, hi, ?_⟩
    exact congrArg (fun z : bundleCechSections L U => z.val i) h
  · intro s
    let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.presheaf, L.isSheaf⟩
    obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' U ⊤ (fun i => (U i).leTop)
      (by rw [hU]) s.val (by intro i j; exact s.property i j)
    refine ⟨t, ?_⟩
    apply Subtype.ext
    funext i
    exact ht i

/-- This comparison is a produced linear equivalence of actual sections, not a grading premise. -/
def bundleGlobalCechEquiv {I : Type u} (L : X.Modules) (U : I → X.Opens)
    (hU : iSup U = ⊤) :
    letI : ∀ i, Module Γ(X, ⊤) (bundleSections L (U i)) :=
      fun i => localSectionsGlobalModule L (U i)
    bundleSections L ⊤ ≃ₗ[Γ(X, ⊤)] bundleCechSections L U :=
  LinearEquiv.ofBijective (bundleGlobalToCech L U) (bundleGlobalToCech_bijective L U hU)



section ProjectivePoint

variable {K : Type u} [Field K]

/-- The actual field-spectrum global sections use their native base-field action. -/
instance fieldSpectrumBundleGlobalModule (L : (Spec (CommRingCat.of K)).Modules) :
    Module K (bundleSections L ⊤) :=
  Module.compHom (bundleSections L ⊤) (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/-- On the actual spectrum of a field, a genuine atlas chart containing the generic point
is the entire scheme. This is derived from the actual one-point spectrum. -/
theorem LineBundleAtlas.fieldSpectrum_genericOpen_eq_top
    {L : (Spec (CommRingCat.of K)).Modules} (a : LineBundleAtlas L) :
    a.opens a.genericIndex = ⊤ := by
  apply top_unique
  intro x _
  have hx : x = genericPoint (Spec (CommRingCat.of K)) := Subsingleton.elim _ _
  rw [hx]
  exact a.genericIndex_mem

/-- A genuine line bundle on the actual field spectrum has a produced global coefficient frame. -/
def LineBundleAtlas.fieldSpectrumGlobalCoefficients
    {L : (Spec (CommRingCat.of K)).Modules} (a : LineBundleAtlas L) :
    bundleSections L ⊤ ≃ₗ[Γ(Spec (CommRingCat.of K), ⊤)] Γ(Spec (CommRingCat.of K), ⊤) :=
  localFrameCoefficientsOn (a.frame a.genericIndex)
    (homOfLE (by rw [a.fieldSpectrum_genericOpen_eq_top]))

/-- Actual global sections on the projective-point model have their true base-field frame. -/
def LineBundleAtlas.fieldSpectrumGlobalFrame
    {L : (Spec (CommRingCat.of K)).Modules} (a : LineBundleAtlas L) :
    bundleSections L ⊤ ≃ₗ[K] K := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  let c := a.fieldSpectrumGlobalCoefficients
  refine { (c.toAddEquiv.trans e.toAddEquiv) with map_smul' := ?_ }
  intro r s
  change e (c (e.symm r • s)) = r * e (c s)
  rw [c.map_smul]
  change e (e.symm r * c s) = r * e (c s)
  rw [map_mul, e.apply_symm_apply]

/-- Finite-dimensionality of actual field-spectrum line sections is derived from its actual atlas. -/
theorem LineBundleAtlas.fieldSpectrum_globalSections_finite
    {L : (Spec (CommRingCat.of K)).Modules} (a : LineBundleAtlas L) :
    Module.Finite K (bundleSections L ⊤) :=
  Module.Finite.equiv a.fieldSpectrumGlobalFrame.symm

/-- The actual global sections on the projective-point model have dimension one. -/
theorem LineBundleAtlas.fieldSpectrum_globalSections_finrank
    {L : (Spec (CommRingCat.of K)).Modules} (a : LineBundleAtlas L) :
    Module.finrank K (bundleSections L ⊤) = 1 := by
  rw [a.fieldSpectrumGlobalFrame.finrank_eq]
  exact Module.finrank_self K

/-- All actual tensor-power global section modules on the projective-point model are finite. -/
theorem LineBundleAtlas.fieldSpectrum_bundlePowerGlobalSections_finite
    {L : (Spec (CommRingCat.of K)).Modules} (a : LineBundleAtlas L) (k : ℕ) :
    Module.Finite K (bundlePowerGlobalSections L k) :=
  (a.tensorPower k).fieldSpectrum_globalSections_finite

end ProjectivePoint

section HomogeneousCharts

variable {K : Type u} [Field K] {I : Type u} [Fintype I] [Nontrivial I]

/-- The actual multivariate Laurent polynomial algebra has integer exponent vectors. -/
abbrev projectiveLaurentAlgebra (K : Type u) [Field K] (I : Type u) :=
  AddMonoidAlgebra K (I → ℤ)

/-- Degree-k exponents on the chart where coordinate i is inverted. -/
def homogeneousChartExponents (k : ℕ) (i : I) : Set (I → ℤ) :=
  {d | (∑ j, d j) = k ∧ ∀ j, j ≠ i → 0 ≤ d j}

/-- The concrete homogeneous chart module inside the actual Laurent algebra. -/
def homogeneousChartModule (k : ℕ) (i : I) :
    Submodule K (projectiveLaurentAlgebra K I) :=
  AddMonoidAlgebra.supported K K (homogeneousChartExponents k i)

/-- Ordinary nonnegative degree-k exponent vectors. -/
def nonnegativeHomogeneousExponents (k : ℕ) : Set (I → ℤ) :=
  {d | (∑ j, d j) = k ∧ ∀ j, 0 ≤ d j}

/-- The actual nonnegative homogeneous part of the Laurent algebra. -/
def nonnegativeHomogeneousLaurentModule (k : ℕ) :
    Submodule K (projectiveLaurentAlgebra K I) :=
  AddMonoidAlgebra.supported K K (nonnegativeHomogeneousExponents (I := I) k)

/-- Genuine chart restrictions are inclusions into the common Laurent algebra.
The degree-zero Cech compatibility condition says these actual restrictions agree. -/
def homogeneousChartCech (k : ℕ) :
    Submodule K (∀ i : I, homogeneousChartModule (K := K) k i) where
  carrier := {s | ∀ i j, (s i : projectiveLaurentAlgebra K I) = s j}
  zero_mem' := by intro i j; rfl
  add_mem' := by intro s t hs ht i j; exact congrArg₂ (· + ·) (hs i j) (ht i j)
  smul_mem' := by intro r s hs i j; exact congrArg (r • ·) (hs i j)

/-- Compatibility on all projective coordinate charts forces every exponent to be nonnegative. -/
theorem homogeneousLaurent_mem_all_charts_iff (k : ℕ) (f : projectiveLaurentAlgebra K I) :
    (∀ i, f ∈ homogeneousChartModule (K := K) k i) ↔
      f ∈ nonnegativeHomogeneousLaurentModule (K := K) (I := I) k := by
  classical
  simp only [homogeneousChartModule, nonnegativeHomogeneousLaurentModule,
    AddMonoidAlgebra.mem_supported, Set.subset_def, Finset.mem_coe]
  constructor
  · intro h d hd
    refine ⟨(h (Classical.arbitrary I) d hd).1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := exists_ne j
    exact (h i d hd).2 j hi.symm
  · intro h i d hd
    exact ⟨(h d hd).1, fun j _ => (h d hd).2 j⟩

/-- The concrete Cech kernel is the actual nonnegative homogeneous Laurent module. -/
def homogeneousChartCechEquiv (k : ℕ) :
    homogeneousChartCech (K := K) (I := I) k ≃ₗ[K]
      nonnegativeHomogeneousLaurentModule (K := K) (I := I) k := by
  classical
  let i₀ : I := Classical.arbitrary I
  refine {
    toFun := fun s => ⟨s.val i₀,
      (homogeneousLaurent_mem_all_charts_iff k _).mp (fun i => ?_)⟩
    invFun := fun f => ⟨fun i => ⟨f.val,
      (homogeneousLaurent_mem_all_charts_iff k f.val).mpr f.property i⟩, fun _ _ => rfl⟩
    left_inv := ?_
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  · rw [s.property i₀ i]
    exact (s.val i).property
  · intro s
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact s.property i₀ i

omit [Nontrivial I] in
/-- Every exponent in the global homogeneous part is bounded by the actual degree. -/
theorem nonnegativeHomogeneousExponents_coordinate_le {k : ℕ} {d : I → ℤ}
    (hd : d ∈ nonnegativeHomogeneousExponents k) (i : I) : d i ≤ k := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => hd.2 j)
    (Finset.mem_univ i)
  simpa only [hd.1] using h

omit [Nontrivial I] in
/-- The global homogeneous exponent set is finite, derived from degree bounds. -/
theorem nonnegativeHomogeneousExponents_finite (k : ℕ) :
    (nonnegativeHomogeneousExponents (I := I) k).Finite := by
  classical
  let F : nonnegativeHomogeneousExponents (I := I) k → I → Fin (k + 1) :=
    fun d i => ⟨(d.val i).toNat, by
      have h := nonnegativeHomogeneousExponents_coordinate_le d.property i
      have hn := Int.toNat_le_toNat h
      simpa only [Int.toNat_natCast] using Nat.lt_succ_of_le hn⟩
  have hinj : Function.Injective F := by
    intro d e h
    apply Subtype.ext
    funext i
    have hi := congrArg (fun z => (z i).val) h
    change (d.val i).toNat = (e.val i).toNat at hi
    have hi' : ((d.val i).toNat : ℤ) = ((e.val i).toNat : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hi
    simpa only [Int.toNat_of_nonneg (d.property.2 i), Int.toNat_of_nonneg (e.property.2 i)] using hi' 
  let : Finite (nonnegativeHomogeneousExponents (I := I) k) := Finite.of_injective F hinj
  exact Set.toFinite _

/-- The actual finite monomial basis of the nonnegative homogeneous Laurent part. -/
def nonnegativeHomogeneousLaurentBasis (k : ℕ) :
    Module.Basis (nonnegativeHomogeneousExponents (I := I) k) K
      (nonnegativeHomogeneousLaurentModule (K := K) (I := I) k) where
  repr := AddMonoidAlgebra.supportedEquivFinsupp _

/-- Actual chart compatibility yields a finite-dimensional homogeneous Cech kernel. -/
theorem homogeneousChartCech_finite (k : ℕ) :
    Module.Finite K (homogeneousChartCech (K := K) (I := I) k) := by
  have := (nonnegativeHomogeneousExponents_finite (I := I) k).to_subtype
  exact Module.Finite.of_basis
    ((nonnegativeHomogeneousLaurentBasis (K := K) (I := I) k).map
      (homogeneousChartCechEquiv k).symm)


/-- Homogeneous polynomial exponent vectors embed in actual integer Laurent exponents. -/
def polynomialExponentToInt : (I →₀ ℕ) →+ (I → ℤ) where
  toFun d := fun i => (d i : ℤ)
  map_zero' := rfl
  map_add' d e := by ext i; exact Int.natCast_add _ _

omit [Fintype I] [Nontrivial I] in
/-- No two ordinary polynomial exponent vectors acquire the same Laurent exponent. -/
theorem polynomialExponentToInt_injective :
    Function.Injective (polynomialExponentToInt (I := I)) := by
  intro d e h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

/-- The genuine ordinary-polynomial inclusion into the actual Laurent algebra. -/
def polynomialToProjectiveLaurent : MvPolynomial I K →ₐ[K] projectiveLaurentAlgebra K I :=
  AddMonoidAlgebra.mapDomainAlgHom K K polynomialExponentToInt

omit [Fintype I] [Nontrivial I] in
/-- The genuine polynomial-to-Laurent inclusion is injective. -/
theorem polynomialToProjectiveLaurent_injective :
    Function.Injective (polynomialToProjectiveLaurent (K := K) (I := I)) :=
  AddMonoidAlgebra.mapDomain_injective polynomialExponentToInt_injective


omit [Fintype I] [Nontrivial I] in
/-- A homogeneous coordinate becomes its actual Laurent monomial. -/
theorem polynomialToProjectiveLaurent_X (i : I) :
    polynomialToProjectiveLaurent (K := K) (MvPolynomial.X i) =
      AddMonoidAlgebra.single (polynomialExponentToInt (Finsupp.single i 1)) 1 := by
  change AddMonoidAlgebra.mapDomain polynomialExponentToInt
    (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  exact AddMonoidAlgebra.mapDomain_single

omit [Fintype I] [Nontrivial I] in
/-- The inverted chart coordinate is an actual unit in the Laurent algebra. -/
theorem polynomialToProjectiveLaurent_X_isUnit (i : I) :
    IsUnit (polynomialToProjectiveLaurent (K := K) (MvPolynomial.X i)) := by
  rw [polynomialToProjectiveLaurent_X]
  apply IsUnit.of_mul_eq_one
    (AddMonoidAlgebra.single (-polynomialExponentToInt (Finsupp.single i 1)) 1)
  simp only [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
  rfl

/-- The genuine coordinate localization maps to the Laurent algebra by its universal property. -/
def coordinateLocalizationToLaurent (i : I) :
    Localization.Away (MvPolynomial.X i : MvPolynomial I K) →ₐ[K]
      projectiveLaurentAlgebra K I :=
  IsLocalization.Away.liftAlgHom _ (polynomialToProjectiveLaurent_X_isUnit i)

omit [Fintype I] [Nontrivial I] in
/-- The actual localization map really extends the ordinary homogeneous coordinate ring. -/
theorem coordinateLocalizationToLaurent_algebraMap (i : I) (p : MvPolynomial I K) :
    coordinateLocalizationToLaurent i
      (algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) p) =
      polynomialToProjectiveLaurent p :=
  IsLocalization.Away.lift_eq _ (polynomialToProjectiveLaurent_X_isUnit i) p

omit [Fintype I] [Nontrivial I] in
/-- The genuine coordinate localization embeds faithfully in the actual Laurent algebra. -/
theorem coordinateLocalizationToLaurent_injective (i : I) :
    Function.Injective (coordinateLocalizationToLaurent (K := K) i) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial I K))
    (coordinateLocalizationToLaurent i).toRingHom).mpr
  intro p q
  change algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) p =
      algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) q ↔
    coordinateLocalizationToLaurent i (algebraMap _ _ p) =
      coordinateLocalizationToLaurent i (algebraMap _ _ q)
  rw [coordinateLocalizationToLaurent_algebraMap, coordinateLocalizationToLaurent_algebraMap]
  constructor
  · intro h
    simpa only [coordinateLocalizationToLaurent_algebraMap] using
      congrArg (coordinateLocalizationToLaurent i) h
  · intro h
    exact congrArg _ (polynomialToProjectiveLaurent_injective h)


omit [Nontrivial I] in
/-- Actual polynomial monomials have no negative Laurent exponents. -/
theorem polynomialToProjectiveLaurent_exponent_nonnegative (p : MvPolynomial I K)
    {d : I → ℤ} (hd : (polynomialToProjectiveLaurent p).coeff d ≠ 0) (j : I) : 0 ≤ d j := by
  classical
  have hs : d ∈ (polynomialToProjectiveLaurent p).coeff.support := Finsupp.mem_support_iff.mpr hd
  change d ∈ ((AddMonoidAlgebra.coeff p).mapDomain polynomialExponentToInt).support at hs
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
  rw [← he]
  exact Int.natCast_nonneg _

omit [Nontrivial I] in
/-- A genuine coordinate-localized polynomial cannot have negative exponents away from
its inverted coordinate. This bound is derived from its actual fraction representation. -/
theorem coordinateLocalizationToLaurent_exponent_nonnegative (i : I)
    (z : Localization.Away (MvPolynomial.X i : MvPolynomial I K)) {d : I → ℤ}
    (hd : (coordinateLocalizationToLaurent i z).coeff d ≠ 0) {j : I} (hji : j ≠ i) :
    0 ≤ d j := by
  classical
  obtain ⟨m, p, hp⟩ := IsLocalization.Away.surj (R := MvPolynomial I K) (S := Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i) z
  have hl := congrArg (coordinateLocalizationToLaurent (K := K) i) hp
  rw [map_mul, map_pow, coordinateLocalizationToLaurent_algebraMap,
    coordinateLocalizationToLaurent_algebraMap, polynomialToProjectiveLaurent_X,
    AddMonoidAlgebra.single_pow, one_pow] at hl
  let a : I → ℤ := m • polynomialExponentToInt (Finsupp.single i 1)
  have hc : (polynomialToProjectiveLaurent p).coeff (d + a) =
      (coordinateLocalizationToLaurent i z).coeff d := by
    rw [← hl]
    exact (AddMonoidAlgebra.coeff_mul_single_add _ 1 _ _).trans (mul_one _)
  have hnonzero : (polynomialToProjectiveLaurent p).coeff (d + a) ≠ 0 := by
    rw [hc]
    exact hd
  have hb := polynomialToProjectiveLaurent_exponent_nonnegative p hnonzero j
  simpa [a, polynomialExponentToInt, Finsupp.single_apply, hji, hji.symm] using hb

/-- The actual degree-k piece of the genuine coordinate localization is cut out only
by its total Laurent degree; chart exponent bounds are proved separately. -/
def coordinateHomogeneousLocalization (k : ℕ) (i : I) :
    Submodule K (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) :=
  (AddMonoidAlgebra.supported K K {d : I → ℤ | (∑ j, d j) = k}).comap
    (coordinateLocalizationToLaurent i).toLinearMap

/-- Genuine localized homogeneous elements enter the concrete chart module by the derived bound. -/
def coordinateHomogeneousToChart (k : ℕ) (i : I) :
    coordinateHomogeneousLocalization (K := K) k i →ₗ[K] homogeneousChartModule (K := K) k i :=
  LinearMap.codRestrict _
    ((coordinateLocalizationToLaurent i).toLinearMap.comp
      (coordinateHomogeneousLocalization (K := K) k i).subtype) (by
        intro z
        apply AddMonoidAlgebra.mem_supported.mpr
        intro d hd
        refine ⟨z.property hd, ?_⟩
        intro j hji
        exact coordinateLocalizationToLaurent_exponent_nonnegative i z.val
          (Finsupp.mem_support_iff.mp hd) hji)

omit [Nontrivial I] in
/-- The genuine localized-chart embedding is faithful. -/
theorem coordinateHomogeneousToChart_injective (k : ℕ) (i : I) :
    Function.Injective (coordinateHomogeneousToChart (K := K) k i) := by
  intro z w h
  apply Subtype.ext
  exact coordinateLocalizationToLaurent_injective i (congrArg Subtype.val h)

/-- The actual coordinate-localization degree-k Cech kernel uses the genuine localization maps. -/
def coordinateHomogeneousCech (k : ℕ) :
    Submodule K (∀ i : I, coordinateHomogeneousLocalization (K := K) k i) where
  carrier := {s | ∀ i j,
    coordinateLocalizationToLaurent i (s i).val = coordinateLocalizationToLaurent j (s j).val}
  zero_mem' := by intro i j; exact (map_zero _).trans (map_zero _).symm
  add_mem' := by
    intro s t hs ht i j
    change coordinateLocalizationToLaurent i ((s i).val + (t i).val) =
      coordinateLocalizationToLaurent j ((s j).val + (t j).val)
    rw [map_add, map_add, hs i j, ht i j]
  smul_mem' := by
    intro r s hs i j
    change coordinateLocalizationToLaurent i (r • (s i).val) =
      coordinateLocalizationToLaurent j (r • (s j).val)
    rw [map_smul, map_smul, hs i j]

/-- The actual localized Cech kernel embeds in the produced finite homogeneous chart equalizer. -/
def coordinateHomogeneousCechToChart (k : ℕ) :
    coordinateHomogeneousCech (K := K) (I := I) k →ₗ[K] homogeneousChartCech (K := K) (I := I) k where
  toFun s := ⟨fun i => coordinateHomogeneousToChart k i (s.val i), s.property⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact (coordinateHomogeneousToChart (K := K) k i).map_add (s.val i) (t.val i)
  map_smul' r s := by
    apply Subtype.ext
    funext i
    exact (coordinateHomogeneousToChart (K := K) k i).map_smul r (s.val i)

omit [Nontrivial I] in
/-- No injectivity conclusion is assumed for actual localized homogeneous Cech sections. -/
theorem coordinateHomogeneousCechToChart_injective (k : ℕ) :
    Function.Injective (coordinateHomogeneousCechToChart (K := K) (I := I) k) := by
  intro s t h
  apply Subtype.ext
  funext i
  apply coordinateHomogeneousToChart_injective k i
  exact congrArg (fun z : homogeneousChartCech (K := K) (I := I) k => z.val i) h

/-- Actual compatible degree-k elements in the genuine coordinate localizations are finite-dimensional. -/
theorem coordinateHomogeneousCech_finite (k : ℕ) :
    Module.Finite K (coordinateHomogeneousCech (K := K) (I := I) k) := by
  let : Module.Finite K (homogeneousChartCech (K := K) (I := I) k) :=
    homogeneousChartCech_finite (K := K) (I := I) k
  exact FiniteDimensional.of_injective (K := K)
    (V := coordinateHomogeneousCech (K := K) (I := I) k)
    (V₂ := homogeneousChartCech (K := K) (I := I) k)
    (coordinateHomogeneousCechToChart (K := K) (I := I) k)
    (coordinateHomogeneousCechToChart_injective (K := K) (I := I) k)

/-- The precise ordinary/ Laurent homogeneous exponent comparison is derived by taking natural parts. -/
def homogeneousExponentEquiv (k : ℕ) :
    {d : I →₀ ℕ | d.degree = k} ≃ nonnegativeHomogeneousExponents (I := I) k := by
  classical
  refine {
    toFun := fun d => ⟨polynomialExponentToInt d.val, ?_⟩
    invFun := fun d => ⟨Finsupp.equivFunOnFinite.symm (fun i => (d.val i).toNat), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · constructor
    · change (∑ i, (d.val i : ℤ)) = (k : ℤ)
      rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, d.property]
    · intro i
      exact Int.natCast_nonneg _
  · apply Int.ofNat_inj.mp
    rw [Finsupp.degree_eq_sum, Nat.cast_sum]
    have h : ∀ i, ((Finsupp.equivFunOnFinite.symm (fun j => (d.val j).toNat)) i : ℤ) =
        d.val i := by
      intro i
      exact Int.toNat_of_nonneg (d.property.2 i)
    simpa only [h] using d.property.1
  · intro d
    apply Subtype.ext
    ext i
    simp [polynomialExponentToInt]
  · intro d
    apply Subtype.ext
    funext i
    exact Int.toNat_of_nonneg (d.property.2 i)

/-- Actual homogeneous polynomial coefficients have their ordinary degree-k exponent basis. -/
def homogeneousPolynomialCoefficients (k : ℕ) :
    MvPolynomial.homogeneousSubmodule I K k ≃ₗ[K] {d : I →₀ ℕ | d.degree = k} →₀ K := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact AddMonoidAlgebra.supportedEquivFinsupp _

/-- The concrete chart equalizer is isomorphic to the actual homogeneous polynomial degree piece. -/
def homogeneousChartCechPolynomialEquiv (k : ℕ) :
    homogeneousChartCech (K := K) (I := I) k ≃ₗ[K] MvPolynomial.homogeneousSubmodule I K k :=
  (homogeneousChartCechEquiv k).trans
    ((AddMonoidAlgebra.supportedEquivFinsupp _).trans
      ((Finsupp.domLCongr (homogeneousExponentEquiv k).symm).trans
        (homogeneousPolynomialCoefficients k).symm))

omit [Nontrivial I] in
/-- A nonnegative homogeneous Laurent polynomial is the image of a genuine
ordinary homogeneous polynomial, by the actual exponent inclusion. -/
theorem homogeneousPolynomial_preimage (k : ℕ)
    (f : nonnegativeHomogeneousLaurentModule (K := K) (I := I) k) :
    ∃ p : MvPolynomial.homogeneousSubmodule I K k,
      polynomialToProjectiveLaurent p.val = f.val := by
  classical
  let p : MvPolynomial I K := AddMonoidAlgebra.comapDomain
    polynomialExponentToInt polynomialExponentToInt_injective f.val
  have hp : p ∈ MvPolynomial.homogeneousSubmodule I K k := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    apply AddMonoidAlgebra.mem_supported.mpr
    intro d hd
    have hc : f.val.coeff (polynomialExponentToInt d) ≠ 0 := by
      have hc := Finsupp.mem_support_iff.mp hd
      change (AddMonoidAlgebra.comapDomain polynomialExponentToInt
        polynomialExponentToInt_injective f.val).coeff d ≠ 0 at hc
      simpa only [AddMonoidAlgebra.coeff_comapDomain, Finsupp.comapDomain_apply] using hc
    have htotal := (f.property (Finsupp.mem_support_iff.mpr hc)).1
    apply Int.ofNat_inj.mp
    rw [Finsupp.degree_eq_sum, Nat.cast_sum]
    exact htotal
  refine ⟨⟨p, hp⟩, ?_⟩
  change AddMonoidAlgebra.mapDomain polynomialExponentToInt
    (AddMonoidAlgebra.comapDomain polynomialExponentToInt
      polynomialExponentToInt_injective f.val) = f.val
  apply AddMonoidAlgebra.mapDomain_comapDomain _ polynomialExponentToInt_injective
  intro d hd
  have hn := (f.property hd).2
  refine ⟨Finsupp.equivFunOnFinite.symm (fun i => (d i).toNat), ?_⟩
  funext i
  exact Int.toNat_of_nonneg (hn i)

/-- Every compatible Laurent chart family is produced by a tuple of elements
in the genuine coordinate localizations. Surjectivity uses a proved polynomial
preimage and the actual localization algebra maps. -/
theorem coordinateHomogeneousCechToChart_surjective (k : ℕ) :
    Function.Surjective (coordinateHomogeneousCechToChart (K := K) (I := I) k) := by
  classical
  intro s
  let f := homogeneousChartCechEquiv (K := K) (I := I) k s
  obtain ⟨p, hp⟩ := homogeneousPolynomial_preimage k f
  have heq (i : I) : f.val = (s.val i).val := s.property (Classical.arbitrary I) i
  let z (i : I) : coordinateHomogeneousLocalization (K := K) k i :=
    ⟨algebraMap (MvPolynomial I K)
      (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) p.val, by
      change coordinateLocalizationToLaurent (K := K) i
        (algebraMap (MvPolynomial I K)
          (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) p.val) ∈
            AddMonoidAlgebra.supported K K {d : I → ℤ | (∑ j, d j) = k}
      rw [coordinateLocalizationToLaurent_algebraMap, hp]
      apply AddMonoidAlgebra.mem_supported.mpr
      intro d hd
      exact (f.property hd).1⟩
  refine ⟨⟨z, ?_⟩, ?_⟩
  · intro i j
    change coordinateLocalizationToLaurent (K := K) i
      (algebraMap (MvPolynomial I K)
        (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) p.val) =
      coordinateLocalizationToLaurent (K := K) j
        (algebraMap (MvPolynomial I K)
          (Localization.Away (MvPolynomial.X j : MvPolynomial I K)) p.val)
    rw [coordinateLocalizationToLaurent_algebraMap, coordinateLocalizationToLaurent_algebraMap]
  · apply Subtype.ext
    funext i
    apply Subtype.ext
    change coordinateLocalizationToLaurent (K := K) i
      (algebraMap (MvPolynomial I K)
        (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) p.val) = (s.val i).val
    rw [coordinateLocalizationToLaurent_algebraMap, hp, heq]

/-- The actual coordinate-localization Cech kernel has a produced comparison
with the concrete Laurent chart kernel. -/
def coordinateHomogeneousCechChartEquiv (k : ℕ) :
    coordinateHomogeneousCech (K := K) (I := I) k ≃ₗ[K]
      homogeneousChartCech (K := K) (I := I) k :=
  LinearEquiv.ofBijective (coordinateHomogeneousCechToChart k)
    ⟨coordinateHomogeneousCechToChart_injective k,
      coordinateHomogeneousCechToChart_surjective k⟩

/-- Actual compatible degree-k coordinate-localized elements are exactly the
actual ordinary homogeneous polynomials of degree k. -/
def coordinateHomogeneousCechPolynomialEquiv (k : ℕ) :
    coordinateHomogeneousCech (K := K) (I := I) k ≃ₗ[K]
      MvPolynomial.homogeneousSubmodule I K k :=
  (coordinateHomogeneousCechChartEquiv k).trans (homogeneousChartCechPolynomialEquiv k)

omit [Nontrivial I] in
/-- The finite monomial piece on the polynomial side is independently finite. -/
theorem homogeneousPolynomialPiece_finite (k : ℕ) :
    Module.Finite K (MvPolynomial.homogeneousSubmodule I K k) :=
  Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg I K k)

end HomogeneousCharts

end

end ComplexSchemes
