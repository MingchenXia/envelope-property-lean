import EnvelopeProperty.AlgGeom.CyclicSectionSNCStalkBranches
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverFrames
import EnvelopeProperty.AlgGeom.SchemeLineZeroIdealNativeFrameOrders
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading
import EnvelopeProperty.AlgGeom.SchemeCommonAffineLineFrames
import EnvelopeProperty.Char0.RoundedSncIdealSheaf

/-! # The original line-section coefficient has its actual stalk unit factor

The original section's whole zero ideal and its original SNC presentation
derive the literal coefficient factorization in the actual smooth stalk.
No affine-ring domain or scalar-factorization certificate is assumed.
-/

noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionSNCOriginalCoefficient
open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules Ideal
open CanonicalGeometry CyclicSectionGlobalCoverFrames SchemePulledPowerFrames
open scoped BigOperators Classical
variable {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
  (n : ℕ) (s : unitObj X ⟶ bundleTensorPower L n)
local notation "J₀" => LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L n)
  (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) s

/-- The SAME original coefficient in its induced power frame generates the ENTIRE original zero ideal. -/
theorem zeroIdeal_ideal_eq_sectionCoefficient (U : X.affineOpens)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    (J₀).ideal U = span {U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)} := by
  simpa only [sectionCoefficient] using
    SchemeLineZeroIdealNativeFrameOrders.zeroIdeal_ideal_of_pullback_frame
      (bundleTensorPower L n) (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
      s U (pullbackPowerFrame U.1.ι e n)

private theorem originalIdeal_ideal_eq_monomial {F : Scheme.DivisorFamily X}
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) :
    (J₀).ideal U = span {∏ i, v (c i) ^ a i.1} := by
  have h1 := Char0.RoundedSncIdealSheaf.product_ideal a 1 x₀ U v c hcomp habsent
  have hprod : Char0.RoundedSncIdealSheaf.product F a 1 = J₀ := by
    simpa only [Char0.RoundedSncIdealSheaf.product, one_mul, Nat.floor_natCast] using hJF.symm
  simpa only [hprod, one_mul, Nat.floor_natCast] using h1

/-- The literal original coefficient germ is associated to the SAME original multiplicity monomial. -/
theorem sectionCoefficient_germ_associated {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X}
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) (y : X) (hy : y ∈ U.1) :
    Associated (X.presheaf.germ U.1 y hy (U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)))
      (∏ i, (X.presheaf.germ U.1 y hy (v (c i))) ^ a i.1) := by
  have := isRegularLocalRing_stalk f y
  have hI : span {U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)} =
      span {∏ i, v (c i) ^ a i.1} :=
    (zeroIdeal_ideal_eq_sectionCoefficient L hL n s U e).symm.trans
      (originalIdeal_ideal_eq_monomial L hL n s a hJF x₀ U v c hcomp habsent)
  apply Ideal.span_singleton_eq_span_singleton.mp
  have heq := congrArg (fun I : Ideal Γ(X, U.1) =>
    I.map (X.presheaf.germ U.1 y hy).hom) hI
  simpa only [Ideal.map_span, Set.image_singleton, map_prod, map_pow] using heq

/-- An actual unit in the SAME original stalk is DERIVED from the original section and chart data. -/
theorem exists_unit_sectionCoefficient_germ {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X}
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) (y : X) (hy : y ∈ U.1) :
    ∃ u : (X.presheaf.stalk y)ˣ,
      X.presheaf.germ U.1 y hy (U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)) =
        (u : X.presheaf.stalk y) * ∏ i, (X.presheaf.germ U.1 y hy (v (c i))) ^ a i.1 := by
  obtain ⟨u, hu⟩ :=
    (sectionCoefficient_germ_associated L hL n s f a hJF x₀ U v c hcomp habsent e y hy).symm
  exact ⟨u, hu.symm.trans (mul_comm _ _)⟩

/-- The SAME original coefficient germ is nonzero, reusing the proved actual SNC stalk branches. -/
theorem sectionCoefficient_germ_ne_zero {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) (y : X) (hy : y ∈ U.1) :
    X.presheaf.germ U.1 y hy (U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)) ≠ 0 := by
  have := isRegularLocalRing_stalk f y
  obtain ⟨u, hu⟩ := exists_unit_sectionCoefficient_germ L hL n s f a hJF x₀ U v c hcomp habsent e y hy
  have hbranches := CyclicSectionSNCStalkBranches.stalk_branches f hF U
    (fun i : {i : F.ι // x₀ ∈ (F.component i).support} => i.1) Subtype.val_injective
    (fun i => v (c i)) hcomp y hy
  rw [hu]
  exact mul_ne_zero u.ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hbranches.2.2.2 i))

/-- Original invertibility INTERNALLY produces a real common affine frame with the actual stalk factorization. -/
theorem exists_affine_stalk_factorization {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (V : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, V.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal V = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap V.1.ι = ⊤)
    (y : X) (hy : y ∈ V.1) :
    ∃ (U : X.affineOpens) (hyU : y ∈ U.1), U.1 ≤ V.1 ∧
      ∃ e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme,
        ∃ u : (X.presheaf.stalk y)ˣ,
          X.presheaf.germ U.1 y hyU (U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)) =
            (u : X.presheaf.stalk y) * ∏ i, (X.presheaf.germ V.1 y hy (v (c i))) ^ a i.1 ∧
          X.presheaf.germ U.1 y hyU (U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)) ≠ 0 := by
  obtain ⟨U, hyU, hUV, ⟨e⟩, _⟩ := SchemeCommonAffineLineFrames.exists_in_open L (unitObj X)
    hL isInvertible_unit y V.1 hy
  let w : Fin m → Γ(X, U.1) := fun j => X.presheaf.map (homOfLE hUV).op (v j)
  have hcompU (i : {i : F.ι // x₀ ∈ (F.component i).support}) :
      (F.component i.1).ideal U = span {w (c i)} := by
    change (F.component i.1).ideal U = span {(X.presheaf.map (homOfLE hUV).op).hom (v (c i))}
    rw [← (F.component i.1).map_ideal hUV, hcomp i, Ideal.map_span, Set.image_singleton]
    rfl
  have habsentU (i : F.ι) (hi : x₀ ∉ (F.component i).support) :
      (F.component i).comap U.1.ι = ⊤ := by
    rw [← X.homOfLE_ι hUV, Scheme.IdealSheafData.comap_comp, habsent i hi,
      Scheme.IdealSheafData.comap_top]
  obtain ⟨u, hu⟩ := exists_unit_sectionCoefficient_germ L hL n s f a hJF x₀ U w c hcompU habsentU e y hyU
  have hne := sectionCoefficient_germ_ne_zero L hL n s f hF a hJF x₀ U w c hcompU habsentU e y hyU
  refine ⟨U, hyU, hUV, e, u, ?_, hne⟩
  simpa only [w, TopCat.Presheaf.germ_res_apply] using hu

end EnvelopeProperty.CyclicSectionSNCOriginalCoefficient
