import EnvelopeProperty.AlgGeom.CyclicSectionSNCOriginalCoefficient

/-! # The original section coefficient has its actual affine unit factor

The original integral scheme and a genuine common affine frame derive a unit
of the SAME actual affine section ring, with the original branch functions
and original multiplicities. Whole-affine branch primality is not assumed.
-/

noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionSNCAffineOriginalCoefficient
open AlgebraicGeometry CategoryTheory Scheme.Modules Ideal
open CanonicalGeometry CyclicSectionGlobalCoverFrames
open scoped BigOperators Classical
variable {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
  (n : ℕ) (s : unitObj X ⟶ bundleTensorPower L n)
local notation "J₀" => LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L n)
  (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) s

/-- The original whole ideal presentation gives association in the SAME actual affine ring. -/
theorem sectionCoefficient_associated [IsIntegral X] {F : Scheme.DivisorFamily X}
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) (y : X) (hy : y ∈ U.1) :
    Associated (U.1.topIso.hom (sectionCoefficient L n s U.1.ι e))
      (∏ i, v (c i) ^ a i.1) := by
  let : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  apply Ideal.span_singleton_eq_span_singleton.mp
  calc
    span {U.1.topIso.hom (sectionCoefficient L n s U.1.ι e)} = (J₀).ideal U :=
      (CyclicSectionSNCOriginalCoefficient.zeroIdeal_ideal_eq_sectionCoefficient L hL n s U e).symm
    _ = span {∏ i, v (c i) ^ a i.1} := by
      have h1 := Char0.RoundedSncIdealSheaf.product_ideal a 1 x₀ U v c hcomp habsent
      have hprod : Char0.RoundedSncIdealSheaf.product F a 1 = J₀ := by
        simpa only [Char0.RoundedSncIdealSheaf.product, one_mul, Nat.floor_natCast] using hJF.symm
      simpa only [hprod, one_mul, Nat.floor_natCast] using h1

/-- An actual unit of the SAME affine section ring is derived from the original section and whole ideal. -/
theorem exists_unit_sectionCoefficient [IsIntegral X] {F : Scheme.DivisorFamily X}
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) (y : X) (hy : y ∈ U.1) :
    ∃ u : (Γ(X, U.1))ˣ,
      U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) =
        (u : Γ(X, U.1)) * ∏ i, v (c i) ^ a i.1 := by
  obtain ⟨u, hu⟩ := (sectionCoefficient_associated L hL n s a hJF x₀ U v c hcomp habsent e y hy).symm
  exact ⟨u, hu.symm.trans (mul_comm _ _)⟩

/-- Actual nonzero SNC germs force these SAME original affine branch sections to be nonzero. -/
theorem branch_sections_ne_zero {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)}) (y : X) (hy : y ∈ U.1) :
    ∀ i, v (c i) ≠ 0 := by
  have hbranches := CyclicSectionSNCStalkBranches.stalk_branches f hF U
    (fun i : {i : F.ι // x₀ ∈ (F.component i).support} => i.1) Subtype.val_injective
    (fun i => v (c i)) hcomp y hy
  intro i hi
  apply hbranches.2.2.2 i
  rw [hi, map_zero]

/-- Original geometry internally gives a real common affine frame and its actual affine unit factor. -/
theorem exists_affine_factorization [IsIntegral X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (V : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, V.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal V = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap V.1.ι = ⊤)
    (y : X) (hy : y ∈ V.1) :
    ∃ (U : X.affineOpens) (_hyU : y ∈ U.1) (hUV : U.1 ≤ V.1),
      ∃ e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme,
        ∃ u : (Γ(X, U.1))ˣ,
          (∀ i, X.presheaf.map (homOfLE hUV).op (v (c i)) ≠ 0) ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) =
            (u : Γ(X, U.1)) * ∏ i,
              (X.presheaf.map (homOfLE hUV).op (v (c i))) ^ a i.1 ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) ≠ 0 := by
  obtain ⟨U, hyU, hUV, e, _, _, _⟩ :=
    CyclicSectionSNCOriginalCoefficient.exists_affine_stalk_factorization L hL n s f hF
      a hJF x₀ V v c hcomp habsent y hy
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
  obtain ⟨u, hu⟩ := exists_unit_sectionCoefficient L hL n s a hJF x₀ U w c hcompU habsentU e y hyU
  have hf := branch_sections_ne_zero f hF x₀ U w c hcompU y hyU
  let : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  have hne : U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) ≠ 0 := by
    rw [hu]
    exact mul_ne_zero u.ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hf i))
  exact ⟨U, hyU, hUV, e, u, hf, hu, hne⟩

end EnvelopeProperty.CyclicSectionSNCAffineOriginalCoefficient
