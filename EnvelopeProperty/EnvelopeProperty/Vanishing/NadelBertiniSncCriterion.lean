import EnvelopeProperty.Vanishing.NadelBertiniSncTransverse
import EnvelopeProperty.Vanishing.NadelBertiniSncCartier

/-! # Actual all-closed-strata smooth Cartier criterion for enlarging SNC

The original new hypersurface and all its genuine original closed-stratum
restrictions are retained. The theorem proves the original appended family's
SNC coordinates rather than taking the desired SNC or SNC-with predicate as input.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncCriterion
open NadelBertiniSncStrata NadelBertiniSncLocal NadelBertiniSncTransverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- Actual all-stratum smooth-divisor intersections produce a COMMON original
coordinate system for the old family and new original hypersurface at each point. -/
theorem exists_transverse_coordinates [IsRegular X] (E : X.DivisorFamily) (hE : E.IsSnc)
    (H : X.IdealSheafData) (hH : IsSmoothDivisor H)
    (hcut : ∀ s : Finset E.ι, IsSmoothDivisor (H.comap (stratum E s).subschemeι))
    (x : X) (hxH : x ∈ H.support) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), IsRegularSystemOfParameters z ∧
      ∃ c : {i : E.ι // x ∈ (E.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (E.component i.1).stalkIdeal x = Ideal.span {z (c i)}) ∧
        ∃ j : Fin n, H.stalkIdeal x = Ideal.span {z j} ∧ ∀ i, c i ≠ j := by
  classical
  let : IsRegularLocalRing (X.presheaf.stalk x) := IsRegular.isRegularAt x
  obtain ⟨n, z, hz, c, hc, hcomp⟩ := hE.2 x
  obtain ⟨h, hm, _, he⟩ := hH.2 x hxH
  let s : Finset E.ι := Finset.univ.filter (fun i => x ∈ (E.component i).support)
  have hxs : x ∈ (stratum E s).support := by
    apply (mem_stratum_support_iff E s x).mpr
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hJ : (stratum E s).stalkIdeal x = Ideal.span (Set.range (z ∘ c)) := by
    rw [stratum, Scheme.IdealSheafData.stalkIdeal_iSup, Ideal.span_range_eq_iSup]
    apply le_antisymm
    · apply iSup_le
      intro i
      have hi : x ∈ (E.component i.1).support := (Finset.mem_filter.mp i.2).2
      rw [hcomp ⟨i.1, hi⟩]
      exact le_iSup (fun j => Ideal.span {(z ∘ c) j}) ⟨i.1, hi⟩
    · apply iSup_le
      intro i
      have hi : i.1 ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩
      change Ideal.span {z (c i)} ≤ _
      rw [← hcomp i]
      exact le_iSup (fun j : s => (E.component j.1).stalkIdeal x) ⟨i.1, hi⟩
  have htrans := equation_transverse_to_stratum E s H (hcut s) hxs hxH h he
  rw [hJ] at htrans
  obtain ⟨m, y, hy, d, hd, hdy⟩ := exists_common_regularParameters z hz c hc h hm htrans
  refine ⟨m, y, hy, (fun i => d (some i)), ?_, ?_, d none, ?_, ?_⟩
  · intro i j hij
    exact Option.some.inj (hd hij)
  · intro i
    rw [hcomp i, hdy (some i)]
    rfl
  · rw [he, hdy none]
    rfl
  · intro i hi
    have hbad : some i = none := hd hi
    cases hbad

/-- The original new hypersurface has SNC with the ORIGINAL family, internally
proved from actual smooth-divisor intersections with every actual closed stratum. -/
theorem hasSncWith_of_strata_smoothDivisor [IsRegular X]
    (E : X.DivisorFamily) (hE : E.IsSnc) (H : X.IdealSheafData)
    (hH : IsSmoothDivisor H)
    (hcut : ∀ s : Finset E.ι, IsSmoothDivisor (H.comap (stratum E s).subschemeι)) :
    E.HasSncWith H := by
  intro x hx
  obtain ⟨n, z, hz, c, hc, hcomp, j, hj, _⟩ :=
    exists_transverse_coordinates E hE H hH hcut x hx
  exact ⟨n, z, ⟨hz, c, hc, hcomp⟩, {j}, by simpa only [Finset.coe_singleton,
    Set.image_singleton] using hj⟩

/-- Genuine simultaneous transversality to every original closed stratum proves
that adjoining the SAME original new hypersurface preserves SNC. -/
theorem append_isSnc_of_strata_smoothDivisor [IsRegular X]
    (E : X.DivisorFamily) (hE : E.IsSnc) (H : X.IdealSheafData)
    (hH : IsSmoothDivisor H)
    (hcut : ∀ s : Finset E.ι, IsSmoothDivisor (H.comap (stratum E s).subschemeι)) :
    (E.append H).IsSnc := by
  classical
  refine ⟨fun i => ?_, fun x => ?_⟩
  · obtain ⟨i, rfl⟩ := toLex.surjective i
    rcases i with i | i
    · exact hE.1 i
    · exact hH.1
  · by_cases hx : x ∈ H.support
    · obtain ⟨n, z, hz, c, hc, hcomp, j, hj, hfresh⟩ :=
        exists_transverse_coordinates E hE H hH hcut x hx
      let d : Option {i : E.ι // x ∈ (E.component i).support} → Fin n :=
        fun i => Option.casesOn' i j c
      have hd : Function.Injective d := by
        rintro (_ | i) (_ | i') heq
        · rfl
        · exact False.elim (hfresh i' heq.symm)
        · exact False.elim (hfresh i heq)
        · exact congrArg some (hc heq)
      refine ⟨n, z, hz, d ∘ appendThrough E H x,
        hd.comp (appendThrough_injective E H x), ?_⟩
      rintro ⟨i, hi⟩
      obtain ⟨i, rfl⟩ := toLex.surjective i
      rcases i with i | i
      · exact hcomp ⟨i, hi⟩
      · exact hj
    · obtain ⟨n, z, hz, c, hc, hcomp⟩ := hE.2 x
      have hsome : ∀ i : {i : (E.append H).ι // x ∈ ((E.append H).component i).support},
          ∃ j, appendThrough E H x i = some j := by
        rintro ⟨i, hi⟩
        obtain ⟨i, rfl⟩ := toLex.surjective i
        rcases i with i | i
        · exact ⟨⟨i, hi⟩, rfl⟩
        · exact (hx hi).elim
      choose d hd using hsome
      have hdi : Function.Injective d := by
        intro i i' heq
        apply appendThrough_injective E H x
        rw [hd, hd, heq]
      refine ⟨n, z, hz, c ∘ d, hc.comp hdi, ?_⟩
      intro i
      obtain ⟨i, hi⟩ := i
      obtain ⟨i, rfl⟩ := toLex.surjective i
      rcases i with i | i
      · have heq : d ⟨toLex (Sum.inl i), hi⟩ = ⟨i, hi⟩ :=
          Option.some.inj (hd ⟨toLex (Sum.inl i), hi⟩).symm
        change (E.component i).stalkIdeal x = Ideal.span {z (c (d _))}
        rw [heq]
        exact hcomp ⟨i, hi⟩
      · exact (hx hi).elim

/-- ORIGINAL smooth Cartier zero schemes on every ORIGINAL closed SNC stratum
internally supply the codimension-one transversality and preserve the original
SNC family. Mere smoothness is never used as a substitute for Cartier data. -/
theorem append_isSnc_of_strata_cartier_smooth {k : Type u} [Field k] [PerfectField k]
    (p : X ⟶ Spec (.of k)) [Smooth p] (E : X.DivisorFamily) (hE : E.IsSnc)
    (H : X.IdealSheafData) (hH : H.IsInvertible) [Smooth (H.subschemeι ≫ p)]
    (hcartier : ∀ s : Finset E.ι, (H.comap (stratum E s).subschemeι).IsInvertible)
    (hsmooth : ∀ s : Finset E.ι, Smooth
      ((H.comap (stratum E s).subschemeι).subschemeι ≫ (stratum E s).subschemeι ≫ p)) :
    (E.append H).IsSnc ∧ E.HasSncWith H := by
  let : IsRegular X := (Scheme.smooth_iff_isRegular p).mp inferInstance
  have hHD : IsSmoothDivisor H := NadelBertiniSncCartier.isSmoothDivisor_of_cartier_regular
    H hH ((Scheme.smooth_iff_isRegular (H.subschemeι ≫ p)).mp inferInstance)
  have hcuts : ∀ s : Finset E.ι, IsSmoothDivisor (H.comap (stratum E s).subschemeι) := by
    intro s
    let : IsRegular (stratum E s).subscheme := stratum_isRegular p E hE s
    let := hsmooth s
    exact NadelBertiniSncCartier.isSmoothDivisor_of_cartier_regular _ (hcartier s)
      ((Scheme.smooth_iff_isRegular
        ((H.comap (stratum E s).subschemeι).subschemeι ≫ (stratum E s).subschemeι ≫ p)).mp
        inferInstance)
  exact ⟨append_isSnc_of_strata_smoothDivisor E hE H hHD hcuts,
    hasSncWith_of_strata_smoothDivisor E hE H hHD hcuts⟩

end EnvelopeProperty.Vanishing.NadelBertiniSncCriterion
