import Hironaka.Scheme.Snc.EtaleParameters
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Algebra.Local.Defs

/-! # Genuine local transversality adjoining an original hypersurface equation

The new equation is tested against the whole original maximal-square plus the
actual old component ideal. Native cotangent basis extension retains every
original component generator and the same original hypersurface equation.
-/
noncomputable section
open AlgebraicGeometry IsLocalRing Ideal
universe u v
namespace EnvelopeProperty.Vanishing.NadelBertiniSncLocal
variable {R : Type u} [CommRing R] [IsLocalRing R] {ι : Type v}

/-- A residue-field cotangent combination lifts to an actual original element of
the original generator ideal, with exactly the same original cotangent class. -/
theorem cotangent_span_lift (w : ι → R) (hw : ∀ i, w i ∈ maximalIdeal R)
    {v : CotangentSpace R}
    (hv : v ∈ Submodule.span (ResidueField R)
      (Set.range fun i => (maximalIdeal R).toCotangent ⟨w i, hw i⟩)) :
    ∃ b : maximalIdeal R, (b : R) ∈ Ideal.span (Set.range w) ∧
      (maximalIdeal R).toCotangent b = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact ⟨⟨w i, hw i⟩, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  | zero => exact ⟨0, Ideal.zero_mem _, map_zero _⟩
  | add v v' hv hv' ih ih' =>
      obtain ⟨b, hb, he⟩ := ih
      obtain ⟨b', hb', he'⟩ := ih'
      exact ⟨b + b', Ideal.add_mem _ hb hb', by rw [map_add, he, he']⟩
  | smul c v hv ih =>
      obtain ⟨b, hb, he⟩ := ih
      obtain ⟨a, ha⟩ := residue_surjective (R := R) c
      refine ⟨a • b, Submodule.smul_mem _ a hb, ?_⟩
      rw [map_smul, he, ← ha, ← ResidueField.algebraMap_eq, algebraMap_smul]

/-- Nonmembership of the ORIGINAL equation in the actual maximal-square plus
old ideal is genuine cotangent transversality to the original old generators. -/
theorem cotangent_notMem_span (w : ι → R) (hw : ∀ i, w i ∈ maximalIdeal R)
    (h : R) (hh : h ∈ maximalIdeal R)
    (htrans : h ∉ maximalIdeal R ^ 2 ⊔ Ideal.span (Set.range w)) :
    (maximalIdeal R).toCotangent ⟨h, hh⟩ ∉ Submodule.span (ResidueField R)
      (Set.range fun i => (maximalIdeal R).toCotangent ⟨w i, hw i⟩) := by
  intro hmem
  obtain ⟨b, hb, he⟩ := cotangent_span_lift w hw hmem
  have hsub : h - (b : R) ∈ maximalIdeal R ^ 2 :=
    (Ideal.toCotangent_eq _).mp he.symm
  apply htrans
  have heq : h = (h - (b : R)) + (b : R) := by ring
  rw [heq]
  exact Submodule.add_mem_sup hsub hb

/-- An original local-ring map carries a genuinely nonzero transverse class back
to nonmembership in maximal-square plus its ACTUAL kernel. -/
theorem notMem_sq_sup_ker_of_image_notMem_sq {S : Type v} [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (h : R)
    (hh : φ h ∉ maximalIdeal S ^ 2) : h ∉ maximalIdeal R ^ 2 ⊔ RingHom.ker φ := by
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  apply hh
  rw [← hab, map_add, RingHom.mem_ker.mp hb, add_zero]
  have hm : (maximalIdeal R ^ 2).map φ ≤ maximalIdeal S ^ 2 := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le φ) 2
  exact hm (Ideal.mem_map_of_mem φ ha)

end EnvelopeProperty.Vanishing.NadelBertiniSncLocal

namespace EnvelopeProperty.Vanishing.NadelBertiniSncLocal
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {ι : Type v}

/-- Genuine original transversality completes the SAME old component parameters
and SAME new equation to one actual regular system of parameters. -/
theorem exists_common_regularParameters
    {n : ℕ} (z : Fin n → R) (hz : IsRegularSystemOfParameters z)
    (c : ι → Fin n) (hc : Function.Injective c) (h : R) (hh : h ∈ maximalIdeal R)
    (htrans : h ∉ maximalIdeal R ^ 2 ⊔ Ideal.span (Set.range (z ∘ c))) :
    ∃ (m : ℕ) (y : Fin m → R), IsRegularSystemOfParameters y ∧
      ∃ d : Option ι → Fin m, Function.Injective d ∧
        ∀ i, y (d i) = Option.casesOn' i h (z ∘ c) := by
  have hw : ∀ i, z (c i) ∈ maximalIdeal R :=
    fun i => x_mem_maximalIdeal_of_span_eq z hz.1.symm (c i)
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hz.1.symm hz.2
  have hli : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent ⟨z (c i), hw i⟩) := by
    convert b.linearIndependent.comp c hc using 1
    funext i
    exact (hb (c i)).symm
  let w : Option ι → R := fun i => Option.casesOn' i h (z ∘ c)
  have hwm : ∀ i, w i ∈ maximalIdeal R := by
    rintro (_ | i)
    · exact hh
    · exact hw i
  have hcot : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent ⟨w i, hwm i⟩) := by
    have hhli := hli.option (cotangent_notMem_span (z ∘ c) hw h hh htrans)
    convert hhli using 1
    funext i
    cases i <;> rfl
  exact exists_span_eq_maximalIdeal_of_linearIndependent w hwm hcot

end EnvelopeProperty.Vanishing.NadelBertiniSncLocal
