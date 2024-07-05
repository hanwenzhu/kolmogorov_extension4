import KolmogorovExtension4.IonescuTulcea

/- Infinite product of probability spaces (Łomnick–Ulam) -/

open Set MeasureTheory

open scoped ENNReal BigOperators

namespace ProbabilityTheory

section PiFinset

variable {ι : Type*} {α : ι → Type*}
variable [∀ i, MeasurableSpace (α i)] [∀ i, Nonempty (α i)]
variable {P : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (P i)]

-- TODO probably can just replace this inline? it is basically just Measure.pi
noncomputable abbrev piFinset (P : ∀ i, Measure (α i)) (J : Finset ι) :
    Measure (∀ i : J, α i) := Measure.pi fun i ↦ P i

theorem pi_projective :
    IsProjectiveMeasureFamily (piFinset P) := by
  classical
  intro I J hJI
  apply Measure.pi_eq
  intro s hs
  have : (fun x j ↦ x ⟨j, hJI j.2⟩) ⁻¹' univ.pi s = (univ : Set I).pi
      fun i ↦ if h : i.1 ∈ J then s ⟨i, h⟩ else (univ : Set (α i)) := by
    ext x
    constructor
    · intro hx i _
      beta_reduce
      split_ifs with h
      · exact hx ⟨i, h⟩ (mem_univ _)
      · trivial
    · intro hx j _
      have := hx ⟨j, hJI j.2⟩ (mem_univ _)
      beta_reduce at this
      rwa [dif_pos] at this
  rw [Measure.map_apply _ (.univ_pi hs), piFinset, this, Measure.pi_pi]
  swap; exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  let e : (I.filter fun i ↦ i ∈ J) ≃ J :=
    ⟨fun i ↦ ⟨i, (Finset.mem_filter.mp i.2).2⟩,
      fun j ↦ ⟨j, (Finset.mem_filter.mpr ⟨hJI j.2, j.2⟩)⟩,
      fun i ↦ rfl,
      fun j ↦ rfl⟩
  calc
    _ = ∏ i ∈ I, P i (if h : i ∈ J then s ⟨i, h⟩ else univ) :=
      Finset.prod_attach _ _
    _ = ∏ i : (I.filter fun i ↦ i ∈ J), P (e i) (s (e i)) := by
      simp_rw [apply_dite, measure_univ, Finset.prod_dite, Finset.prod_const_one, mul_one]
      rfl
    _ = ∏ i : J, P i (s i) :=
      e.bijective.prod_comp fun i ↦ P i (s i)

end PiFinset

section PiNat

variable {α : ℕ → Type*}
variable [∀ i, MeasurableSpace (α i)] [∀ i, Nonempty (α i)]
variable (P : ∀ i : ℕ, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]

/-- Auxiliary construction -/
noncomputable def piNat (P : ∀ i : ℕ, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    Measure (∀ i, α i) :=
  itLimit fun i ↦ kernel.const _ (P i)

instance : IsProbabilityMeasure (piNat P) := itLimit_isProbabilityMeasure

-- theorem MeasureTheory.Measure.map_pi {ι : Type*} {α : ι → Type*} [Fintype ι]
--     [(i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))

def rangeToFin (n) : Finset.range n ≃ Fin n where
  toFun i := ⟨i, Finset.mem_range.mp i.2⟩
  invFun i := ⟨i, Finset.mem_range.mpr i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- i feel like this proof and pi_projective are related and can be simplified..
lemma map_piFinset_range {n} :
    (piFinset P (Finset.range n)).map (fun x (i : Fin n) ↦ x ⟨i, Finset.mem_range.mpr i.2⟩) =
      Measure.pi fun (i : Fin n) ↦ P i := by
  symm; apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply]
  rotate_left
  · exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  · exact .pi (Countable.to_set inferInstance) fun _ _ ↦ hs _
  calc
  _ = piFinset P _ ((univ : Set (Finset.range n)).pi fun i ↦ s (rangeToFin n i)) := by
    congr
    ext x
    constructor <;> exact fun hx i _ ↦ hx _ (mem_univ _)
  _ = ∏ i : Finset.range n, P (rangeToFin n i) (s (rangeToFin n i)) := by
    rw [piFinset, Measure.pi_pi]
    rfl
  _ = ∏ i : Fin n, P i (s i) :=
    (rangeToFin n).bijective.prod_comp fun i ↦ P i (s i)

lemma piNat_fin {n : ℕ} :
    (piNat P).map (fun x (i : Fin n) ↦ x i) = Measure.pi fun (i : Fin n) ↦ P i := by
  have isProb n : IsProbabilityMeasure ((piNat P).map (fun x (i : Fin n) ↦ x i)) :=
    isProbabilityMeasure_map (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _).aemeasurable
  induction' n with n ih
  · apply measure_eq_of_subsingleton
  · rw [piNat, isProjectiveLimitNat_itLimit] at ih
    rw [piNat, isProjectiveLimitNat_itLimit, itMeasure,
      Measure.compProd, kernel.prodMkLeft, kernel.comap_const, kernel.const_compProd_const,
      kernel.const_apply, ih]
    symm; apply Measure.pi_eq
    intro s hs
    conv_rhs => rw [Fin.prod_univ_castSucc, ← Measure.pi_pi, ← Measure.prod_prod]
    apply (Measure.map_apply measurable_fin_prod_right
      (.pi (Countable.to_set inferInstance) fun _ _ ↦ hs _)).trans
    congr
    -- fin_prod_right n ⁻¹' univ.pi s = univ.pi (s ∘ castSucc) ×ˢ s n
    ext x
    unfold fin_prod_right
    constructor
    · intro h
      constructor
      · intro i _
        have := h i (mem_univ _)
        beta_reduce at this
        rwa [Fin.coe_eq_castSucc, Fin.lastCases_castSucc] at this
      · simpa [Fin.lastCases_last] using h (Fin.last n) (mem_univ _)
    · intro h i _
      cases' i using Fin.lastCases with i
      · simpa using h.2
      · simpa using h.1 i

lemma piNat_finset {n : ℕ} :

end PiNat

variable {ι : Type*} {α : ι → Type*}
variable [∀ i, MeasurableSpace (α i)] [∀ i, Nonempty (α i)]
variable {P : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (P i)]

section Countable

lemma _root_.Encodable.iget_encodek₂ {α : Type*} [Inhabited α] [Encodable α] (a : α) :
    (Encodable.decode₂ α (Encodable.encode a)).iget = a := by
  rw [Encodable.encodek₂]

open Encodable

variable [Inhabited ι] [Encodable ι]

/-- Auxiliary construction, product indexed on nonempty and countable I. -/
noncomputable def piOfEncodable (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    Measure (∀ i : ι, α i) :=
  (itLimit fun n ↦ kernel.const _ (P (decode₂ ι n).iget)).map
    fun x i ↦ cast (congrArg (fun i ↦ α i) (iget_encodek₂ i)) (x (encode i))

-- theorem piOfEncodable_preimage_fin
--     {n : ℕ} {s : Set (∀ i : Fin n, α i)} :
--     piOfEncodable P ((fun x (i : Fin n) ↦ x (decode₂ ι n).iget)) = Equiv.piFinSucc

-- theorem piOfEncodable_preimage_finset
--     {J : Finset ι} {s : Set (∀ j : J, α j)} :
--     piOfEncodable P ((fun x (j : J) ↦ x j) ⁻¹' s) = piFinset P J s := by
--   have : Inhabited J := sorry
--   rw [piOfEncodable, Measure.map_apply]
--   -- J viewed as a Finset of ℕ
--   set J' : Finset ℕ := J.map ⟨encode, encode_injective⟩ with hJ'
--   have h (j : J) := congrArg α (iget_encodek₂ (j : ι))
--   set t : Set (∀ n : ℕ, α (decode₂ ι n).iget) := cylinder J'
--     ((fun x (j : J) ↦ h j ▸ x ⟨encode (j : ι), by simp [hJ']⟩) ⁻¹' s) with ht
--   change itLimit (fun n ↦ kernel.const _ (P (decode₂ ι n).iget)) t = _
--   have htc : t ∈ cylinders _ := cylinder_mem_cylinders J' _ ?_
--   rw [ht, itLimit_of_mem_cylinders htc]
--   induction cylinders.nat htc

-- noncomputable def cylinders.setEncodable {s}
--     (hs : s ∈ cylinders α) (hsI : ↑(cylinders.finset hs) ⊆ I) :
--     Set (∀ i : I, α i) :=
--   (fun x i ↦ x (inclusion hsI i)) ⁻¹' (cylinders.set hs)

-- theorem piOfEncodable_cylinder' {s}
--     (hs : s ∈ cylinders α) (hsI : ↑(cylinders.finset hs) ⊆ I) :
--     piOfEncodable P I (cylinders.setEncodable hs hsI) =
--       piFinset P (cylinders.finset hs) (cylinders.set hs) := by
--   classical
--   rw [cylinders.setEncodable, ← Measure.map_apply _ (cylinders.measurableSet hs)]
--   swap; exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
--   congr
--   symm; apply Measure.pi_eq
--   intro t ht
--   -- set J := cylinders.finset hs
--   have : (fun x j ↦ x (inclusion hsI j)) ⁻¹' univ.pi t = (univ : Set I).pi
--       fun i ↦ if h : i.1 ∈ cylinders.finset hs then t ⟨i, h⟩ else (univ : Set (α i)) := by
--     ext x
--     constructor
--     · intro hx i _
--       beta_reduce
--       split_ifs with h
--       · exact hx ⟨i, h⟩ (mem_univ _)
--       · trivial
--     · intro hx j _
--       have := hx ⟨j, hsI j.2⟩ (mem_univ _)
--       beta_reduce at this
--       rwa [dif_pos] at this
--   erw [Measure.map_apply _ (.univ_pi ht), this, Measure.pi_pi]

end Countable

noncomputable def piContent (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    AddContent (cylinders α) := kolContent (pi_projective (P := P))

theorem piContent_eq_of_subset_encodable {s} {I : Set ι} [Inhabited I] [Encodable I]
    (hs : s ∈ cylinders α) (hsI : ↑(cylinders.finset hs) ⊆ I) :
    piContent P s = piOfEncodable P I (cylinders.setEncodable hs hsI) := by
  rw [piContent, kolContent_eq, piOfEncodable_cylinder']
  rfl

-- theorem cylinders.iUnion {s : ℕ → Set (∀ i, α i)}
--     (hs : ∀ n, s n ∈ cylinders α) (hs_Union : (⋃ n, s n) ∈ cylinders α) :

theorem piContent_sigma_subadditive ⦃s : ℕ → Set (∀ i, α i)⦄
    (hs : ∀ n, s n ∈ cylinders α) (hs_Union : (⋃ n, s n) ∈ cylinders α) :
    piContent P (⋃ n, s n) ≤ ∑' n, piContent P (s n) := by
  classical
  let I : Set ι := (⋃ n, cylinders.finset (hs n)) ∪ cylinders.finset hs_Union
  have hI : Encodable I := (countable_union.mpr ⟨(countable_iUnion fun _ ↦
    Finset.countable_toSet _), Finset.countable_toSet _⟩).toEncodable

noncomputable def pi (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    Measure (∀ i, α i) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (piContent P) piContent_sigma_subadditive
