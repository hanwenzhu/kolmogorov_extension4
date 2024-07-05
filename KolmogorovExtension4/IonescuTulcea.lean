import KolmogorovExtension4.KolmogorovExtension
-- import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.Data.Real.Archimedean

/- Note: we follow the proof of Kallenberg. -/

-- TODO standardize some namings (of_mem_cylinder/measure_cylinder/etc), namespace, move stuff etc

open Set MeasureTheory

open scoped ENNReal BigOperators

namespace ProbabilityTheory

section ProdAssoc

variable {α β γ : Type*}
variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[measurability]
lemma measurable_prodAssoc : Measurable (Equiv.prodAssoc α β γ) :=
  Measurable.prod_mk
    (measurable_fst.comp measurable_fst)
    (Measurable.prod_mk (measurable_snd.comp measurable_fst) measurable_snd)

@[measurability]
lemma measurable_prodAssoc_symm : Measurable (Equiv.prodAssoc α β γ).symm :=
  Measurable.prod_mk
    (Measurable.prod_mk measurable_fst (measurable_fst.comp measurable_snd))
    (measurable_snd.comp measurable_snd)

-- therefore infact it is a MeasurableEquiv, not used here

end ProdAssoc

namespace kernel

variable {α β γ δ : Type*}
variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
variable {κ : kernel α β} {η : kernel (α × β) γ} {ρ : kernel (α × β × γ) δ}
variable [IsSFiniteKernel κ] [IsSFiniteKernel η] [IsSFiniteKernel ρ]

-- we can form variants of this by replacing α × β × γ with (α × β) × γ, map κ f = η with κ = map η f⁻¹, etc
theorem compProd_assoc :
    map ((κ ⊗ₖ η) ⊗ₖ ρ) (Equiv.prodAssoc β γ δ) measurable_prodAssoc =
    κ ⊗ₖ (η ⊗ₖ comap ρ (Equiv.prodAssoc α β γ) measurable_prodAssoc) := by
  ext a s hs
  rw [map_apply', compProd_apply, lintegral_compProd, compProd_apply]
  · congr; ext b
    rw [compProd_apply]; rfl
    · exact measurable_prod_mk_left hs
  · exact hs
  · apply measurable_kernel_prod_mk_left' (measurable_prodAssoc hs)
  · exact measurable_prodAssoc hs
  · exact hs

@[simp]
theorem map_map {f : β → γ} {g : γ → δ} (hf : Measurable f) (hg : Measurable g) :
    map (map κ f hf) g hg = map κ (g ∘ f) (hg.comp hf) := by
  ext
  rw [map_apply, map_apply, Measure.map_map hg hf, map_apply]

@[simp]
theorem comap_comap {f : γ → α} {g : δ → γ} (hf : Measurable f) (hg : Measurable g) :
    comap (comap κ f hf) g hg = comap κ (f ∘ g) (hf.comp hg) :=
  rfl

@[simp]
theorem comap_const {μβ : Measure β} {f : γ → α} (hf : Measurable f) :
    comap (const α μβ) f hf = const γ μβ := rfl

@[simp]
theorem compProd_const {μγ : Measure γ} :
    κ ⊗ₖ const (α × β) μγ = κ ×ₖ const α μγ := rfl

@[simp]
theorem const_compProd_const {μβ : Measure β} {μγ : Measure γ} [SFinite μβ] [SFinite μγ] :
    const α μβ ⊗ₖ const (α × β) μγ = const α (μβ.prod μγ) := by
  simp only [compProd_const]
  -- FIXME: see mathlib#14424
  -- exact prod_const μβ μγ
  ext
  rw [const_apply, prod_apply]; rfl

-- similarly we can do other ones
theorem _root_.MeasureTheory.Measure.compProd_map_left {μ : Measure γ} [SFinite μ]
    {f : γ → α} (hf : Measurable f) :
    μ.map f ⊗ₘ κ = (μ ⊗ₘ comap κ f hf).map (Prod.map f id) := by
  ext s hs
  rw [Measure.map_apply, Measure.compProd_apply, Measure.compProd_apply,
    MeasureTheory.lintegral_map]; rfl
  · exact measurable_kernel_prod_mk_left hs
  · exact hf
  · exact hf.prod_map measurable_id hs
  · exact hs
  · exact hf.prod_map measurable_id
  · exact hs

-- similarly we can do compProd_comap_right? idk
theorem compProd_map_left {f : β → γ} (hf : Measurable f)
    {η : kernel (α × γ) δ} [IsSFiniteKernel η] :
    map κ f hf ⊗ₖ η = map (κ ⊗ₖ comap η (Prod.map id f) (measurable_id.prod_map hf))
      (Prod.map f id) (hf.prod_map measurable_id) := by
  ext a s hs
  rw [compProd_apply, lintegral_map, map_apply', compProd_apply]; rfl
  · exact hf.prod_map measurable_id hs
  · exact hs
  · apply measurable_kernel_prod_mk_left' hs
  · exact hs

theorem comap_compProd {f : δ → α} (hf : Measurable f) :
    comap (κ ⊗ₖ η) f hf =
      comap κ f hf ⊗ₖ comap η (Prod.map f id) (hf.prod_map measurable_id) := by
  ext a s hs
  rw [comap_apply, compProd_apply _ _ _ hs, compProd_apply _ _ _ hs]; rfl

theorem compProd_map_right {f : γ → δ} (hf : Measurable f) :
    κ ⊗ₖ map η f hf = map (κ ⊗ₖ η) (Prod.map id f) (measurable_id.prod_map hf) := by
  ext a s hs
  rw [compProd_apply, map_apply', compProd_apply]
  congr; ext b
  rw [map_apply']; rfl
  · exact measurable_prod_mk_left hs
  · exact measurable_id.prod_map hf hs
  · exact hs
  · exact hs

theorem compProd_assoc' :
    (κ ⊗ₖ η) ⊗ₖ ρ = map
      (κ ⊗ₖ (η ⊗ₖ comap ρ (Equiv.prodAssoc α β γ) measurable_prodAssoc))
      (Equiv.prodAssoc β γ δ).symm measurable_prodAssoc_symm := by
  ext
  rw [← compProd_assoc, map_map, map_apply, (Equiv.prodAssoc β γ δ).symm_comp_self, Measure.map_id]

theorem swapRight_prod {η : kernel α γ} [IsSFiniteKernel η] :
    swapRight (κ ×ₖ η) = η ×ₖ κ := by
  ext
  rw [prod_apply, swapRight_apply, prod_apply, Measure.prod_swap]

theorem _root_.MeasureTheory.Measure.eq_of_subsingleton
    [hα : Subsingleton α] {μ ν : Measure α}
    (h : μ univ = ν univ) : μ = ν := by
  ext s hs
  obtain rfl | rfl : s = ∅ ∨ s = univ := by
    rcases isEmpty_or_nonempty α with h_empty | h_nonempty
    · exact .inl (eq_empty_of_forall_not_mem fun y _ ↦ h_empty.elim y)
    have ⟨x⟩ := h_nonempty
    by_cases hx : x ∈ s
    · exact .inr (eq_univ_of_forall fun y ↦ hα.allEq y x ▸ hx)
    · exact .inl (eq_empty_of_forall_not_mem fun y ↦ hα.allEq y x ▸ hx)
  · rw [measure_empty, measure_empty]
  · exact h

theorem _root_.ProbabilityTheory.measure_eq_of_subsingleton
    [hα : Subsingleton α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν :=
  Measure.eq_of_subsingleton (by rw [measure_univ, measure_univ])

theorem eq_of_subsingleton {η : kernel α β}
    [IsMarkovKernel κ] [IsMarkovKernel η] [Subsingleton β] :
    κ = η := by
  ext1 a
  exact ProbabilityTheory.measure_eq_of_subsingleton

end kernel

variable {α : ℕ → Type*} [∀ i, MeasurableSpace (α i)]

section KolExtensionNat

/- We restate some results when they are in ℕ. -/

-- TODO this can be replaced inline
abbrev proj (n m : ℕ) (h : m ≤ n) (x : ∀ i : Fin n, α i) (j : Fin m) : α j :=
  x (Fin.castLE h j)

def succSup (I : Finset ℕ) : ℕ :=
  if h : I.Nonempty then (I.sup' h id).succ else 0

lemma lt_succSup {I : Finset ℕ} {i : I} : i < succSup I := by
  rw [succSup]
  split_ifs with h
  · exact Nat.lt_succ_of_le (I.le_sup' (f := id) i.2)
  · exact absurd ⟨i, Finset.coe_mem i⟩ h

lemma succSup_mono {I J : Finset ℕ} (h : I ⊆ J) :
    succSup I ≤ succSup J := by
  unfold succSup
  split_ifs with hI hJ
  · exact Nat.succ_le_succ (Finset.sup'_le hI id fun _ hx ↦ Finset.le_sup' id (h hx))
  · have ⟨i, hi⟩ := hI
    exact absurd ⟨i, h hi⟩ hJ
  · exact Nat.zero_le _
  · rfl

lemma succSup_range {n : ℕ} : succSup (Finset.range n) = n := by
  unfold succSup
  by_cases h : n = 0
  · rw [h]; rfl
  have h' := Finset.nonempty_range_iff.mpr h
  rw [dif_pos h']
  apply le_antisymm
  · exact Nat.succ_le_of_lt ((Finset.sup'_lt_iff h').mpr fun _ ↦ Finset.mem_range.mp)
  · exact Nat.le_succ_of_pred_le (Finset.le_sup' id (Finset.mem_range.mpr (Nat.pred_lt h)))

def IsProjectiveMeasureFamilyNat (P : ∀ n : ℕ, Measure (∀ i : Fin n, α i)) : Prop :=
  ∀ (n : ℕ),
    P n = (P (n + 1)).map fun (x : ∀ i : Fin (n + 1), α i) (i : Fin n) ↦ x i.castSucc

noncomputable def toFinsetNat (P : ∀ n : ℕ, Measure (∀ i : Fin n, α i)) (I : Finset ℕ) :
    Measure (∀ i : I, α i) :=
  (P (succSup I)).map fun x i ↦ x ⟨i, lt_succSup⟩

instance {P : ∀ n, Measure (∀ i : Fin n, α i)} {I}
    [IsFiniteMeasure (P (succSup I))] : IsFiniteMeasure (toFinsetNat P I) :=
  Measure.isFiniteMeasure_map _ _

instance {P : ∀ n, Measure (∀ i : Fin n, α i)} {I}
    [IsProbabilityMeasure (P (succSup I))] : IsProbabilityMeasure (toFinsetNat P I) :=
  isProbabilityMeasure_map (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _).aemeasurable

theorem toFinsetNat_range {P : ∀ n : ℕ, Measure (∀ i : Fin n, α i)} {n : ℕ} :
    toFinsetNat P (Finset.range n) = (P n).map fun f (i : Finset.range n) ↦ f ⟨i, Finset.mem_range.mp (Finset.coe_mem i)⟩ := by
  have {m} (h : m = n) : P m = (P n).map fun x (i : Fin m) ↦ x (i.cast h) := by
    cases h
    exact Measure.map_id.symm
  rw [toFinsetNat, this (@succSup_range n), Measure.map_map]
  · rfl
  all_goals exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem IsProjectiveMeasureFamilyNat.map_proj
    {P : ∀ n : ℕ, Measure (∀ j : Fin n, α j)} (hP : IsProjectiveMeasureFamilyNat P)
    {n m : ℕ} (h : m ≤ n) : P m = (P n).map fun x j ↦ proj n m h x j := by
  induction' n, h using Nat.le_induction with n h ih
  · exact Measure.map_id.symm
  · rw [ih, hP, Measure.map_map]
    · rfl
    all_goals exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem IsProjectiveMeasureFamilyNat.isProjectiveMeasureFamily_toFinsetNat
    {P : ∀ n : ℕ, Measure (∀ j : Fin n, α j)} (hP : IsProjectiveMeasureFamilyNat P) :
    IsProjectiveMeasureFamily (toFinsetNat P) := by
  intro I J hJI
  dsimp only [toFinsetNat]
  rw [IsProjectiveMeasureFamilyNat.map_proj hP (succSup_mono hJI),
    Measure.map_map, Measure.map_map]
  · rfl
  all_goals exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem IsProjectiveMeasureFamily.toNat
    {P : ∀ J : Finset ℕ, Measure (∀ j : J, α j)} (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveMeasureFamilyNat fun n ↦ (P (Finset.range n)).map fun x i ↦ x ⟨i, Finset.mem_range.mpr i.2⟩ := by
  intro n
  beta_reduce
  rw [Measure.map_map, hP (Finset.range (n + 1)) _ (Finset.range_mono n.le_succ),
    Measure.map_map]; rfl
  all_goals exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

def cylinderNat (n : ℕ) (S : Set (∀ i : Fin n, α i)) : Set (∀ i : ℕ, α i) :=
  (fun (f : ∀ i : ℕ, α i) (i : Fin n) ↦ f i) ⁻¹' S

theorem cylinderNat_eq_cylinder {n} {S : Set (∀ i : Fin n, α i)} :
    cylinderNat n S = cylinder (Finset.range n)
      fun f ↦ (fun (i : Fin n) ↦ f ⟨i, Finset.mem_range.mpr i.2⟩) ∈ S :=
  rfl

theorem cylinderNat_mem_cylinders {n S} (hS : MeasurableSet S) :
    cylinderNat n S ∈ cylinders α := by
  rw [cylinderNat_eq_cylinder]
  exact cylinder_mem_cylinders _ _
    ((measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _) hS)

-- TODO? Maybe we can restrict this finset so that the nat is minimal; so that
-- cylinders.nat is mono in s
noncomputable def cylinders.nat {s : Set (∀ i : ℕ, α i)} (hs : s ∈ cylinders α) : ℕ :=
  succSup (cylinders.finset hs)

def cylinders.setFin {s : Set (∀ i : ℕ, α i)} (hs : s ∈ cylinders α) :
    Set (∀ i : Fin (cylinders.nat hs), α i) :=
  (fun (f : ∀ i : Fin _, α i) (i : cylinders.finset hs) ↦
    f ⟨i, lt_succSup⟩) ⁻¹' cylinders.set hs

theorem cylinders.measurableSet_setFin {s : Set (∀ i : ℕ, α i)} (hs : s ∈ cylinders α) :
    MeasurableSet (cylinders.setFin hs) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) (cylinders.measurableSet hs)

theorem cylinders.eq_cylinderNat {s : Set (∀ i : ℕ, α i)} (hs : s ∈ cylinders α) :
    s = cylinderNat (cylinders.nat hs) (cylinders.setFin hs) :=
  cylinders.eq_cylinder hs

theorem cylinderNat_univ (n : ℕ) : cylinderNat n univ = (univ : Set (∀ i, α i)) := by
  rw [cylinderNat, preimage_univ]

theorem IsProjectiveMeasureFamilyNat.congr_cylinderNat [∀ i, Nonempty (α i)]
    {P : ∀ n : ℕ, Measure (∀ j : Fin n, α j)} (hP : IsProjectiveMeasureFamilyNat P)
    {m n : ℕ} {S : Set (∀ i : Fin m, α i)} {T : Set (∀ i : Fin n, α i)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (h_eq : cylinderNat m S = cylinderNat n T) :
    P m S = P n T := by
  -- we could prove this directly (as in IsProjectiveMeasureFamily.congr) but we quote that result instead
  rw [cylinderNat_eq_cylinder, cylinderNat_eq_cylinder] at h_eq
  convert hP.isProjectiveMeasureFamily_toFinsetNat.congr_cylinder _ _ h_eq
  any_goals
    rw [toFinsetNat_range, Measure.map_apply]
    · rfl
  any_goals apply measurableSet_preimage _ ‹MeasurableSet _›
  all_goals exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

def IsProjectiveLimitNat (μ : Measure (∀ i, α i))
    (P : ∀ n : ℕ, Measure (∀ i : Fin n, α i)) : Prop :=
  ∀ n : ℕ, (μ.map fun (x : ∀ i, α i) (i : Fin n) ↦ x i) = P n

-- not used, but there should also be a non-ℕ version of this?
theorem IsProjectiveLimitNat.isProjectiveMeasureFamilyNat {μ P}
    (hμ : IsProjectiveLimitNat μ P) : @IsProjectiveMeasureFamilyNat α _ P := by
  intro n
  rw [← hμ, ← hμ, Measure.map_map]; rfl
  all_goals exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem IsProjectiveLimitNat.isProjectiveLimit {μ P}
    (hμ : IsProjectiveLimitNat μ P) :
    @IsProjectiveLimit ℕ α _ μ (toFinsetNat P) := by
  intro I
  rw [toFinsetNat, ← hμ, Measure.map_map]; rfl
  all_goals exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem IsProjectiveLimitNat.unique {μ ν : Measure (∀ i, α i)} {P}
    [∀ n, IsFiniteMeasure (P n)]
    (hμ : IsProjectiveLimitNat μ P) (hν : IsProjectiveLimitNat ν P) : μ = ν :=
  isProjectiveLimit_unique hμ.isProjectiveLimit hν.isProjectiveLimit

theorem IsProjectiveLimitNat.measure_cylinderNat {μ P} (h : IsProjectiveLimitNat μ P)
    {n} {s : Set (∀ i : Fin n, α i)} (hs : MeasurableSet s) :
    μ (cylinderNat n s) = P n s := by
  rw [cylinderNat, ← Measure.map_apply _ hs, h n]
  exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

end KolExtensionNat

section ITKernel

section FinMaps

/- Basic maps between products of α indexed by Fin, Finset.Ico, their products etc.
  (TODO rename, and they may be abstracted? and may belong to Mathlib.MeasureTheory.MeasurableSpace.Embedding,
    and Mathlib.Logic.Equiv.Fin, e.g. MeasurableEquiv.piFinsetUnion) -/

def fin_prod_ico (k n : ℕ)
    (p : (∀ i : Fin k, α i) × (∀ i : Finset.Ico k n, α i))
    (i : Fin n) : α i :=
  if h : i < k then
    p.1 ⟨i, h⟩
  else
    p.2 ⟨i, Finset.mem_Ico.mpr ⟨le_of_not_lt h, i.2⟩⟩

-- curried version
def fin_prod_ico' (k n : ℕ)
    (x : ∀ i : Fin k, α i) (y : ∀ i : Finset.Ico k n, α i)
    (i : Fin n) : α i :=
  fin_prod_ico k n (x, y) i

-- (this is just MeasurableEquiv.piFinSuccAbove)
def fin_prod_right (k : ℕ)
    (p : (∀ i : Fin k, α i) × α k)
    (i : Fin (k + 1)) : α i :=
  i.lastCases p.2 p.1

def ico_prod_right (j k : ℕ)
    (p : (∀ i : Finset.Ico j k, α i) × α k)
    (i : Finset.Ico j (k + 1)) : α i :=
  if h : i < k then
    p.1 ⟨i, Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp i.2).1, h⟩⟩
  else by
    rw [Nat.eq_of_le_of_lt_succ (le_of_not_lt h) (Finset.mem_Ico.mp i.2).2]
    exact p.2

def left_prod_ico (j k : ℕ)
    (p : α j × ∀ i : Finset.Ico (j + 1) k, α i)
    (i : Finset.Ico j k) : α i :=
  if h : j = i then
    cast (congrArg α h) p.1
  else
    haveI := Finset.mem_Ico.mp i.2
    p.2 ⟨i, Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt (lt_of_le_of_ne this.1 h), this.2⟩⟩

-- todo rename
lemma fin_prod_right_of_lt {k p} {i : Fin (k + 1)} (h : (i : ℕ) < k) :
    @fin_prod_right α k p i = p.1 ⟨i, h⟩ := by
  unfold fin_prod_right Fin.lastCases Fin.reverseInduction
  rw [dif_neg]
  intro h₁
  exact h.ne (congrArg ((↑) : Fin _ → ℕ) h₁)

lemma wtf {k n x y z} :
    @fin_prod_ico α k n (x, left_prod_ico k n (y, z)) =
      fin_prod_ico (k + 1) n (fin_prod_right k (x, y), z) := by
  ext i
  unfold fin_prod_ico left_prod_ico fin_prod_right Fin.lastCases Fin.reverseInduction
  simp only [Function.comp_apply, Equiv.prodAssoc_apply, Prod_map, id_eq, Fin.val_last]
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ <;> try rfl
  all_goals exfalso
  · apply_fun ((↑) : Fin (k + 1) → ℕ) at h₃
    exact h₁.ne h₃
  · exact h₂ (h₁.trans k.lt_succ_self)
  · exact h₆ (Fin.eq_of_val_eq (by simpa using h₄.symm))
  · exact h₅ (h₄.symm.trans_lt k.lt_succ_self)
  · exact h₄ (Nat.eq_of_lt_succ_of_not_lt h₇ h₁).symm
  · exact h₄ (Nat.eq_of_lt_succ_of_not_lt h₇ h₁).symm

lemma wtf2 {k n x y z} (h_ne : k ≠ n) :
    @ico_prod_right α k n (left_prod_ico k n (x, y), z) =
      left_prod_ico k (n + 1) (x, ico_prod_right (k + 1) n (y, z)) := by
  ext i
  unfold ico_prod_right left_prod_ico
  simp only [Function.comp_apply, Equiv.prodAssoc_symm_apply, Prod_map, id_eq]
  split_ifs with h₁ h₂ h₃ <;> try rfl
  exfalso
  exact h_ne (h₃.trans (Nat.eq_of_lt_succ_of_not_lt (Finset.mem_Ico.mp i.2).2 h₁))

lemma wtf3 {k a x} : @fin_prod_ico α k k (a, x) = a := by
  ext i
  unfold fin_prod_ico
  split_ifs with h
  · rfl
  · exact absurd i.2 h

lemma wtf4 {k x y z} : @ico_prod_right α k k (x, y) = left_prod_ico k (k + 1) (y, z) := by
  ext i
  unfold ico_prod_right left_prod_ico
  split_ifs with h₁ h₂ h₃
  · exact absurd h₂ h₁.ne'
  · exact absurd (Finset.mem_Ico.mp i.2).1 h₁.not_le
  · rfl
  · exact absurd (Nat.eq_of_lt_succ_of_not_lt (Finset.mem_Ico.mp i.2).2 h₁).symm h₃

-- should we eta expand this?
lemma wtf5 {n} : @fin_prod_ico' α 0 (n + 1) default ∘ ico_prod_right 0 n =
    fin_prod_right n ∘ Prod.map (fin_prod_ico' 0 n default) id := by
  funext ⟨x, y⟩ i
  unfold fin_prod_ico' fin_prod_ico ico_prod_right fin_prod_right Fin.lastCases Fin.reverseInduction
  simp only [not_lt_zero', ↓reduceDIte, eq_mpr_eq_cast, Function.comp_apply, Fin.val_last,
    Prod.map_apply, id_eq]
  split_ifs with h₁ h₂ h₃ <;> try rfl
  · simp only [h₂, Fin.val_last, lt_self_iff_false] at h₁
  · exact absurd (Fin.val_lt_last h₃) h₁

@[measurability]
theorem measurable_fin_prod_ico {k n : ℕ} :
    Measurable (@fin_prod_ico α k n) := by
  unfold fin_prod_ico
  apply measurable_pi_lambda
  intro i
  split_ifs
  · exact Measurable.eval measurable_fst
  · exact Measurable.eval measurable_snd

@[measurability]
theorem measurable_fin_prod_ico' {k n : ℕ} {x} :
    Measurable (@fin_prod_ico' α k n x) :=
  Measurable.of_uncurry_left (f := @fin_prod_ico' α k n) measurable_fin_prod_ico

@[measurability]
theorem measurable_ico_prod_right {j k : ℕ} :
    Measurable (@ico_prod_right α j k) := by
  unfold ico_prod_right
  apply measurable_pi_lambda
  intro i
  split_ifs with h
  · exact Measurable.eval measurable_fst
  · have := Nat.eq_of_le_of_lt_succ (le_of_not_lt h) (Finset.mem_Ico.mp i.2).2
    measurability

@[measurability]
theorem measurable_fin_prod_right {k : ℕ} :
    Measurable (@fin_prod_right α k) := by
  unfold fin_prod_right Fin.lastCases Fin.reverseInduction
  apply measurable_pi_lambda
  intro i
  split_ifs with h
  · measurability
  · exact Measurable.eval measurable_fst

@[measurability]
theorem measurable_left_prod_ico {j k : ℕ} :
    Measurable (@left_prod_ico α j k) := by
  unfold left_prod_ico
  apply measurable_pi_lambda
  intro i
  split_ifs with h
  · have {j' : ℕ} (h : j' = i) :
        Measurable fun (p : α j' × ∀ i : Finset.Ico (j' + 1) k, α i) ↦ cast (congrArg α h) p.1 := by
      cases h
      exact measurable_fst
    exact this h
  · exact Measurable.eval measurable_snd

-- these are used implicitly later
instance (k : ℕ) : IsEmpty (Finset.Ico k 0) :=
  ⟨fun x ↦ Nat.not_lt_zero _ (Finset.mem_Ico.mp x.2).2⟩

instance (k : ℕ) : IsEmpty (Finset.Ico k k) :=
  ⟨fun x ↦
    haveI := Finset.mem_Ico.mp x.2
    lt_irrefl k (this.1.trans_lt this.2)⟩

end FinMaps

variable {κ : ∀ n : ℕ, kernel (∀ i : Fin n, α i) (α n)}
variable [∀ n, IsMarkovKernel (κ n)]

/-- Informally this is `κ k ⊗ₖ ⋯ ⊗ₖ κ (n - 1)`, a kernel
from `α 0 × ⋯ × α (k - 1)` to `α k × ⋯ × α (n - 1)`. -/
noncomputable def itKernel (κ : ∀ n : ℕ, kernel (∀ i : Fin n, α i) (α n)) (k n : ℕ) :
    kernel (∀ i : Fin k, α i) (∀ i : Finset.Ico k n, α i) :=
  match n with
  | 0 => kernel.const _ (Measure.dirac
      -- note the space is singleton as Ico k 0 is empty
      default)
  | n + 1 => kernel.map
      (itKernel κ k n ⊗ₖ kernel.comap (κ n) (fin_prod_ico k n) measurable_fin_prod_ico)
      (ico_prod_right k n) measurable_ico_prod_right

instance {k n : ℕ} : IsMarkovKernel (itKernel κ k n) := by
  induction' n with n ih <;> unfold itKernel
  · infer_instance
  · infer_instance

theorem itKernel_succ {k n : ℕ} :
    itKernel κ k (n + 1) = kernel.map
      (itKernel κ k n ⊗ₖ kernel.comap (κ n) (fin_prod_ico k n) measurable_fin_prod_ico)
      (fun p i ↦ ico_prod_right k n p i) measurable_ico_prod_right := rfl

theorem itKernel_of_ge {k n : ℕ} (h : n ≤ k) :
    itKernel κ k n = kernel.const _ (Measure.dirac fun x ↦
      haveI := Finset.mem_Ico.mp x.2
      (lt_irrefl n ((h.trans this.1).trans_lt this.2)).elim) := by
  have : IsEmpty (Finset.Ico k n) := ⟨fun x ↦
    haveI := Finset.mem_Ico.mp x.2
    (lt_irrefl n ((h.trans this.1).trans_lt this.2))⟩
  exact kernel.eq_of_subsingleton

theorem itKernel_succ_left {k n : ℕ} :
    itKernel κ k n = kernel.map
      (κ k ⊗ₖ kernel.comap (itKernel κ (k + 1) n) (fin_prod_right k) measurable_fin_prod_right)
      (left_prod_ico k n) measurable_left_prod_ico := by
  induction' n with n ih
  · exact kernel.eq_of_subsingleton
  · rcases eq_or_ne k n with rfl | h_ne
    · rw [itKernel_succ, itKernel_of_ge (le_refl k), itKernel_of_ge (le_refl (k + 1)), kernel.comap_const,
        kernel.compProd_const, ← kernel.swapRight_prod]
      ext a s hs
      rw [kernel.map_apply', kernel.compProd_apply, kernel.const_apply, lintegral_dirac, kernel.comap_apply,
        kernel.map_apply', kernel.swapRight_apply', kernel.prod_apply', kernel.const_apply, lintegral_dirac]
      rotate_left
      · exact measurable_swap (measurable_left_prod_ico hs)
      · exact measurable_left_prod_ico hs
      · exact hs
      · exact measurable_ico_prod_right hs
      · exact hs
      congr
      · exact wtf3
      · ext y
        simp only [mem_preimage, mem_setOf_eq, Prod.swap_prod_mk]
        rw [wtf4]
    -- simplify LHS
    rw [itKernel_succ, ih, kernel.compProd_map_left, kernel.comap_comap, kernel.map_map,
      kernel.compProd_assoc', kernel.map_map, kernel.comap_comap]
    -- simplify RHS
    rw [itKernel_succ, kernel.comap_map_comm, kernel.comap_compProd, kernel.comap_comap,
      kernel.compProd_map_right, kernel.map_map]
    congr
    · ext1 x
      exact wtf
    · ext1 x
      exact wtf2 h_ne

/-- Informally `itMeasure' κ k x n` is a measure on `α 0 × ⋯ × α (n - 1)`,
defined as `S ↦ (κ k ⊗ₖ ⋯ ⊗ₖ κ (n - 1))(x)({y | (x, y) ∈ S})`,
where `k : ℕ` and `x : α 0 × ⋯ × α (k - 1)` are fixed.

We are primarily interested in the case `k = 0`, `x = ()` although a general
definition is used for the proof. -/
noncomputable def itMeasure' (κ : ∀ n : ℕ, kernel (∀ i : Fin n, α i) (α n)) (k : ℕ)
    (x : ∀ i : Fin k, α i) (n : ℕ) : Measure (∀ i : Fin n, α i) :=
  (itKernel κ k n x).map (fin_prod_ico' k n x)

theorem itMeasure'_apply {k x n s} (hs : MeasurableSet s) :
    itMeasure' κ k x n s = itKernel κ k n x (fin_prod_ico' k n x ⁻¹' s) := by
  exact Measure.map_apply measurable_fin_prod_ico' hs

theorem itMeasure'_measurable_coe {k n s} (hs : MeasurableSet s) :
    Measurable fun x ↦ itMeasure' κ k x n s := by
  simp_rw [itMeasure'_apply hs]
  change Measurable fun x ↦ itKernel κ k n x (Prod.mk x ⁻¹' (fin_prod_ico k n ⁻¹' s))
  apply kernel.measurable_kernel_prod_mk_left
  exact measurable_fin_prod_ico hs

theorem itMeasure'_measurable {k} :
    Measurable (itMeasure' κ k) :=
  measurable_pi_lambda _ fun _ ↦
    Measure.measurable_of_measurable_coe _ fun _ ↦ itMeasure'_measurable_coe

instance {k x n} : IsProbabilityMeasure (itMeasure' κ k x n) :=
  isProbabilityMeasure_map <| Measurable.aemeasurable <|
    measurable_pi_lambda _ fun _ ↦ Measurable.eval measurable_fin_prod_ico'

/-- `itMeasure' κ k x n` is a projective family wrt `n`. -/
theorem isProjectiveMeasureFamilyNat_itMeasure' {k : ℕ} {x} :
    IsProjectiveMeasureFamilyNat (itMeasure' κ k x) := by
  intro n
  unfold itMeasure'
  rw [← kernel.fst_compProd (itKernel κ k n) (kernel.comap (κ n) (fin_prod_ico k n) measurable_fin_prod_ico),
    kernel.fst_apply, itKernel_succ, kernel.map_apply, Measure.map_map, Measure.map_map, Measure.map_map]
  · congr; ext
    simp [fin_prod_ico', fin_prod_ico, ico_prod_right]
  · unfold Function.comp
    exact measurable_pi_lambda _ fun _ ↦ Measurable.eval measurable_fin_prod_ico'
  · exact measurable_pi_lambda _ fun _ ↦ Measurable.eval measurable_ico_prod_right
  · exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  · exact measurable_fin_prod_ico'
  · exact measurable_fin_prod_ico'
  · exact measurable_fst

/-- The measure on `α 0 × ⋯ × α (n - 1)` defined by `κ 0 ⊗ₖ ⋯ ⊗ₖ κ (n - 1)`.

i.e. the case of `itMeasure'` where `k = 0`, `x = ()`. -/
noncomputable def itMeasure (κ : ∀ n : ℕ, kernel (∀ i : Fin n, α i) (α n)) (n : ℕ) :
    Measure (∀ i : Fin n, α i) :=
  match n with
  | 0 => Measure.dirac default
  | n + 1 => (itMeasure κ n ⊗ₘ κ n).map (fin_prod_right n)

theorem itMeasure_eq_itMeasure'_zero : itMeasure κ = itMeasure' κ 0 default := by
  ext1 n; symm
  induction' n with n ih
  · exact Measure.map_dirac measurable_fin_prod_ico' _
  · rw [itMeasure', itKernel, kernel.map_apply,
      Measure.map_map measurable_fin_prod_ico' measurable_ico_prod_right]
    rw [itMeasure, ← ih, itMeasure', Measure.compProd_map_left measurable_fin_prod_ico',
      Measure.map_map measurable_fin_prod_right (measurable_fin_prod_ico'.prod_map measurable_id),
      wtf5]
    congr
    ext as hs
    rw [kernel.compProd_apply _ _ _ hs, Measure.compProd_apply hs]
    rfl

instance {n} : IsProbabilityMeasure (itMeasure κ n) := by
  rw [itMeasure_eq_itMeasure'_zero]
  infer_instance

/-- `itMeasure κ n` is a projective family wrt `n`. -/
theorem isProjectiveMeasureFamilyNat_itMeasure :
    IsProjectiveMeasureFamilyNat (itMeasure κ) := by
  rw [itMeasure_eq_itMeasure'_zero]
  exact isProjectiveMeasureFamilyNat_itMeasure'

variable [∀ i, Nonempty (α i)]

/-- The content on cylinder sets of `α 0 × α 1 × ⋯` induced by the
projective family `itMeasure' κ k x`.

Note that we are primarily interested in the case `k = 0`, `x = ()` although a
general definition over `k`, `x` is needed for the proof. -/
noncomputable def itContent' (κ : ∀ n : ℕ, kernel (∀ i : Fin n, α i) (α n)) [∀ i, IsMarkovKernel (κ i)]
    (k : ℕ) (x : ∀ i : Fin k, α i) : AddContent (cylinders α) :=
  kolContent (P := toFinsetNat (itMeasure' κ k x))
    isProjectiveMeasureFamilyNat_itMeasure'.isProjectiveMeasureFamily_toFinsetNat

variable [∀ i, IsMarkovKernel (κ i)]

theorem itContent'_congr {k x s} (hs : s ∈ cylinders α) {n : ℕ}
    {S : Set (∀ i : Fin n, α i)} (hs_eq : s = cylinderNat n S) (hS : MeasurableSet S) :
    itContent' κ k x s = itMeasure' κ k x n S := by
  rw [itContent', kolContent_eq _ hs, kolmogorovFun, toFinsetNat, Measure.map_apply]
  · apply isProjectiveMeasureFamilyNat_itMeasure'.congr_cylinderNat
      ((measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _) (cylinders.measurableSet hs)) hS
    conv_rhs => rw [← hs_eq, cylinders.eq_cylinderNat hs]
    rfl
  · exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  · exact cylinders.measurableSet hs

theorem itContent'_eq {k x s} (hs : s ∈ cylinders α) :
    itContent' κ k x s = itMeasure' κ k x (cylinders.nat hs) (cylinders.setFin hs) :=
  itContent'_congr hs (cylinders.eq_cylinderNat hs) (cylinders.measurableSet_setFin hs)

theorem itContent'_measurable_coe {k s} (hs : s ∈ cylinders α) :
    Measurable (fun x ↦ itContent' κ k x s) := by
  simp_rw [itContent'_eq hs]
  exact itMeasure'_measurable_coe (κ := κ) (cylinders.measurableSet_setFin hs)

theorem itContent'_eq_lintegral_succ {k x s} (hs : s ∈ cylinders α) :
    itContent' κ k x s =
      ∫⁻ a : α k, itContent' κ (k + 1) (fin_prod_right k (x, a)) s ∂κ k x := by
  have hs' := cylinders.measurableSet_setFin hs
  rw [itContent'_eq hs, itMeasure'_apply hs', itKernel_succ_left,
    kernel.map_apply', kernel.compProd_apply]
  congr; ext a
  rw [kernel.comap_apply, itContent'_eq, itMeasure'_apply hs']
  rotate_left
  · exact measurable_left_prod_ico (measurable_fin_prod_ico' hs')
  · exact measurable_fin_prod_ico' hs'
  congr
  unfold fin_prod_ico'
  simp_rw [← wtf]; rfl

theorem itContent'_of_not_mem {s} (hs : s ∈ cylinders α)
    {x : ∀ i : Fin (cylinders.nat hs), α i} (h : x ∉ cylinders.setFin hs) :
    itContent' κ (cylinders.nat hs) x s = 0 := by
  rw [itContent'_eq hs, itMeasure'_apply (cylinders.measurableSet_setFin hs)]
  unfold fin_prod_ico'
  simp only [wtf3, h, not_false_eq_true, preimage_const_of_not_mem, measure_empty]

/-- The content (which is in fact a measure as shown later) on cylinder sets of
`α 0 × α 1 × ⋯` induced by the projective family `itMeasure κ`.

i.e. the case of `itContent'` where `k = 0`, `x = ()`. -/
noncomputable def itContent (κ : ∀ n : ℕ, kernel (∀ i : Fin n, α i) (α n)) [∀ i, IsMarkovKernel (κ i)] :
    AddContent (cylinders α) :=
  kolContent (P := toFinsetNat (itMeasure κ))
    isProjectiveMeasureFamilyNat_itMeasure.isProjectiveMeasureFamily_toFinsetNat

theorem itContent_eq_itContent'_zero_default :
    itContent κ = itContent' κ 0 default := by
  unfold itContent
  simp only [itMeasure_eq_itMeasure'_zero]
  rfl

theorem itContent_congr {s} (hs : s ∈ cylinders α) {n : ℕ}
    {S : Set (∀ i : Fin n, α i)} (hs_eq : s = cylinderNat n S) (hS : MeasurableSet S) :
    itContent κ s = itMeasure κ n S := by
  rw [itContent_eq_itContent'_zero_default, itMeasure_eq_itMeasure'_zero]
  exact itContent'_congr hs hs_eq hS

theorem itContent_eq {s} (hs : s ∈ cylinders α) :
    itContent κ s = itMeasure κ (cylinders.nat hs) (cylinders.setFin hs) :=
  itContent_congr hs (cylinders.eq_cylinderNat hs) (cylinders.measurableSet_setFin hs)

section SigmaAdditive

open Filter in
open scoped Topology in
theorem itContent_sigma_additive
    ⦃f : ℕ → Set (∀ i, α i)⦄ (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α)
    (h_disj : Pairwise (Disjoint on f)) :
    itContent κ (⋃ i, f i) = ∑' i, itContent κ (f i) := by
  -- it suffices to show continuity at 0
  refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders _ ?_ ?_ hf hf_Union h_disj
  · intro s hs
    rw [itContent_eq hs]
    exact measure_ne_top _ _
  rw [itContent_eq_itContent'_zero_default]
  intro s hs h_anti h_inter

  -- set up limit for each k
  have h_anti' k x : Antitone (fun n ↦ itContent' κ k x (s n)) := fun m n h ↦
      (itContent' κ k x).mono setSemiringCylinders (hs n) (hs m) (h_anti h)
  have h_tendsto k x := tendsto_atTop_iInf (h_anti' k x)
  let μ k x := ⨅ n, itContent' κ k x (s n)

  -- iterative relation of the limits using dominated convergence
  have hμ_succ k x : μ k x = ∫⁻ a : α k, μ (k + 1) (fin_prod_right k (x, a)) ∂κ k x := by
    apply tendsto_nhds_unique' inferInstance (h_tendsto k x)
    convert tendsto_lintegral_of_dominated_convergence
      (μ := κ k x) (F := fun n a ↦ itContent' κ (k + 1) (fin_prod_right k (x, a)) (s n))
      (f := fun a ↦ μ (k + 1) (fin_prod_right k (x, a))) (bound := 1)
      (fun n ↦ (itContent'_measurable_coe (hs n)).comp (measurable_fin_prod_right.comp measurable_prod_mk_left))
      (fun n ↦ eventually_of_forall fun a ↦ by simp_rw [itContent'_eq (hs n)]; exact prob_le_one)
      (by simp) (eventually_of_forall fun a ↦ h_tendsto (k + 1) _)
    exact itContent'_eq_lintegral_succ (hs _)

  -- assume for contradiction the limit is nonzero, hence positive
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε εpos
  by_contra! hlt
  replace hlt : μ 0 default > 0 := by
    refine lt_iInf_iff.mpr ⟨ε, εpos, fun n ↦ ?_⟩
    have ⟨_, h, hm⟩ := hlt n
    exact hm.le.trans (h_anti' 0 default h)

  -- contruct contradicting sequence seq
  have step k x (h : μ k x > 0) : ∃ a, μ (k + 1) (fin_prod_right k (x, a)) > 0 := by
    rw [hμ_succ] at h
    by_contra! h0
    simp_rw [nonpos_iff_eq_zero] at h0
    simp [h0] at h
  let seqs (k : ℕ) : {x : ∀ i : Fin k, α i // μ k x > 0} :=
    k.rec ⟨default, hlt⟩ fun k ⟨x, hx⟩ ↦
      ⟨fin_prod_right k (x, (step k x hx).choose), (step k x hx).choose_spec⟩
  have seqs_succ k : (seqs (k + 1)).1 =
    fin_prod_right k ((seqs k).1, (step k (seqs k).1 (seqs k).2).choose) := rfl
  let seq (k : ℕ) : α k := (seqs (k + 1)).1 ⟨k, k.lt_succ_self⟩
  have seq_eq_seqs k n (h : k < n) : seq k = (seqs n).1 ⟨k, h⟩ := by
    induction' n, h using Nat.le_induction with n h ih
    · rfl
    · rw [seqs_succ, ih, fin_prod_right_of_lt]

  -- evaluate sequence on k = cylinders.nat (hs n)
  have hmem n : seq ∈ s n := by
    let k := cylinders.nat (hs n)
    suffices (seqs k).1 ∈ cylinders.setFin (hs n) by
      rw [cylinders.eq_cylinderNat (hs n), cylinderNat, mem_preimage]
      convert this
      rw [seq_eq_seqs]
    have : itContent' κ k (seqs k).1 (s n) ≠ 0 :=
      ((seqs k).2.trans_le (iInf_le _ _)).ne'
    contrapose! this
    exact itContent'_of_not_mem (hs n) this

  -- contradiction: seq is in the empty intersection
  have ⟨n, hn⟩ := iInter_eq_empty_iff.mp h_inter seq
  exact hn (hmem n)

theorem itContent_sigma_subadditive
    ⦃f : ℕ → Set (∀ i, α i)⦄ (hf : ∀ i, f i ∈ cylinders α) (hf_Union : (⋃ i, f i) ∈ cylinders α) :
    itContent κ (⋃ i, f i) ≤ ∑' i, itContent κ (f i) :=
  (itContent κ).sigma_subadditive_of_sigma_additive setRing_cylinders
    itContent_sigma_additive f hf hf_Union

end SigmaAdditive

/-- The measure on `α 0 × α 1 × ⋯` from `itContent`. -/
noncomputable def itLimit (κ : ∀ n : ℕ, kernel (∀ i : Fin n, α i) (α n))
    [∀ i, IsMarkovKernel (κ i)] : Measure (∀ i, α i) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (itContent κ) itContent_sigma_subadditive

/-- `itLimit κ` is a projective limit. -/
theorem isProjectiveLimitNat_itLimit :
    IsProjectiveLimitNat (itLimit κ) (itMeasure κ) := by
  intro n
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  have h_mem : (fun (x : ∀ i, α i) (i : Fin n) ↦ x i) ⁻¹' s ∈ cylinders α :=
    cylinderNat_mem_cylinders hs
  rw [itLimit, Measure.ofAddContent_eq _ _ _ _ h_mem, itContent_congr h_mem rfl hs]

theorem itLimit_cylinderNat {n} {s : Set (∀ i : Fin n, α i)} (hs : MeasurableSet s) :
    itLimit κ (cylinderNat n s) = itMeasure κ n s :=
  isProjectiveLimitNat_itLimit.measure_cylinderNat hs

theorem itLimit_of_mem_cylinders {s : Set (∀ i, α i)} (hs : s ∈ cylinders α) :
    itLimit κ s = itMeasure κ (cylinders.nat hs) (cylinders.setFin hs) := by
  conv_lhs => rw [cylinders.eq_cylinderNat hs]
  exact itLimit_cylinderNat (cylinders.measurableSet_setFin hs)

instance itLimit_isProbabilityMeasure : IsProbabilityMeasure (itLimit κ) := by
  constructor
  rw [← cylinderNat_univ 0, itLimit_cylinderNat .univ]
  exact measure_univ

end ITKernel
