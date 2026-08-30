/-
Copyright (c) 2026 Disk Rigidity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Disk Rigidity Authors
-/

module

public import DiskRigidity.Operator.CrouzeixConstant
public import DiskRigidity.Operator.NumericalRangeConvexity
public import Mathlib.Data.Matrix.Block

/-!
# Direct sums

This file formalizes the direct-sum part of Lemma 2.1 in the manuscript.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace DiskRigidity.Operator

variable {m n : Type*}

/-- The binary block direct sum of two square matrices. -/
def matrixDirectSum (A : SquareMatrix m) (B : SquareMatrix n) :
    SquareMatrix (m ⊕ n) :=
  Matrix.fromBlocks A 0 0 B

/-- The left component of a vector indexed by a sum. -/
def sumVectorLeft (x : EuclideanVector (m ⊕ n)) : EuclideanVector m :=
  WithLp.toLp 2 (fun i ↦ x (Sum.inl i))

/-- The right component of a vector indexed by a sum. -/
def sumVectorRight (x : EuclideanVector (m ⊕ n)) : EuclideanVector n :=
  WithLp.toLp 2 (fun i ↦ x (Sum.inr i))

/-- Embed a vector into the left summand. -/
def sumVectorInl (x : EuclideanVector m) : EuclideanVector (m ⊕ n) :=
  WithLp.toLp 2 (Sum.elim (fun i ↦ x i) (fun _ ↦ 0))

/-- Embed a vector into the right summand. -/
def sumVectorInr (x : EuclideanVector n) : EuclideanVector (m ⊕ n) :=
  WithLp.toLp 2 (Sum.elim (fun _ ↦ 0) (fun i ↦ x i))

@[simp] theorem sumVectorLeft_apply (x : EuclideanVector (m ⊕ n)) (i : m) :
    sumVectorLeft x i = x (Sum.inl i) :=
  rfl

@[simp] theorem sumVectorRight_apply (x : EuclideanVector (m ⊕ n)) (i : n) :
    sumVectorRight x i = x (Sum.inr i) :=
  rfl

@[simp] theorem sumVectorLeft_inl (x : EuclideanVector m) :
    sumVectorLeft (sumVectorInl (n := n) x) = x := by
  ext i
  rfl

@[simp] theorem sumVectorRight_inl (x : EuclideanVector m) :
    sumVectorRight (sumVectorInl (n := n) x) = 0 := by
  ext i
  rfl

@[simp] theorem sumVectorLeft_inr (x : EuclideanVector n) :
    sumVectorLeft (sumVectorInr (m := m) x) = 0 := by
  ext i
  rfl

@[simp] theorem sumVectorRight_inr (x : EuclideanVector n) :
    sumVectorRight (sumVectorInr (m := m) x) = x := by
  ext i
  rfl

variable [Fintype m] [Fintype n]

/-- Normalize a nonzero Euclidean vector. -/
def normalizedVector (x : EuclideanVector m) : EuclideanVector m :=
  (‖x‖ : ℂ)⁻¹ • x

/-- Squared Euclidean norm splits over the two summands. -/
theorem sumVector_norm_sq (x : EuclideanVector (m ⊕ n)) :
    ‖x‖ ^ 2 = ‖sumVectorLeft x‖ ^ 2 + ‖sumVectorRight x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type,
    sumVectorLeft_apply, sumVectorRight_apply]

/-- The coordinate embeddings are isometries. -/
theorem norm_sumVectorInl (x : EuclideanVector m) :
    ‖sumVectorInl (n := n) x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.norm_sq_eq, sumVectorInl, Fintype.sum_sum_type]

/-- The coordinate embeddings are isometries. -/
theorem norm_sumVectorInr (x : EuclideanVector n) :
    ‖sumVectorInr (m := m) x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.norm_sq_eq, sumVectorInr, Fintype.sum_sum_type]

/-- A nonzero vector becomes a unit vector after normalization. -/
theorem norm_normalizedVector {x : EuclideanVector m} (hx : x ≠ 0) :
    ‖normalizedVector x‖ = 1 := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [normalizedVector, norm_smul, hnorm]

/-- Recover the original vector from its normalization. -/
theorem norm_smul_normalizedVector {x : EuclideanVector m} (hx : x ≠ 0) :
    (‖x‖ : ℂ) • normalizedVector x = x := by
  have hnorm : (‖x‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hx
  simp [normalizedVector, hnorm]

/-- A block direct sum acts independently on its two components. -/
theorem matrixDirectSum_mulVec (A : SquareMatrix m) (B : SquareMatrix n)
    (x : EuclideanVector (m ⊕ n)) :
    (matrixDirectSum A B).mulVec x =
      Sum.elim (A.mulVec (sumVectorLeft x)) (B.mulVec (sumVectorRight x)) := by
  rw [matrixDirectSum, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  rfl

variable [DecidableEq m] [DecidableEq n]

/-- A quadratic form scales by the squared norm under normalization. -/
theorem inner_eq_norm_sq_smul_inner_normalized
    (A : SquareMatrix m) {x : EuclideanVector m} (hx : x ≠ 0) :
    ⟪x, euclideanOperator A x⟫_ℂ =
      ‖x‖ ^ 2 • ⟪normalizedVector x,
        euclideanOperator A (normalizedVector x)⟫_ℂ := by
  conv_lhs => rw [← norm_smul_normalizedVector hx]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.real_smul, pow_two]
  ring

/-- The numerical-range quadratic form splits over a block direct sum. -/
theorem inner_matrixDirectSum (A : SquareMatrix m) (B : SquareMatrix n)
    (x : EuclideanVector (m ⊕ n)) :
    ⟪x, euclideanOperator (matrixDirectSum A B) x⟫_ℂ =
      ⟪sumVectorLeft x, euclideanOperator A (sumVectorLeft x)⟫_ℂ +
        ⟪sumVectorRight x, euclideanOperator B (sumVectorRight x)⟫_ℂ := by
  change
    ⟪x, ((Matrix.toEuclideanCLM (n := m ⊕ n) (𝕜 := ℂ))
      (matrixDirectSum A B)) x⟫_ℂ =
      ⟪sumVectorLeft x, ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ))
        A) (sumVectorLeft x)⟫_ℂ +
        ⟪sumVectorRight x, ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
          B) (sumVectorRight x)⟫_ℂ
  simp only [PiLp.inner_apply, Matrix.ofLp_toEuclideanCLM,
    Fintype.sum_sum_type, matrixDirectSum_mulVec, sumVectorLeft_apply,
    sumVectorRight_apply, Sum.elim_inl, Sum.elim_inr]

@[simp] theorem sumVectorLeft_euclideanOperator_matrixDirectSum
    (A : SquareMatrix m) (B : SquareMatrix n) (x : EuclideanVector (m ⊕ n)) :
    sumVectorLeft (euclideanOperator (matrixDirectSum A B) x) =
      euclideanOperator A (sumVectorLeft x) := by
  ext i
  change ((matrixDirectSum A B).mulVec x) (Sum.inl i) =
    (A.mulVec (sumVectorLeft x)) i
  rw [matrixDirectSum_mulVec]
  rfl

@[simp] theorem sumVectorRight_euclideanOperator_matrixDirectSum
    (A : SquareMatrix m) (B : SquareMatrix n) (x : EuclideanVector (m ⊕ n)) :
    sumVectorRight (euclideanOperator (matrixDirectSum A B) x) =
      euclideanOperator B (sumVectorRight x) := by
  ext i
  change ((matrixDirectSum A B).mulVec x) (Sum.inr i) =
    (B.mulVec (sumVectorRight x)) i
  rw [matrixDirectSum_mulVec]
  rfl

/-- Matrix polynomial evaluation preserves binary block direct sums. -/
theorem polynomialEval_matrixDirectSum (p : Polynomial ℂ)
    (A : SquareMatrix m) (B : SquareMatrix n) :
    polynomialEval p (matrixDirectSum A B) =
      matrixDirectSum (polynomialEval p A) (polynomialEval p B) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [polynomialEval, map_add] at hp hq ⊢
      rw [hp, hq]
      simp [matrixDirectSum, Matrix.fromBlocks_add]
  | monomial k a =>
      simp [polynomialEval, matrixDirectSum, Polynomial.aeval_def,
        Matrix.fromBlocks_diagonal_pow, Matrix.fromBlocks_smul,
        Algebra.algebraMap_eq_smul_one]

/-- The operator norm of a block direct sum is at most the larger block norm. -/
theorem norm_matrixDirectSum_le_max (A : SquareMatrix m) (B : SquareMatrix n) :
    ‖matrixDirectSum A B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [matrix_norm_eq_operator_norm, matrix_norm_eq_operator_norm,
    matrix_norm_eq_operator_norm]
  refine ContinuousLinearMap.opNorm_le_bound _
    ((norm_nonneg (euclideanOperator A)).trans (le_max_left _ _)) ?_
  intro x
  have hleft :
      ‖euclideanOperator A (sumVectorLeft x)‖ ≤
        max ‖euclideanOperator A‖ ‖euclideanOperator B‖ *
          ‖sumVectorLeft x‖ :=
    (euclideanOperator A).le_opNorm (sumVectorLeft x) |>.trans <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hright :
      ‖euclideanOperator B (sumVectorRight x)‖ ≤
        max ‖euclideanOperator A‖ ‖euclideanOperator B‖ *
          ‖sumVectorRight x‖ :=
    (euclideanOperator B).le_opNorm (sumVectorRight x) |>.trans <|
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [sumVector_norm_sq]
  simp only [sumVectorLeft_euclideanOperator_matrixDirectSum,
    sumVectorRight_euclideanOperator_matrixDirectSum]
  calc
    ‖euclideanOperator A (sumVectorLeft x)‖ ^ 2 +
        ‖euclideanOperator B (sumVectorRight x)‖ ^ 2 ≤
      (max ‖euclideanOperator A‖ ‖euclideanOperator B‖ *
          ‖sumVectorLeft x‖) ^ 2 +
        (max ‖euclideanOperator A‖ ‖euclideanOperator B‖ *
          ‖sumVectorRight x‖) ^ 2 := by
            gcongr
    _ = (max ‖euclideanOperator A‖ ‖euclideanOperator B‖) ^ 2 *
        (‖sumVectorLeft x‖ ^ 2 + ‖sumVectorRight x‖ ^ 2) := by ring
    _ = (max ‖euclideanOperator A‖ ‖euclideanOperator B‖ * ‖x‖) ^ 2 := by
      rw [← sumVector_norm_sq]
      ring

/-- Each left-block numerical-range point remains a numerical-range point of
the direct sum. -/
theorem numericalRange_subset_matrixDirectSum_left
    (A : SquareMatrix m) (B : SquareMatrix n) :
    numericalRange A ⊆ numericalRange (matrixDirectSum A B) := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨sumVectorInl (n := n) x, norm_sumVectorInl x |>.trans hx, ?_⟩
  rw [inner_matrixDirectSum]
  simp

/-- Each right-block numerical-range point remains a numerical-range point of
the direct sum. -/
theorem numericalRange_subset_matrixDirectSum_right
    (A : SquareMatrix m) (B : SquareMatrix n) :
    numericalRange B ⊆ numericalRange (matrixDirectSum A B) := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨sumVectorInr (m := m) x, norm_sumVectorInr x |>.trans hx, ?_⟩
  rw [inner_matrixDirectSum]
  simp

/-- The convex hull of the two block numerical ranges is contained in the
numerical range of the direct sum. -/
theorem convexHull_union_numericalRange_subset_matrixDirectSum
    (A : SquareMatrix m) (B : SquareMatrix n) :
    convexHull ℝ (numericalRange A ∪ numericalRange B) ⊆
      numericalRange (matrixDirectSum A B) := by
  apply convexHull_min
  · exact Set.union_subset
      (numericalRange_subset_matrixDirectSum_left A B)
      (numericalRange_subset_matrixDirectSum_right A B)
  · exact numericalRange_convex (matrixDirectSum A B)

/-- Every direct-sum numerical-range value is a convex combination of one
value from each block. -/
theorem numericalRange_matrixDirectSum_subset_convexHull_union
    (A : SquareMatrix m) (B : SquareMatrix n) :
    numericalRange (matrixDirectSum A B) ⊆
      convexHull ℝ (numericalRange A ∪ numericalRange B) := by
  rintro z ⟨x, hx, rfl⟩
  have hsum :
      ‖sumVectorLeft x‖ ^ 2 + ‖sumVectorRight x‖ ^ 2 = 1 := by
    rw [← sumVector_norm_sq x, hx]
    norm_num
  by_cases hleft : sumVectorLeft x = 0
  · have hrightNorm : ‖sumVectorRight x‖ = 1 := by
      have hsquare : ‖sumVectorRight x‖ ^ 2 = 1 := by
        simpa [hleft] using hsum
      nlinarith [norm_nonneg (sumVectorRight x)]
    rw [inner_matrixDirectSum, hleft]
    simp only [map_zero, inner_zero_left, zero_add]
    exact subset_convexHull ℝ _ <| Set.mem_union_right _
      ⟨sumVectorRight x, hrightNorm, rfl⟩
  by_cases hright : sumVectorRight x = 0
  · have hleftNorm : ‖sumVectorLeft x‖ = 1 := by
      have hsquare : ‖sumVectorLeft x‖ ^ 2 = 1 := by
        simpa [hright] using hsum
      nlinarith [norm_nonneg (sumVectorLeft x)]
    rw [inner_matrixDirectSum, hright]
    simp only [map_zero, inner_zero_left, add_zero]
    exact subset_convexHull ℝ _ <| Set.mem_union_left _
      ⟨sumVectorLeft x, hleftNorm, rfl⟩
  · rw [inner_matrixDirectSum,
      inner_eq_norm_sq_smul_inner_normalized A hleft,
      inner_eq_norm_sq_smul_inner_normalized B hright]
    apply (convex_convexHull ℝ (numericalRange A ∪ numericalRange B))
    · exact subset_convexHull ℝ _ <| Set.mem_union_left _
        ⟨normalizedVector (sumVectorLeft x), norm_normalizedVector hleft, rfl⟩
    · exact subset_convexHull ℝ _ <| Set.mem_union_right _
        ⟨normalizedVector (sumVectorRight x), norm_normalizedVector hright, rfl⟩
    · exact sq_nonneg _
    · exact sq_nonneg _
    · exact hsum

/-- Binary form of Lemma 2.1(4): the numerical range of a direct sum is the
convex hull of the block numerical ranges. -/
theorem numericalRange_matrixDirectSum (A : SquareMatrix m) (B : SquareMatrix n) :
    numericalRange (matrixDirectSum A B) =
      convexHull ℝ (numericalRange A ∪ numericalRange B) :=
  Set.Subset.antisymm
    (numericalRange_matrixDirectSum_subset_convexHull_union A B)
    (convexHull_union_numericalRange_subset_matrixDirectSum A B)

/-- The index type of a nonempty recursively nested direct sum of `k + 1`
copies of `n`. -/
def FinDirectSumIndex (n : Type*) : ℕ → Type _
  | 0 => n
  | k + 1 => n ⊕ FinDirectSumIndex n k

instance {d : Type*} [Fintype d] (k : ℕ) :
    Fintype (FinDirectSumIndex d k) := by
  induction k with
  | zero => simp only [FinDirectSumIndex]; infer_instance
  | succ k ih => simp only [FinDirectSumIndex]; infer_instance

instance {d : Type*} [DecidableEq d] (k : ℕ) :
    DecidableEq (FinDirectSumIndex d k) := by
  induction k with
  | zero => simp only [FinDirectSumIndex]; infer_instance
  | succ k ih => simp only [FinDirectSumIndex]; infer_instance

instance {d : Type*} [Nonempty d] (k : ℕ) :
    Nonempty (FinDirectSumIndex d k) := by
  induction k with
  | zero => simp only [FinDirectSumIndex]; infer_instance
  | succ k ih => simp only [FinDirectSumIndex]; infer_instance

/-- The recursively nested direct sum of a nonempty `Fin (k + 1)`-family
of square matrices. -/
def matrixFinDirectSum : ∀ k : ℕ,
    (Fin (k + 1) → SquareMatrix n) → SquareMatrix (FinDirectSumIndex n k)
  | 0, A => A 0
  | k + 1, A => matrixDirectSum (A 0) (matrixFinDirectSum k (Fin.tail A))

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem matrixFinDirectSum_zero (A : Fin 1 → SquareMatrix n) :
    matrixFinDirectSum 0 A = A 0 :=
  rfl

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem matrixFinDirectSum_succ (k : ℕ)
    (A : Fin (k + 2) → SquareMatrix n) :
    matrixFinDirectSum (k + 1) A =
      matrixDirectSum (A 0) (matrixFinDirectSum k (Fin.tail A)) :=
  rfl

/-- Split a union indexed by `Fin (k + 1)` into its zeroth member and its
tail. -/
theorem iUnion_fin_succ {a : Type*} {k : ℕ}
    (S : Fin (k + 1) → Set a) :
    (⋃ i, S i) = S 0 ∪ ⋃ j : Fin k, S j.succ := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine Fin.cases (motive := fun i ↦ x ∈ S i →
      x ∈ S 0 ∪ ⋃ j : Fin k, S j.succ) ?_ ?_ i hi
    · intro h
      exact Or.inl h
    · intro j h
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩)
  · intro hx
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨0, hx⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨j.succ, hj⟩

/-- Taking a convex hull absorbs a convex hull on one side of a union. -/
theorem convexHull_union_convexHull {s t : Set ℂ} :
    convexHull ℝ (s ∪ convexHull ℝ t) = convexHull ℝ (s ∪ t) := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · apply Set.union_subset
      · exact Set.subset_union_left.trans (subset_convexHull ℝ (s ∪ t))
      · apply convexHull_min
        · exact Set.subset_union_right.trans (subset_convexHull ℝ (s ∪ t))
        · exact convex_convexHull ℝ _
    · exact convex_convexHull ℝ _
  · apply convexHull_mono
    apply Set.union_subset
    · intro x hx
      exact Or.inl hx
    · intro x hx
      exact Or.inr (subset_convexHull ℝ t hx)

/-- Finite nonempty form of Lemma 2.1(4): the numerical range of an
`Fin (k + 1)`-indexed direct sum is the convex hull of the union of all block
numerical ranges. -/
theorem numericalRange_matrixFinDirectSum (k : ℕ)
    (A : Fin (k + 1) → SquareMatrix n) :
    numericalRange (matrixFinDirectSum k A) =
      convexHull ℝ (⋃ i, numericalRange (A i)) := by
  induction k with
  | zero =>
      rw [matrixFinDirectSum_zero, iUnion_fin_succ]
      simp only [Set.iUnion_of_empty, Set.union_empty]
      exact (numericalRange_convex (A 0)).convexHull_eq.symm
  | succ k ih =>
      rw [matrixFinDirectSum_succ]
      change numericalRange
        (matrixDirectSum (A 0) (matrixFinDirectSum k (Fin.tail A))) = _
      rw [numericalRange_matrixDirectSum, ih (Fin.tail A),
        convexHull_union_convexHull]
      exact congrArg (convexHull ℝ)
        (iUnion_fin_succ (fun i ↦ numericalRange (A i))).symm

universe u

/-- The index type of a recursively nested direct sum whose `k + 1` blocks
may have different finite dimensions. -/
def FiniteFamilyDirectSumIndex :
    (k : ℕ) → (Fin (k + 1) → Type u) → Type u
  | 0, d => d 0
  | k + 1, d => d 0 ⊕ FiniteFamilyDirectSumIndex k (Fin.tail d)

instance finiteFamilyDirectSumIndexFintype
    (k : ℕ) (d : Fin (k + 1) → Type u) [∀ i, Fintype (d i)] :
    Fintype (FiniteFamilyDirectSumIndex k d) := by
  induction k with
  | zero =>
      simp only [FiniteFamilyDirectSumIndex]
      infer_instance
  | succ k ih =>
      simp only [FiniteFamilyDirectSumIndex]
      letI : ∀ j, Fintype ((Fin.tail d) j) := fun j =>
        show Fintype (d j.succ) from inferInstance
      letI : Fintype (FiniteFamilyDirectSumIndex k (Fin.tail d)) :=
        ih (Fin.tail d)
      infer_instance

instance finiteFamilyDirectSumIndexDecidableEq
    (k : ℕ) (d : Fin (k + 1) → Type u) [∀ i, DecidableEq (d i)] :
    DecidableEq (FiniteFamilyDirectSumIndex k d) := by
  induction k with
  | zero =>
      simp only [FiniteFamilyDirectSumIndex]
      infer_instance
  | succ k ih =>
      simp only [FiniteFamilyDirectSumIndex]
      letI : ∀ j, DecidableEq ((Fin.tail d) j) := fun j =>
        show DecidableEq (d j.succ) from inferInstance
      letI : DecidableEq (FiniteFamilyDirectSumIndex k (Fin.tail d)) :=
        ih (Fin.tail d)
      infer_instance

instance finiteFamilyDirectSumIndexNonempty
    (k : ℕ) (d : Fin (k + 1) → Type u) [∀ i, Nonempty (d i)] :
    Nonempty (FiniteFamilyDirectSumIndex k d) := by
  induction k with
  | zero =>
      simp only [FiniteFamilyDirectSumIndex]
      infer_instance
  | succ k ih =>
      simp only [FiniteFamilyDirectSumIndex]
      let _ : ∀ j, Nonempty ((Fin.tail d) j) := fun j =>
        show Nonempty (d j.succ) from inferInstance
      let _ : Nonempty (FiniteFamilyDirectSumIndex k (Fin.tail d)) :=
        ih (Fin.tail d)
      infer_instance

/-- The recursively nested direct sum of a nonempty finite family of square
matrices whose block dimensions may vary with the index. -/
def matrixFiniteFamilyDirectSum :
    (k : ℕ) → {d : Fin (k + 1) → Type u} →
      ((i : Fin (k + 1)) → SquareMatrix (d i)) →
        SquareMatrix (FiniteFamilyDirectSumIndex k d)
  | 0, _, A => A 0
  | k + 1, _, A => matrixDirectSum (A 0)
      (matrixFiniteFamilyDirectSum k (fun j => A j.succ))

@[simp] theorem matrixFiniteFamilyDirectSum_zero
    {d : Fin 1 → Type u} (A : (i : Fin 1) → SquareMatrix (d i)) :
    matrixFiniteFamilyDirectSum 0 A = A 0 :=
  rfl

@[simp] theorem matrixFiniteFamilyDirectSum_succ
    (k : ℕ) {d : Fin (k + 2) → Type u}
    (A : (i : Fin (k + 2)) → SquareMatrix (d i)) :
    matrixFiniteFamilyDirectSum (k + 1) A =
      matrixDirectSum (A 0)
        (matrixFiniteFamilyDirectSum k (fun j => A j.succ)) :=
  rfl

/-- Varying-dimension finite form of Lemma 2.1(4): the numerical range of a
nonempty finite direct sum is the convex hull of the union of all block
numerical ranges. -/
theorem numericalRange_matrixFiniteFamilyDirectSum
    (k : ℕ) {d : Fin (k + 1) → Type u}
    [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    [∀ i, Nonempty (d i)]
    (A : (i : Fin (k + 1)) → SquareMatrix (d i)) :
    numericalRange (matrixFiniteFamilyDirectSum k A) =
      convexHull ℝ (⋃ i, numericalRange (A i)) := by
  induction k with
  | zero =>
      rw [matrixFiniteFamilyDirectSum_zero, iUnion_fin_succ]
      simp only [Set.iUnion_of_empty, Set.union_empty]
      exact (numericalRange_convex (A 0)).convexHull_eq.symm
  | succ k ih =>
      rw [matrixFiniteFamilyDirectSum_succ]
      let _ : ∀ j, Fintype ((Fin.tail d) j) := fun j =>
        show Fintype (d j.succ) from inferInstance
      let _ : ∀ j, DecidableEq ((Fin.tail d) j) := fun j =>
        show DecidableEq (d j.succ) from inferInstance
      let _ : ∀ j, Nonempty ((Fin.tail d) j) := fun j =>
        show Nonempty (d j.succ) from inferInstance
      change numericalRange
        (matrixDirectSum (A 0)
          (matrixFiniteFamilyDirectSum k (fun j => A j.succ))) = _
      rw [numericalRange_matrixDirectSum]
      have htail :
          numericalRange
              (matrixFiniteFamilyDirectSum k (fun j => A j.succ)) =
            convexHull ℝ
              (⋃ j : Fin (k + 1), numericalRange (A j.succ)) := by
        exact ih (d := fun j : Fin (k + 1) => d j.succ)
          (fun j => A j.succ)
      rw [htail, convexHull_union_convexHull]
      exact congrArg (convexHull ℝ)
        (iUnion_fin_succ (fun i ↦ numericalRange (A i))).symm

variable [Nonempty m] [Nonempty n]

/-- The maximum modulus on either block is bounded by the maximum modulus on
the direct sum. -/
theorem maxPolynomialModulus_le_matrixDirectSum_left
    (A : SquareMatrix m) (B : SquareMatrix n) (p : Polynomial ℂ) :
    maxPolynomialModulus A p ≤ maxPolynomialModulus (matrixDirectSum A B) p := by
  obtain ⟨z, hz, hmax⟩ := exists_norm_eval_eq_maxPolynomialModulus A p
  rw [← hmax]
  exact norm_eval_le_maxPolynomialModulus (matrixDirectSum A B) p
    (numericalRange_subset_matrixDirectSum_left A B hz)

omit [Nonempty m] in
/-- The maximum modulus on either block is bounded by the maximum modulus on
the direct sum. -/
theorem maxPolynomialModulus_le_matrixDirectSum_right
    (A : SquareMatrix m) (B : SquareMatrix n) (p : Polynomial ℂ) :
    maxPolynomialModulus B p ≤ maxPolynomialModulus (matrixDirectSum A B) p := by
  obtain ⟨z, hz, hmax⟩ := exists_norm_eval_eq_maxPolynomialModulus B p
  rw [← hmax]
  exact norm_eval_le_maxPolynomialModulus (matrixDirectSum A B) p
    (numericalRange_subset_matrixDirectSum_right A B hz)

/-- The normalized family defining the Crouzeix constant is nonempty. -/
theorem normalizedPolynomialValues_nonempty (A : SquareMatrix m) :
    (normalizedPolynomialValues A).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · obtain ⟨z, hz, hmax⟩ := exists_norm_eval_eq_maxPolynomialModulus A 0
    have hzero : maxPolynomialModulus A 0 = 0 := by
      simpa using hmax.symm
    rw [hzero]
    norm_num
  · simp [polynomialEval]

omit [Nonempty m] in
/-- Every member of a bounded normalized family lies below its Crouzeix
constant. -/
theorem norm_polynomialEval_le_crouzeixConstant
    (A : SquareMatrix m) (hbounded : BddAbove (normalizedPolynomialValues A))
    (p : Polynomial ℂ) (hp : maxPolynomialModulus A p ≤ 1) :
    ‖polynomialEval p A‖ ≤ crouzeixConstant A := by
  exact le_csSup hbounded ⟨p, hp, rfl⟩

/-- Lemma 2.1(4), with the logically necessary boundedness facts for the two
real suprema made explicit.  The global sharp estimate supplies these facts
in the application. -/
theorem crouzeixConstant_matrixDirectSum_le
    (A : SquareMatrix m) (B : SquareMatrix n)
    (hA : BddAbove (normalizedPolynomialValues A))
    (hB : BddAbove (normalizedPolynomialValues B)) :
    crouzeixConstant (matrixDirectSum A B) ≤
      max (crouzeixConstant A) (crouzeixConstant B) := by
  apply csSup_le (normalizedPolynomialValues_nonempty (matrixDirectSum A B))
  rintro r ⟨p, hp, rfl⟩
  rw [polynomialEval_matrixDirectSum]
  refine (norm_matrixDirectSum_le_max _ _).trans ?_
  apply max_le_max
  · apply norm_polynomialEval_le_crouzeixConstant A hA p
    exact (maxPolynomialModulus_le_matrixDirectSum_left A B p).trans hp
  · apply norm_polynomialEval_le_crouzeixConstant B hB p
    exact (maxPolynomialModulus_le_matrixDirectSum_right A B p).trans hp

end DiskRigidity.Operator
