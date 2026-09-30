/-
Formalization of Sections 2 and 3 of
"The Erdős Conjecture for Primes Congruent to 7 modulo 36" (D. Paquin).

We work over ℕ (with truncated subtraction).  For `p = 36 * k + 7` we set
`x = 6 * k + 1` and prove:

Section 2 — the primary representation:
* `primary_rep`             : p − 1 = 6·(6k + 1)                        (Problem 2.1)
* `x_odd`, `x_coprime_three`: 6k + 1 is odd and coprime to 3            (Exercise 2.1(b))
* `p_sub_one_squarefree_iff`: p − 1 squarefree ↔ 6k + 1 squarefree      (Exercise 2.1(c))
* `obstructing_prime_ge_five`: q prime, q² ∣ p − 1 → q ≥ 5              (Exercise 2.1(d))

Section 3 — the key substitution:
* `p_sub_one_eq` … `p_sub_eight_eq`
    : the four candidate remainders as linear functions of x            (Exercise 3.1)
* `squarefree_iff₀` … `squarefree_iff₃`
    : the four squarefree equivalences                                  (Exercise 3.2(a–d))
* `candidate_iff` : some `p − 2^a` (a < 4) is squarefree ↔ one of
    x, 6x − 1, 2x − 1, 6x − 7 is squarefree                             (Exercise 3.2, conclusion)
* `one_power_of_candidate` : if one of the four candidates is squarefree,
    then p = 2^a + m with m squarefree and positive — i.e. the one-power
    conjecture holds for p.

The only point where ℕ-subtraction needs care is `p − 8` at `k = 0`
(p = 7): there both `p − 8` and `6x − 7` truncate to `0`, so the identity
still holds, and `0` is not squarefree, so no spurious representation is
produced (positivity of `m` is recovered from `Squarefree.ne_zero`).
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime

namespace Erdos7Mod36

/-! ### Section 2: the primary representation -/

/-- **Problem 2.1.** For `p = 36k + 7` we have `p − 2⁰ = p − 1 = 6(6k + 1)`. -/
theorem primary_rep (k : ℕ) : 36 * k + 7 - 1 = 6 * (6 * k + 1) := by
  omega

/-- **Exercise 2.1(b), first half.** `6k + 1` is odd. -/
theorem x_odd (k : ℕ) : Odd (6 * k + 1) :=
  ⟨3 * k, by ring⟩

/-- **Exercise 2.1(b), second half.** `6k + 1` is coprime to 3. -/
theorem x_coprime_three (k : ℕ) : Nat.Coprime (6 * k + 1) 3 :=
  Nat.coprime_comm.mp (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega))

/-- `6` is coprime to `6k + 1`. -/
theorem six_coprime_x (k : ℕ) : Nat.Coprime 6 (6 * k + 1) := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, Nat.coprime_mul_iff_left]
  exact ⟨Nat.prime_two.coprime_iff_not_dvd.mpr (by omega),
    Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)⟩

theorem squarefree_six : Squarefree (6 : ℕ) := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩

/-- **Exercise 2.1(c).** `p − 1` is squarefree iff `6k + 1` is squarefree. -/
theorem p_sub_one_squarefree_iff (k : ℕ) :
    Squarefree (36 * k + 7 - 1) ↔ Squarefree (6 * k + 1) := by
  rw [primary_rep, Nat.squarefree_mul_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨six_coprime_x k, squarefree_six, h⟩⟩

/-- **Exercise 2.1(d).** Any prime whose square divides `p − 1` is at least 5. -/
theorem obstructing_prime_ge_five (k q : ℕ) (hq : q.Prime)
    (h : q ^ 2 ∣ 36 * k + 7 - 1) : 5 ≤ q := by
  by_contra hlt
  push Not at hlt
  have h2 := hq.two_le
  interval_cases q
  · norm_num at h; omega   -- q = 2 : 4 ∤ 36k + 6
  · norm_num at h; omega   -- q = 3 : 9 ∤ 36k + 6
  · exact absurd hq (by norm_num)   -- q = 4 is not prime

/-! ### Section 3: the key substitution -/

/-- **Definition 3.1.** For `p = 36k + 7`, set `x = 6k + 1`. -/
def x (k : ℕ) : ℕ := 6 * k + 1

theorem x_def (k : ℕ) : x k = 6 * k + 1 := rfl

/-- **Exercise 3.1.** `p − 1 = 6x`. -/
theorem p_sub_one_eq (k : ℕ) : 36 * k + 7 - 1 = 6 * x k := by
  rw [x_def]; omega

/-- **Exercise 3.1.** `p − 2 = 6x − 1`. -/
theorem p_sub_two_eq (k : ℕ) : 36 * k + 7 - 2 = 6 * x k - 1 := by
  rw [x_def]; omega

/-- **Exercise 3.1.** `p − 4 = 3(2x − 1)`. -/
theorem p_sub_four_eq (k : ℕ) : 36 * k + 7 - 4 = 3 * (2 * x k - 1) := by
  rw [x_def]; omega

/-- **Exercise 3.1.** `p − 8 = 6x − 7`.  (At `k = 0` both sides truncate to `0`.) -/
theorem p_sub_eight_eq (k : ℕ) : 36 * k + 7 - 8 = 6 * x k - 7 := by
  rw [x_def]; omega

/-- **Exercise 3.2(a).** `p − 1` is squarefree iff `x` is squarefree. -/
theorem squarefree_iff₀ (k : ℕ) :
    Squarefree (36 * k + 7 - 1) ↔ Squarefree (x k) := by
  rw [x_def]
  exact p_sub_one_squarefree_iff k

/-- **Exercise 3.2(b).** `p − 2` is squarefree iff `6x − 1` is squarefree. -/
theorem squarefree_iff₁ (k : ℕ) :
    Squarefree (36 * k + 7 - 2) ↔ Squarefree (6 * x k - 1) := by
  rw [p_sub_two_eq]

/-- **Exercise 3.2(c).** `p − 4` is squarefree iff `2x − 1` is squarefree. -/
theorem squarefree_iff₂ (k : ℕ) :
    Squarefree (36 * k + 7 - 4) ↔ Squarefree (2 * x k - 1) := by
  rw [p_sub_four_eq, Nat.squarefree_mul_iff]
  refine ⟨fun h => h.2.2, fun h => ⟨?_, Nat.prime_three.prime.squarefree, h⟩⟩
  exact Nat.prime_three.coprime_iff_not_dvd.mpr (by rw [x_def]; omega)

/-- **Exercise 3.2(d).** `p − 8` is squarefree iff `6x − 7` is squarefree. -/
theorem squarefree_iff₃ (k : ℕ) :
    Squarefree (36 * k + 7 - 8) ↔ Squarefree (6 * x k - 7) := by
  rw [p_sub_eight_eq]

/-- **Exercise 3.2, conclusion.** Among the exponents `a = 0, 1, 2, 3`, some
remainder `p − 2^a` is squarefree iff one of `x, 6x − 1, 2x − 1, 6x − 7` is
squarefree. -/
theorem candidate_iff (k : ℕ) :
    (∃ a < 4, Squarefree (36 * k + 7 - 2 ^ a)) ↔
      Squarefree (x k) ∨ Squarefree (6 * x k - 1) ∨
        Squarefree (2 * x k - 1) ∨ Squarefree (6 * x k - 7) := by
  have e0 : (2 : ℕ) ^ 0 = 1 := by norm_num
  have e1 : (2 : ℕ) ^ 1 = 2 := by norm_num
  have e2 : (2 : ℕ) ^ 2 = 4 := by norm_num
  have e3 : (2 : ℕ) ^ 3 = 8 := by norm_num
  constructor
  · rintro ⟨a, ha, hsf⟩
    interval_cases a
    · rw [e0] at hsf; exact Or.inl ((squarefree_iff₀ k).mp hsf)
    · rw [e1] at hsf; exact Or.inr (Or.inl ((squarefree_iff₁ k).mp hsf))
    · rw [e2] at hsf; exact Or.inr (Or.inr (Or.inl ((squarefree_iff₂ k).mp hsf)))
    · rw [e3] at hsf; exact Or.inr (Or.inr (Or.inr ((squarefree_iff₃ k).mp hsf)))
  · rintro (h | h | h | h)
    · exact ⟨0, by norm_num, by rw [e0]; exact (squarefree_iff₀ k).mpr h⟩
    · exact ⟨1, by norm_num, by rw [e1]; exact (squarefree_iff₁ k).mpr h⟩
    · exact ⟨2, by norm_num, by rw [e2]; exact (squarefree_iff₂ k).mpr h⟩
    · exact ⟨3, by norm_num, by rw [e3]; exact (squarefree_iff₃ k).mpr h⟩

/-- If one of the four candidates is squarefree, then `p = 36k + 7` satisfies
the one-power conjecture: `p = 2^a + m` with `m` a squarefree positive integer. -/
theorem one_power_of_candidate (k : ℕ)
    (h : Squarefree (x k) ∨ Squarefree (6 * x k - 1) ∨
      Squarefree (2 * x k - 1) ∨ Squarefree (6 * x k - 7)) :
    ∃ a m : ℕ, 0 < m ∧ Squarefree m ∧ 36 * k + 7 = 2 ^ a + m := by
  obtain h | h | h | h := h
  · -- a = 0, m = 6x = p − 1
    refine ⟨0, 6 * x k, by rw [x_def]; omega, ?_, ?_⟩
    · exact Nat.squarefree_mul_iff.mpr ⟨six_coprime_x k, squarefree_six, h⟩
    · rw [pow_zero, x_def]; omega
  · -- a = 1, m = 6x − 1 = p − 2
    refine ⟨1, 6 * x k - 1, by rw [x_def]; omega, h, ?_⟩
    rw [pow_one, x_def]; omega
  · -- a = 2, m = 3(2x − 1) = p − 4
    refine ⟨2, 3 * (2 * x k - 1), by rw [x_def]; omega, ?_, ?_⟩
    · refine Nat.squarefree_mul_iff.mpr ⟨?_, Nat.prime_three.prime.squarefree, h⟩
      exact Nat.prime_three.coprime_iff_not_dvd.mpr (by rw [x_def]; omega)
    · have e2 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [e2, x_def]; omega
  · -- a = 3, m = 6x − 7 = p − 8; squarefreeness forces m ≠ 0, hence k ≥ 1
    have hne : 6 * x k - 7 ≠ 0 := h.ne_zero
    refine ⟨3, 6 * x k - 7, Nat.pos_of_ne_zero hne, h, ?_⟩
    have e3 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [e3]
    rw [x_def] at hne ⊢
    omega

end Erdos7Mod36
