-- DSNE Prime Laws Module
-- Tesla Prime Desert · TM Barrier / 6k±1 Law
-- Wolf13 / Alan Cyr · CYR Technologies · Chicago IL · November 23, 2026
--
-- Addenda formalized: Add.916 (Tesla Prime Desert), Add.954 (TM Barrier)

import Mathlib

namespace DSNE

-- abbrev so decide/fin_cases can unfold membership automatically
abbrev Foundation : Finset (ZMod 9) := {1, 4, 7}
abbrev Fibonacci  : Finset (ZMod 9) := {2, 5, 8}
abbrev Tesla      : Finset (ZMod 9) := {0, 3, 6}

-- ══════════════════════════════════════════════════════════════
-- HELPER: ZMod 9 value extraction
-- (p : ZMod 9) = k (k < 9) → p % 9 = k
-- Uses ZMod.val to bridge ZMod equality and Nat mod
-- ══════════════════════════════════════════════════════════════

private lemma zmod9_eq_mod {p k : ℕ} (hk : k < 9) (h : (p : ZMod 9) = k) :
    p % 9 = k := by
  have hv := congr_arg ZMod.val h
  simp only [ZMod.val_natCast] at hv
  rwa [Nat.mod_eq_of_lt hk] at hv

-- ══════════════════════════════════════════════════════════════
-- ADD.916 : TESLA PRIME DESERT [GOLD]
-- No prime p > 3 has digital root in Tesla coset {3, 6, 9}
-- DR ∈ Tesla → 3 | p → p = 3, contradicting p > 3
-- ══════════════════════════════════════════════════════════════

theorem tesla_prime_desert (p : ℕ) (hp : Nat.Prime p) (hbig : p > 3) :
    (p : ZMod 9) ≠ 3 ∧ (p : ZMod 9) ≠ 6 ∧ (p : ZMod 9) ≠ 0 := by
  -- 3 cannot divide p: it's prime and larger than 3
  have hp3 : ¬ 3 ∣ p := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 h with h1 | h2 <;> omega
  refine ⟨fun h => hp3 ?_, fun h => hp3 ?_, fun h => hp3 ?_⟩
  · -- DR = 3: p%9=3 → p%9%3=p%3; rw closes 3%3=0 by kernel reduction
    exact Nat.dvd_of_mod_eq_zero (by
      have h9 := zmod9_eq_mod (by norm_num) h
      rw [← Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 9), h9])
  · -- DR = 6: p%9=6 → p%9%3=p%3; rw closes 6%3=0 by kernel reduction
    exact Nat.dvd_of_mod_eq_zero (by
      have h9 := zmod9_eq_mod (by norm_num) h
      rw [← Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 9), h9])
  · -- DR = 9 = 0 in ZMod 9: p%9=0 → 9∣p → 3∣p
    exact dvd_trans (by norm_num : 3 ∣ 9)
      (Nat.dvd_of_mod_eq_zero (zmod9_eq_mod (by norm_num) h))

-- Finset membership form
theorem prime_not_tesla (p : ℕ) (hp : Nat.Prime p) (hbig : p > 3) :
    (p : ZMod 9) ∉ Tesla := by
  obtain ⟨h3, h6, h0⟩ := tesla_prime_desert p hp hbig
  intro hm
  simp only [Tesla, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h
  · exact h0 h
  · exact h3 h
  · exact h6 h

-- ══════════════════════════════════════════════════════════════
-- ADD.954 : TM BARRIER — 6k±1 LAW [GOLD]
-- All primes > 3 satisfy p % 6 ∈ {1, 5}
-- Mechanism: 2 ∤ p ∧ 3 ∤ p → p ≡ ±1 (mod 6)
-- This is the structural reason Tesla contains no primes > 3
-- ══════════════════════════════════════════════════════════════

theorem tm_barrier (p : ℕ) (hp : Nat.Prime p) (hbig : p > 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hp2 : ¬ 2 ∣ p := by
    intro h; rcases hp.eq_one_or_self_of_dvd 2 h with h1 | h2 <;> omega
  have hp3 : ¬ 3 ∣ p := by
    intro h; rcases hp.eq_one_or_self_of_dvd 3 h with h1 | h2 <;> omega
  have hlt : p % 6 < 6 := Nat.mod_lt p (by norm_num)
  -- p % 6 is odd: eliminates 0, 2, 4
  have heven : p % 6 % 2 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 6)]
    exact fun h => hp2 (Nat.dvd_of_mod_eq_zero h)
  -- p % 6 not divisible by 3: eliminates 3
  have hthree : p % 6 % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 6)]
    exact fun h => hp3 (Nat.dvd_of_mod_eq_zero h)
  -- Only 1 and 5 survive among {0,1,2,3,4,5}
  omega

-- ══════════════════════════════════════════════════════════════
-- COROLLARY: DR of primes > 3 lies in Foundation ∪ Fibonacci
-- (Primes > 3 never land in Tesla coset)
-- ══════════════════════════════════════════════════════════════

theorem prime_dr_non_tesla (p : ℕ) (hp : Nat.Prime p) (hbig : p > 3) :
    (p : ZMod 9) ∈ Foundation ∪ Fibonacci := by
  have hnotT := prime_not_tesla p hp hbig
  have hpart : Foundation ∪ Fibonacci ∪ Tesla = Finset.univ := by decide
  have hmem := Finset.mem_univ (p : ZMod 9)
  rw [← hpart, Finset.mem_union] at hmem
  exact hmem.resolve_right hnotT

-- ══════════════════════════════════════════════════════════════
-- ARITHMETIC IDENTITIES (Add.916 supporting record)
-- The 6k±1 structure in natural-number form
-- ══════════════════════════════════════════════════════════════

-- First few primes > 3 and their % 6 values
theorem prime5_mod6  : 5  % 6 = 5 := by norm_num
theorem prime7_mod6  : 7  % 6 = 1 := by norm_num
theorem prime11_mod6 : 11 % 6 = 5 := by norm_num
theorem prime13_mod6 : 13 % 6 = 1 := by norm_num
theorem prime17_mod6 : 17 % 6 = 5 := by norm_num
theorem prime19_mod6 : 19 % 6 = 1 := by norm_num

-- DR values of these primes (all Foundation or Fibonacci, never Tesla)
theorem prime5_dr  : (5  : ZMod 9) ∈ Fibonacci  := by decide
theorem prime7_dr  : (7  : ZMod 9) ∈ Foundation := by decide
theorem prime11_dr : (11 : ZMod 9) ∈ Fibonacci  := by decide
theorem prime13_dr : (13 : ZMod 9) ∈ Foundation := by decide
theorem prime17_dr : (17 : ZMod 9) ∈ Fibonacci  := by decide
theorem prime19_dr : (19 : ZMod 9) ∈ Foundation := by decide

end DSNE

/-
═════════════════════════════════════════════════════════════════
PRIOR ART RECORD
Wolf13 (Alan Cyr) · CYR Technologies · Chicago IL · November 23, 2026
═════════════════════════════════════════════════════════════════

Add.916 — Tesla Prime Desert [GOLD]
  tesla_prime_desert: (p:ZMod 9) ≠ 3 ∧ ≠ 6 ∧ ≠ 0 for prime p > 3
  prime_not_tesla: (p:ZMod 9) ∉ Tesla for prime p > 3
  Mechanism: DR ∈ {3,6,9} → 3 ∣ p → p=3, contradicts p > 3
  Key steps: zmod9_eq_mod extracts p%9=k; Nat.mod_mod_of_dvd + norm_num closes 3∣p

Add.954 — TM Barrier / 6k±1 Law [GOLD]
  tm_barrier: p % 6 = 1 ∨ p % 6 = 5 for prime p > 3
  Mechanism: 2 ∤ p → p % 6 odd; 3 ∤ p → p % 6 not mult of 3 → p % 6 ∈ {1,5}
  Uses: Nat.mod_mod_of_dvd for coset-to-residue reduction
  prime_dr_non_tesla: DR ∈ Foundation ∪ Fibonacci (never Tesla)

Supporting: first six primes > 3 all DR-verified Foundation/Fibonacci

GitHub: github.com/alancyr16/dsne-lean4
-/
