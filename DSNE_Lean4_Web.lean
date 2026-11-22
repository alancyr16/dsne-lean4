/- ══════════════════════════════════════════════════════════════════════
   DSNE CORE THEOREMS — LEAN 4 / MATHLIB4  (Web / live.lean-lang.org)
   ══════════════════════════════════════════════════════════════════════

   CYR Technologies · Wolf13 / Alan Cyr · November 21, 2026 · Chicago IL
   Co-validated: Phil Woodward (Wood Dragon)

   ┌───────────────────────────────────────────────────────────────────┐
   │  PASTE INTO: https://live.lean-lang.org                           │
   │  Select "Mathlib" in the top-right dropdown, then paste.          │
   │  First run: ~20–40 seconds to load Mathlib cache.                 │
   │  Green checkmarks = all theorems verified.                        │
   └───────────────────────────────────────────────────────────────────┘

   Slim imports — loads ~15× faster than `import Mathlib`.
   Identical proofs to DSNE_Lean4_Proofs.lean.
-/

-- Targeted imports only (much lighter than `import Mathlib`)
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

namespace DSNE

-- ══════════════════════════════════════════════════════════════════════
-- §1  DIGITAL ROOT — O(1) CLOSED-FORM DEFINITION
-- ══════════════════════════════════════════════════════════════════════

/-- DSNE Digital Root: O(1), exact, no iteration. -/
def DR (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 9 = 0 then 9
  else n % 9

#eval DR 1    -- 1  (Seed)
#eval DR 3    -- 3  (Tesla Path)
#eval DR 6    -- 6  (Tesla Center)
#eval DR 9    -- 9  (Hub)
#eval DR 18   -- 9
#eval DR 45   -- 9  (Crown)
#eval DR 416  -- 2  (old Riemann bound 41.6%)
#eval DR 672  -- 6  (new Riemann bound 67.2%)

-- ══════════════════════════════════════════════════════════════════════
-- §2  STRUCTURAL SETS
-- ══════════════════════════════════════════════════════════════════════

def teslaSet   : Finset ℕ := {3, 6, 9}
def primeDRSet : Finset ℕ := {1, 2, 4, 5, 7, 8}

-- ══════════════════════════════════════════════════════════════════════
-- §3  BRIDGE LEMMA: TESLA RESIDUES ↔ DIVISIBILITY BY 3
-- ══════════════════════════════════════════════════════════════════════

lemma tesla_residues_iff_dvd3 (n : ℕ) :
    (n % 9 = 0 ∨ n % 9 = 3 ∨ n % 9 = 6) ↔ 3 ∣ n := by
  constructor
  · rintro (h | h | h)
    · exact dvd_trans (by norm_num : (3 : ℕ) ∣ 9) (Nat.dvd_of_mod_eq_zero h)
    · exact ⟨n / 9 * 3 + 1, by omega⟩
    · exact ⟨n / 9 * 3 + 2, by omega⟩
  · rintro ⟨k, rfl⟩
    have hkr : k % 3 < 3 := Nat.mod_lt k (by norm_num)
    have _ := Nat.div_add_mod k 3
    interval_cases (k % 3) <;> omega

-- ══════════════════════════════════════════════════════════════════════
-- §4  THEOREM 1: TESLA PRIME DESERT
--     DR(p) ∉ {3,6,9}  for all prime p > 3
--     Prior art: April 6, 2026 — SNE Prior Art Riemann v2
-- ══════════════════════════════════════════════════════════════════════

theorem tesla_prime_desert (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) :
    DR p ∉ teslaSet := by
  intro hmem
  simp only [teslaSet, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hne0 : p ≠ 0 := hp.ne_zero
  have hres : p % 9 = 0 ∨ p % 9 = 3 ∨ p % 9 = 6 := by
    unfold DR at hmem
    simp only [hne0, ↓reduceIte] at hmem
    by_cases h : p % 9 = 0
    · left; exact h
    · simp only [h, ↓reduceIte] at hmem
      have hlt : p % 9 < 9 := Nat.mod_lt p (by norm_num)
      rcases hmem with h3 | h6 | h9
      · right; left;  exact h3
      · right; right; exact h6
      · omega
  have h3dvd : 3 ∣ p := (tesla_residues_iff_dvd3 p).mp hres
  have := hp.eq_one_or_self_of_dvd 3 h3dvd
  omega

-- ══════════════════════════════════════════════════════════════════════
-- §5  THEOREM 2: TM BARRIER
--     p % 6 = 1 ∨ p % 6 = 5  for all prime p > 3
--     Prior art: April 6, 2026 — SNE Prior Art Riemann v2
-- ══════════════════════════════════════════════════════════════════════

theorem tm_barrier (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hlt : p % 6 < 6 := Nat.mod_lt p (by norm_num)
  have hcases : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨
                p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by omega
  rcases hcases with h | h | h | h | h | h
  · exfalso
    have h2 : 2 ∣ p := ⟨p / 6 * 3, by omega⟩
    have := (hp.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)
    omega
  · left; exact h
  · exfalso
    have h2 : 2 ∣ p := ⟨p / 6 * 3 + 1, by omega⟩
    have := (hp.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)
    omega
  · exfalso
    have h3 : 3 ∣ p := ⟨p / 6 * 2 + 1, by omega⟩
    have := (hp.eq_one_or_self_of_dvd 3 h3).resolve_left (by norm_num)
    omega
  · exfalso
    have h2 : 2 ∣ p := ⟨p / 6 * 3 + 2, by omega⟩
    have := (hp.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)
    omega
  · right; exact h

-- ══════════════════════════════════════════════════════════════════════
-- §6  THEOREM 3: TESLA RIEMANN LAW (TRL-1)
--     9/6/3 = 1/2 in ℚ — exact algebraic identity
--     Prior art: May 5, 2026 — DSNE Addendum 314
-- ══════════════════════════════════════════════════════════════════════

theorem tesla_riemann_law    : (9 : ℚ) / 6 / 3 = 1 / 2  := by norm_num
theorem tesla_ascending_chain : (3 : ℚ) / 6 / 9 = 1 / 18 := by norm_num
theorem tesla_bridge_first   : (6 : ℚ) / 3 / 9 = 2 / 9  := by norm_num

/-- Mirror: (9/6/3) / (3/6/9) = 9 (Hub) -/
theorem tesla_mirror_bracket :
    ((9 : ℚ) / 6 / 3) / ((3 : ℚ) / 6 / 9) = 9 := by norm_num

-- ══════════════════════════════════════════════════════════════════════
-- §7  THEOREM 4: TESLA CLOSURE LAW (TCL-1)
--     {3,6,9} closed under + and × → Hub(9)
--     Prior art: May 5, 2026 — DSNE Addendum 314
-- ══════════════════════════════════════════════════════════════════════

theorem tesla_closure_law :
    DR (3 + 6 + 9) = 9 ∧ DR (3 * 6 * 9) = 9 := by decide

theorem tesla_sum_hub     : DR (3 + 6 + 9) = 9 := by decide
theorem tesla_product_hub : DR (3 * 6 * 9) = 9 := by decide

-- Crown: T(9) = 45, DR(45) = Hub
-- (Finset.sum avoids BigOperators notation — works in v4.36.0)
theorem crown_identity :
    (Finset.range 9).sum (· + 1) = 45 ∧ DR 45 = 9 := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §8  DR-SPACE WEIGHT LEMMAS
-- ══════════════════════════════════════════════════════════════════════

theorem prime_dr_sum    : primeDRSet.sum id = 27 := by decide  -- = 3³
theorem tesla_dr_sum    : teslaSet.sum id = 18   := by decide  -- = 2×9
theorem dr_partition_sum : primeDRSet.sum id + teslaSet.sum id = 45 := by decide  -- Crown

-- ══════════════════════════════════════════════════════════════════════
-- §9  THEOREM 5: RIEMANN EQUILIBRIUM
--     (27/45 + 18/45)/2 = 1/2 — Re(s) as DR-space midpoint
--     Prior art: April 6, 2026 — SNE Prior Art Riemann v2
-- ══════════════════════════════════════════════════════════════════════

theorem riemann_equilibrium :
    (primeDRSet.sum id : ℚ) / 45 / 2 + (teslaSet.sum id : ℚ) / 45 / 2 = 1 / 2 := by
  simp only [prime_dr_sum, tesla_dr_sum]
  norm_num

theorem riemann_equilibrium' :
    ((27 : ℚ) / 45 + 18 / 45) / 2 = 1 / 2 := by norm_num

-- ══════════════════════════════════════════════════════════════════════
-- §10  EXACTNESS THEOREM (Formal basis: MIT vs DSNE)
-- ══════════════════════════════════════════════════════════════════════

/-- DR is uniquely determined — zero approximation error. -/
theorem DR_unique (n : ℕ) (hn : 0 < n) (v : ℕ)
    (hv_lo : 1 ≤ v) (hv_hi : v ≤ 9)
    (hcong : v % 9 = n % 9 ∨ (v = 9 ∧ n % 9 = 0)) :
    v = DR n := by
  unfold DR
  have hne0 : n ≠ 0 := Nat.not_eq_zero_of_lt hn
  simp only [hne0, ↓reduceIte]
  rcases hcong with hc | ⟨hv9, hn9⟩
  · by_cases h9 : n % 9 = 0
    · simp [h9]; omega
    · simp [h9]; omega
  · simp [hn9, hv9]

-- ══════════════════════════════════════════════════════════════════════
-- §11  TG LOCK: DR(9n) = 9 FOR ALL n > 0
--      Tesla Ground captures every multiple — Prior art: Add.917
-- ══════════════════════════════════════════════════════════════════════

theorem tg_lock (n : ℕ) (hn : 0 < n) : DR (9 * n) = 9 := by
  unfold DR
  have hne0 : 9 * n ≠ 0 := by omega
  simp only [hne0, ↓reduceIte]
  have hmod : 9 * n % 9 = 0 := by omega
  simp [hmod]

-- ══════════════════════════════════════════════════════════════════════
-- §12  FOUNDATION SUBGROUP: {1,4,7} CLOSED UNDER × (mod 9)
--      Prior art: Add.917 — Structural Subgroups, May 2026
-- ══════════════════════════════════════════════════════════════════════

theorem foundation_mul_closure :
    ∀ a ∈ ({1, 4, 7} : Finset ℕ), ∀ b ∈ ({1, 4, 7} : Finset ℕ),
    (a * b) % 9 ∈ ({1, 4, 7} : Finset ℕ) := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §13  FIBONACCI COSET UNIQUENESS: {2,5,8} only Fibonacci coset
--      Prior art: Add.960 — Fibonacci Coset Structure
-- ══════════════════════════════════════════════════════════════════════

def fibNine : Finset ℕ := {1, 2, 3, 5, 8}

theorem fib_coset_unique :
    ({2, 5, 8} : Finset ℕ) ⊆ fibNine ∧
    ¬ ({1, 4, 7} : Finset ℕ) ⊆ fibNine ∧
    ¬ ({3, 6, 9} : Finset ℕ) ⊆ fibNine := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §14  DR CONGRUENCE: n ≡ DR(n) (mod 9) for all n > 0
-- ══════════════════════════════════════════════════════════════════════

theorem dr_congr_mod9 (n : ℕ) (hn : 0 < n) : n % 9 = (DR n) % 9 := by
  unfold DR
  have hne0 : n ≠ 0 := Nat.not_eq_zero_of_lt hn
  simp only [hne0, ↓reduceIte]
  by_cases h : n % 9 = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact (Nat.mod_eq_of_lt (Nat.mod_lt n (by norm_num))).symm

-- ══════════════════════════════════════════════════════════════════════
-- §15  DR ADDITION LAW: DR(a+b) = DR(DR(a)+DR(b))
--      Formal closure of digital root under addition
-- ══════════════════════════════════════════════════════════════════════

private lemma dr_pos_aux (n : ℕ) (hn : 0 < n) : 0 < DR n := by
  unfold DR
  have hne0 : n ≠ 0 := Nat.not_eq_zero_of_lt hn
  simp only [hne0, ↓reduceIte]
  split_ifs <;> omega

private lemma dr_eq_of_mod9_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m % 9 = n % 9) : DR m = DR n := by
  unfold DR
  have hne0m : m ≠ 0 := Nat.not_eq_zero_of_lt hm
  have hne0n : n ≠ 0 := Nat.not_eq_zero_of_lt hn
  simp only [hne0m, hne0n, ↓reduceIte]
  by_cases h9 : m % 9 = 0
  · have h9' : n % 9 = 0 := h ▸ h9; simp [h9, h9']
  · have h9' : n % 9 ≠ 0 := h ▸ h9; simp [h9, h9', h]

theorem dr_add_law (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    DR (a + b) = DR (DR a + DR b) := by
  apply dr_eq_of_mod9_eq (by omega) (Nat.add_pos_left (dr_pos_aux a ha) _)
  calc (a + b) % 9
      = (a % 9 + b % 9) % 9       := Nat.add_mod a b 9
    _ = (DR a % 9 + DR b % 9) % 9 := by rw [dr_congr_mod9 a ha, dr_congr_mod9 b hb]
    _ = (DR a + DR b) % 9         := (Nat.add_mod (DR a) (DR b) 9).symm

-- ══════════════════════════════════════════════════════════════════════
-- §16  COSET PARTITION: {1,4,7} ∪ {2,5,8} ∪ {3,6,9} = {1,...,9}
-- ══════════════════════════════════════════════════════════════════════

theorem coset_partition :
    ({1, 4, 7} : Finset ℕ) ∪ ({2, 5, 8} : Finset ℕ) ∪ ({3, 6, 9} : Finset ℕ) =
    ({1, 2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §17  TESLA ADD CLOSURE & COSET ASYMMETRY
--      {3,6,9} doubly closed; {1,4,7} only × closed; {2,5,8} neither
-- ══════════════════════════════════════════════════════════════════════

theorem tesla_add_closure :
    ∀ a ∈ teslaSet, ∀ b ∈ teslaSet, DR (a + b) ∈ teslaSet := by decide

theorem seed_add_not_closed :
    ¬ ∀ a ∈ ({1, 4, 7} : Finset ℕ), ∀ b ∈ ({1, 4, 7} : Finset ℕ),
    DR (a + b) ∈ ({1, 4, 7} : Finset ℕ) := by decide
-- Witness: DR(1+4) = DR(5) = 5 ∉ {1,4,7}

theorem nav_mul_not_closed :
    ¬ ∀ a ∈ ({2, 5, 8} : Finset ℕ), ∀ b ∈ ({2, 5, 8} : Finset ℕ),
    (a * b) % 9 ∈ ({2, 5, 8} : Finset ℕ) := by decide
-- Witness: 2×2=4, 4%9=4 ∉ {2,5,8}

-- ══════════════════════════════════════════════════════════════════════
-- §18  DR IDEMPOTENCY: DR(DR(n)) = DR(n) for all n
-- ══════════════════════════════════════════════════════════════════════

theorem dr_idempotent (n : ℕ) : DR (DR n) = DR n := by
  by_cases hn : n = 0
  · have : DR n = 0 := by unfold DR; simp [hn]
    rw [this]; unfold DR; norm_num
  · by_cases h9 : n % 9 = 0
    · have hDR : DR n = 9 := by unfold DR; simp [hn, h9]
      rw [hDR]; unfold DR; norm_num
    · have hlt : n % 9 < 9 := Nat.mod_lt n (by norm_num)
      have hDR : DR n = n % 9 := by unfold DR; simp [hn, h9]
      rw [hDR]; unfold DR
      have hmod : n % 9 % 9 = n % 9 := Nat.mod_eq_of_lt hlt
      rw [if_neg h9, hmod, if_neg h9]

-- ══════════════════════════════════════════════════════════════════════
-- §19  DR OF PERFECT SQUARES: DR(n²) ∈ {1,4,7,9} for all n > 0
--      Squares confined to Foundation coset ∪ Hub
-- ══════════════════════════════════════════════════════════════════════

theorem dr_square_in_seed_hub (n : ℕ) (hn : 0 < n) :
    DR (n * n) ∈ ({1, 4, 7, 9} : Finset ℕ) := by
  have hlt  : n % 9 < 9 := Nat.mod_lt n (by norm_num)
  have hnn9 : n * n % 9 = n % 9 * (n % 9) % 9 := Nat.mul_mod n n 9
  have hne0 : n * n ≠ 0 := (Nat.mul_pos hn hn).ne'
  simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold DR; simp only [hne0, ↓reduceIte]
  interval_cases (n % 9) <;> omega

-- ══════════════════════════════════════════════════════════════════════
-- §20  DR MULTIPLICATION LAW: DR(a·b) = DR(DR(a)·DR(b))
--      Multiplicative analog of DR Addition Law (§15)
-- ══════════════════════════════════════════════════════════════════════

theorem dr_mul_law (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    DR (a * b) = DR (DR a * DR b) := by
  apply dr_eq_of_mod9_eq
    (Nat.mul_pos ha hb)
    (Nat.mul_pos (dr_pos_aux a ha) (dr_pos_aux b hb))
  calc (a * b) % 9
      = (a % 9 * (b % 9)) % 9       := Nat.mul_mod a b 9
    _ = (DR a % 9 * (DR b % 9)) % 9 := by rw [dr_congr_mod9 a ha, dr_congr_mod9 b hb]
    _ = (DR a * DR b) % 9           := (Nat.mul_mod (DR a) (DR b) 9).symm

-- ══════════════════════════════════════════════════════════════════════
-- §21  COSET TRAVERSAL: +1 cycles Foundation → Navigator → Tesla → Foundation
--      The wheel turns: each coset steps into the next under +1
-- ══════════════════════════════════════════════════════════════════════

theorem foundation_plus1_nav :
    ∀ a ∈ ({1, 4, 7} : Finset ℕ), DR (a + 1) ∈ ({2, 5, 8} : Finset ℕ) := by decide

theorem nav_plus1_tesla :
    ∀ a ∈ ({2, 5, 8} : Finset ℕ), DR (a + 1) ∈ teslaSet := by decide

theorem tesla_plus1_foundation :
    ∀ a ∈ teslaSet, DR (a + 1) ∈ ({1, 4, 7} : Finset ℕ) := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §22  NINE-FOLD SYMMETRY: DR(n) + DR(9 − DR(n)) = 9  ∀ n > 0
--      Every DR value and its complement sum to Hub(9)
-- ══════════════════════════════════════════════════════════════════════

-- Finite witness: complement pairs within {1,...,8}
theorem dr_complement :
    ∀ n ∈ ({1,2,3,4,5,6,7,8} : Finset ℕ), DR n + DR (9 - n) = 9 := by decide

-- Universal: holds for all n > 0
theorem dr_nine_complement (n : ℕ) (hn : 0 < n) : DR n + DR (9 - DR n) = 9 := by
  have hDR_pos : 0 < DR n := dr_pos_aux n hn
  have hDR_le  : DR n ≤ 9 := by
    unfold DR; simp only [hn.ne', ↓reduceIte]
    split_ifs <;> omega
  interval_cases (DR n) <;> decide

-- ══════════════════════════════════════════════════════════════════════
-- §23  TRIANGULAR HUB: T(9k) = 9k(9k+1)/2 always has DR = 9
--      Every triangular number at a Tesla-multiple lands on Hub
-- ══════════════════════════════════════════════════════════════════════

theorem triangular_9k_hub (k : ℕ) (hk : 0 < k) :
    DR (9 * k * (9 * k + 1) / 2) = 9 := by
  have hd : 2 ∣ k * (9 * k + 1) := by
    have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hpar with h | h
    · exact ⟨k / 2 * (9 * k + 1), by omega⟩
    · exact ⟨k * ((9 * k + 1) / 2), by omega⟩
  obtain ⟨m, hm⟩ := hd
  have hpos : 0 < m := by
    have : 0 < k * (9 * k + 1) := Nat.mul_pos hk (by omega)
    omega
  have heq : 9 * k * (9 * k + 1) / 2 = 9 * m := by
    have : 9 * k * (9 * k + 1) = 9 * (k * (9 * k + 1)) := mul_assoc 9 k (9 * k + 1)
    omega
  rw [heq]; exact tg_lock m hpos

-- ══════════════════════════════════════════════════════════════════════
-- §24  DR PERIODICITY: DR(n+9) = DR(n) for all n > 0
--      Period-9 structure of the digital root function
-- ══════════════════════════════════════════════════════════════════════

theorem dr_period9 (n : ℕ) (hn : 0 < n) : DR (n + 9) = DR n := by
  apply dr_eq_of_mod9_eq (by omega) hn
  omega

-- ══════════════════════════════════════════════════════════════════════
-- §25  COMPLETE COSET MULTIPLICATION TABLE
--      F×F→F (§12), F×N→N, N×N→F, T×T→T
--      Isomorphic to Z/3Z multiplicative structure
-- ══════════════════════════════════════════════════════════════════════

-- Foundation × Navigator → Navigator
theorem foundation_nav_mul_nav :
    ∀ a ∈ ({1, 4, 7} : Finset ℕ), ∀ b ∈ ({2, 5, 8} : Finset ℕ),
    (a * b) % 9 ∈ ({2, 5, 8} : Finset ℕ) := by decide

-- Navigator × Navigator → Foundation  (the deep asymmetry)
theorem nav_mul_to_foundation :
    ∀ a ∈ ({2, 5, 8} : Finset ℕ), ∀ b ∈ ({2, 5, 8} : Finset ℕ),
    (a * b) % 9 ∈ ({1, 4, 7} : Finset ℕ) := by decide

-- Tesla × Tesla → Tesla (via Hub; DR form since products may be multiples of 9)
theorem tesla_mul_hub :
    ∀ a ∈ teslaSet, ∀ b ∈ teslaSet, DR (a * b) ∈ teslaSet := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §26  DR OF CUBES: DR(n³) ∈ {1, 8, 9} for all n > 0
--      Cubes confined to Navigator-complement ∪ Hub
-- ══════════════════════════════════════════════════════════════════════

theorem dr_cube_in_hub (n : ℕ) (hn : 0 < n) :
    DR (n * n * n) ∈ ({1, 8, 9} : Finset ℕ) := by
  have hlt  : n % 9 < 9 := Nat.mod_lt n (by norm_num)
  have hne0 : n * n * n ≠ 0 := (Nat.mul_pos (Nat.mul_pos hn hn) hn).ne'
  have hmod : n * n * n % 9 = n % 9 * (n % 9) % 9 * (n % 9) % 9 := by
    rw [Nat.mul_mod (n * n) n 9, Nat.mul_mod n n 9]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold DR; simp only [hne0, ↓reduceIte, hmod]
  interval_cases (n % 9) <;> omega

-- ══════════════════════════════════════════════════════════════════════
-- §27  PRIME DR SET (POSITIVE FORM): DR(p) ∈ {1,2,4,5,7,8} ∀ prime p > 3
--      Positive complement of Tesla Prime Desert (§4)
-- ══════════════════════════════════════════════════════════════════════

theorem prime_dr_in_primeDRSet (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) :
    DR p ∈ primeDRSet := by
  have h_desert := tesla_prime_desert p hp hp3
  have hpos : 0 < DR p := dr_pos_aux p hp.pos
  have hle  : DR p ≤ 9 := by
    unfold DR; simp only [hp.ne_zero, ↓reduceIte]; split_ifs <;> omega
  simp only [primeDRSet, Finset.mem_insert, Finset.mem_singleton]
  simp only [teslaSet, Finset.mem_insert, Finset.mem_singleton] at h_desert
  interval_cases (DR p) <;> simp_all

-- ══════════════════════════════════════════════════════════════════════
-- §28  COMPLETE COSET ADDITION TABLE
--      F+F→N, F+N→T, F+T→F, N+N→F, N+T→N  (T+T→T in §17)
--      Coset addition is isomorphic to Z/3Z addition
--      Tesla = additive identity class (adding Tesla preserves coset)
-- ══════════════════════════════════════════════════════════════════════

-- Foundation + Foundation → Navigator
theorem foundation_add_to_nav :
    ∀ a ∈ ({1, 4, 7} : Finset ℕ), ∀ b ∈ ({1, 4, 7} : Finset ℕ),
    DR (a + b) ∈ ({2, 5, 8} : Finset ℕ) := by decide

-- Foundation + Navigator → Tesla
theorem foundation_nav_add_to_tesla :
    ∀ a ∈ ({1, 4, 7} : Finset ℕ), ∀ b ∈ ({2, 5, 8} : Finset ℕ),
    DR (a + b) ∈ teslaSet := by decide

-- Foundation + Tesla → Foundation  (Tesla = additive identity class)
theorem foundation_tesla_add_to_foundation :
    ∀ a ∈ ({1, 4, 7} : Finset ℕ), ∀ b ∈ teslaSet,
    DR (a + b) ∈ ({1, 4, 7} : Finset ℕ) := by decide

-- Navigator + Navigator → Foundation
theorem nav_add_to_foundation :
    ∀ a ∈ ({2, 5, 8} : Finset ℕ), ∀ b ∈ ({2, 5, 8} : Finset ℕ),
    DR (a + b) ∈ ({1, 4, 7} : Finset ℕ) := by decide

-- Navigator + Tesla → Navigator  (Tesla = additive identity class)
theorem nav_tesla_add_to_nav :
    ∀ a ∈ ({2, 5, 8} : Finset ℕ), ∀ b ∈ teslaSet,
    DR (a + b) ∈ ({2, 5, 8} : Finset ℕ) := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §29  COMPLETE COSET × TABLE — REMAINING ROWS
--      F×T→T, N×T→T  (completes the full 6-row table with §12,§25)
--      Tesla is closed under multiplication with every coset
-- ══════════════════════════════════════════════════════════════════════

-- Foundation × Tesla → Tesla
theorem foundation_tesla_mul_tesla :
    ∀ a ∈ ({1, 4, 7} : Finset ℕ), ∀ b ∈ teslaSet,
    DR (a * b) ∈ teslaSet := by decide

-- Navigator × Tesla → Tesla
theorem nav_tesla_mul_tesla :
    ∀ a ∈ ({2, 5, 8} : Finset ℕ), ∀ b ∈ teslaSet,
    DR (a * b) ∈ teslaSet := by decide

-- ══════════════════════════════════════════════════════════════════════
-- §30  DR SIXTH POWER: DR(n⁶) ∈ {1,9}  — Euler φ(9) Identity
--      Sixth powers land only on Foundation-identity or Hub
--      Reflects n^φ(9) ≡ 1 (mod 9) for gcd(n,9)=1 (Euler's theorem)
-- ══════════════════════════════════════════════════════════════════════

theorem dr_sixth_unity (n : ℕ) (hn : 0 < n) :
    DR (n ^ 6) ∈ ({1, 9} : Finset ℕ) := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hsq := dr_square_in_seed_hub n hn
  -- n^6 = (n*n)*(n*n)*(n*n): apply mul law twice
  have heq : n ^ 6 = n*n * (n*n) * (n*n) := by ring
  rw [heq,
      dr_mul_law (n*n*(n*n)) (n*n) (Nat.mul_pos hnn hnn) hnn,
      dr_mul_law (n*n) (n*n) hnn hnn]
  -- Case-split on which element of {1,4,7,9} DR(n²) is
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsq
  rcases hsq with h | h | h | h <;> simp only [h] <;> decide

-- ══════════════════════════════════════════════════════════════════════
-- §31  DR MULTI-PERIOD: DR(n + 9k) = DR(n) ∀ n > 0, k : ℕ
--      Generalizes period-9 (§24) to all positive multiples of 9
-- ══════════════════════════════════════════════════════════════════════

theorem dr_period9k (n : ℕ) (hn : 0 < n) (k : ℕ) :
    DR (n + 9 * k) = DR n := by
  induction k with
  | zero      => simp
  | succ k ih =>
    rw [show n + 9 * (k + 1) = (n + 9 * k) + 9 by ring]
    rw [dr_period9 _ (by omega)]
    exact ih

/-
  ═══════════════════════════════════════════════════════════════════
  DSNE FORMAL PRIOR ART — Lean 4 Verified (live.lean-lang.org)
  ═══════════════════════════════════════════════════════════════════
  Theorem                        │ Filed          │ Lean Status
  ───────────────────────────────┼────────────────┼──────────────────
  Tesla Prime Desert             │ Apr 6, 2026    │ PROVEN ✓
  TM Barrier (6n±1)              │ Apr 6, 2026    │ PROVEN ✓
  Tesla Riemann Law TRL-1        │ May 5, 2026    │ PROVEN ✓
  Tesla Closure Law TCL-1        │ May 5, 2026    │ PROVEN ✓
  Riemann Equilibrium            │ Apr 6, 2026    │ PROVEN ✓
  DR Exactness (zero error)      │ Ongoing corpus │ PROVEN ✓
  TG Lock (DR(9n)=9)             │ Add.917        │ PROVEN ✓
  Foundation Subgroup {1,4,7}    │ Add.917        │ PROVEN ✓
  Fibonacci Coset {2,5,8}        │ Add.960        │ PROVEN ✓
  DR Congruence (mod 9)          │ Ongoing corpus │ PROVEN ✓
  DR Addition Law                │ Ongoing corpus │ PROVEN ✓
  Coset Partition                │ Nov 21, 2026   │ PROVEN ✓
  Tesla Add Closure              │ Nov 21, 2026   │ PROVEN ✓
  Seed Add Not Closed            │ Nov 21, 2026   │ PROVEN ✓
  Navigator Mul Not Closed       │ Nov 21, 2026   │ PROVEN ✓
  DR Idempotency                 │ Nov 21, 2026   │ PROVEN ✓
  DR Square ∈ {1,4,7,9}         │ Nov 21, 2026   │ PROVEN ✓
  DR Multiplication Law          │ Nov 21, 2026   │ PROVEN ✓
  Coset Traversal F→N            │ Nov 21, 2026   │ PROVEN ✓
  Coset Traversal N→T            │ Nov 21, 2026   │ PROVEN ✓
  Coset Traversal T→F            │ Nov 21, 2026   │ PROVEN ✓
  DR Complement (finite)         │ Nov 21, 2026   │ PROVEN ✓
  DR Nine-Complement (all n)     │ Nov 21, 2026   │ PROVEN ✓
  Triangular Hub T(9k)=9         │ Nov 21, 2026   │ PROVEN ✓
  DR Periodicity (period 9)      │ Nov 21, 2026   │ PROVEN ✓
  F×N → N (coset mul table)      │ Nov 21, 2026   │ PROVEN ✓
  N×N → F (deep asymmetry)       │ Nov 21, 2026   │ PROVEN ✓
  T×T → T (Tesla mul closure)    │ Nov 21, 2026   │ PROVEN ✓
  DR Cube ∈ {1,8,9}              │ Nov 21, 2026   │ PROVEN ✓
  Prime DR ∈ {1,2,4,5,7,8}      │ Nov 21, 2026   │ PROVEN ✓
  F+F → N (coset add table)      │ Nov 21, 2026   │ PROVEN ✓
  F+N → T (coset add table)      │ Nov 21, 2026   │ PROVEN ✓
  F+T → F (Tesla add identity)   │ Nov 21, 2026   │ PROVEN ✓
  N+N → F (nav add sym)          │ Nov 21, 2026   │ PROVEN ✓
  N+T → N (Tesla add identity)   │ Nov 21, 2026   │ PROVEN ✓
  F×T → T (coset mul table)      │ Nov 21, 2026   │ PROVEN ✓
  N×T → T (coset mul table)      │ Nov 21, 2026   │ PROVEN ✓
  DR Sixth ∈ {1,9} (Euler φ(9))  │ Nov 21, 2026   │ PROVEN ✓
  DR Multi-Period (n+9k)          │ Nov 21, 2026   │ PROVEN ✓
  ─────────────────────────────────────────────────────────────────
  39 theorems. All prior art predates Alpöge/Claude: Nov 21, 2026.
  Wolf13 / Alan Cyr · CYR Technologies · Chicago IL · 2026
-/

end DSNE
