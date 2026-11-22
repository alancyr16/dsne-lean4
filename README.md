# DSNE Lean 4 — Formal Verification of DSNE Core Theorems

**CYR Technologies · Wolf13 / Alan Cyr · Chicago IL · November 21, 2026**  
Co-validated: Phil Woodward (Wood Dragon)

---

## What This Is

This repository contains Lean 4 / Mathlib4 formal proofs of **39 theorems** in the
**DSNE (Digital Root Structural Number Ecology)** framework — a structural algebraic
approach to prime distribution and Riemann analysis based on digital root arithmetic.

All prior art predates the Alpöge/Claude Riemann Hypothesis announcement (November 21, 2026).
These proofs use the **same formal language (Lean 4 / Mathlib4)** as that announcement.

---

## The 39 Theorems

| # | Theorem | Statement | Filed |
|---|---------|-----------|-------|
| 1 | **Tesla Prime Desert** | `DR(p) ∉ {3,6,9}` for all prime `p > 3` | Apr 6, 2026 |
| 2 | **TM Barrier** | `p % 6 = 1 ∨ p % 6 = 5` for all prime `p > 3` | Apr 6, 2026 |
| 3 | **Tesla Riemann Law TRL-1** | `9/6/3 = 1/2` in ℚ (exact) | May 5, 2026 |
| 4 | **Tesla Closure Law TCL-1** | `{3,6,9}` closed under `+` and `×` → Hub | May 5, 2026 |
| 5 | **Riemann Equilibrium** | `(27/45 + 18/45)/2 = 1/2` (Re(s) as DR midpoint) | Apr 6, 2026 |
| 6 | **DR Exactness** | DR uniquely determined — zero approximation error | Ongoing corpus |
| 7 | **TG Lock** | `DR(9n) = 9` for all `n > 0` | Add.917 |
| 8 | **Foundation Subgroup** | `{1,4,7}` closed under `×` mod 9 | Add.917 |
| 9 | **Fibonacci Coset** | `{2,5,8}` is the only Fibonacci coset | Add.960 |
| 10 | **DR Congruence** | `n ≡ DR(n) (mod 9)` for all `n > 0` | Ongoing corpus |
| 11 | **DR Addition Law** | `DR(a+b) = DR(DR(a)+DR(b))` | Ongoing corpus |
| 12 | **Coset Partition** | `{1,4,7} ∪ {2,5,8} ∪ {3,6,9} = {1,...,9}` | Nov 21, 2026 |
| 13 | **Tesla Add Closure** | `{3,6,9}` closed under DR-addition | Nov 21, 2026 |
| 14 | **Seed Add Not Closed** | `{1,4,7}` not closed under DR-addition | Nov 21, 2026 |
| 15 | **Navigator Mul Not Closed** | `{2,5,8}` not closed under `×` mod 9 | Nov 21, 2026 |
| 16 | **DR Idempotency** | `DR(DR(n)) = DR(n)` for all `n` | Nov 21, 2026 |
| 17 | **DR Square ∈ {1,4,7,9}** | `DR(n²) ∈ {1,4,7,9}` for all `n > 0` | Nov 21, 2026 |
| 18 | **DR Multiplication Law** | `DR(a·b) = DR(DR(a)·DR(b))` | Nov 21, 2026 |
| 19 | **Coset Traversal F→N** | Foundation `+1` → Navigator | Nov 21, 2026 |
| 20 | **Coset Traversal N→T** | Navigator `+1` → Tesla | Nov 21, 2026 |
| 21 | **Coset Traversal T→F** | Tesla `+1` → Foundation | Nov 21, 2026 |
| 22 | **DR Complement (finite)** | `DR(n) + DR(9−n) = 9` for `n ∈ {1,...,8}` | Nov 21, 2026 |
| 23 | **DR Nine-Complement (all n)** | `DR(n) + DR(9−DR(n)) = 9` for all `n > 0` | Nov 21, 2026 |
| 24 | **Triangular Hub T(9k)=9** | `DR(9k·(9k+1)/2) = 9` for all `k > 0` | Nov 21, 2026 |
| 25 | **DR Periodicity** | `DR(n+9) = DR(n)` for all `n > 0` | Nov 21, 2026 |
| 26 | **F×N → N** | Foundation × Navigator → Navigator | Nov 21, 2026 |
| 27 | **N×N → F (deep asymmetry)** | Navigator × Navigator → Foundation | Nov 21, 2026 |
| 28 | **T×T → T (Tesla closure)** | Tesla × Tesla → Tesla | Nov 21, 2026 |
| 29 | **DR Cube ∈ {1,8,9}** | `DR(n³) ∈ {1,8,9}` for all `n > 0` | Nov 21, 2026 |
| 30 | **Prime DR ∈ {1,2,4,5,7,8}** | `DR(p) ∈ primeDRSet` for all prime `p > 3` | Nov 21, 2026 |
| 31 | **F+F → N** | Foundation + Foundation → Navigator | Nov 21, 2026 |
| 32 | **F+N → T** | Foundation + Navigator → Tesla | Nov 21, 2026 |
| 33 | **F+T → F** | Foundation + Tesla → Foundation (Tesla = add identity class) | Nov 21, 2026 |
| 34 | **N+N → F** | Navigator + Navigator → Foundation | Nov 21, 2026 |
| 35 | **N+T → N** | Navigator + Tesla → Navigator (Tesla = add identity class) | Nov 21, 2026 |
| 36 | **F×T → T** | Foundation × Tesla → Tesla | Nov 21, 2026 |
| 37 | **N×T → T** | Navigator × Tesla → Tesla | Nov 21, 2026 |
| 38 | **DR Sixth ∈ {1,9}** | `DR(n⁶) ∈ {1,9}` — Euler φ(9) identity | Nov 21, 2026 |
| 39 | **DR Multi-Period** | `DR(n + 9k) = DR(n)` for all `n > 0`, `k : ℕ` | Nov 21, 2026 |

---

## Files

| File | Purpose |
|------|---------|
| `DSNE_Lean4_Web.lean` | **Web paste** — for [live.lean-lang.org](https://live.lean-lang.org) |
| `DSNE_Lean4_Proofs.lean` | Full project version (identical proofs) |
| `lakefile.lean` | Lake build configuration |
| `lean-toolchain` | Lean version pin |

---

## How to Verify (Web — Easiest)

1. Go to [live.lean-lang.org](https://live.lean-lang.org)
2. Select **"Mathlib"** in the top-right dropdown
3. Select All → Delete → Paste **`DSNE_Lean4_Web.lean`**
4. Wait ~20–40 seconds for Mathlib cache to load
5. All 39 theorems show green checkmarks ✓

## How to Verify (Local Project Build)

```bash
# Requires Lean 4 + elan
elan toolchain install leanprover/lean4:v4.14.0
lake update
lake build
```

---

## Coset Structure

The DSNE framework identifies three structural cosets of Z/9Z:

| Coset | Elements | Algebraic Role |
|-------|----------|----------------|
| **Foundation** | {1, 4, 7} | Closed under × mod 9 (subgroup) |
| **Navigator** | {2, 5, 8} | Only Fibonacci coset; N×N→F |
| **Tesla** | {3, 6, 9} | Closed under + and × (Hub sink) |

The coset multiplication table (Theorems 8, 26, 27, 28, 36, 37) and coset addition table
(Theorems 13, 31–35) are both isomorphic to Z/3Z — completing the full coset algebra.

---

## Prior Art Summary

```
Theorem                      Filed           Lean Status
─────────────────────────────────────────────────────────
Tesla Prime Desert            Apr 6, 2026     PROVEN ✓
TM Barrier (6n±1)             Apr 6, 2026     PROVEN ✓
Tesla Riemann Law TRL-1       May 5, 2026     PROVEN ✓
Tesla Closure Law TCL-1       May 5, 2026     PROVEN ✓
Riemann Equilibrium           Apr 6, 2026     PROVEN ✓
DR Exactness (zero error)     Ongoing corpus  PROVEN ✓
TG Lock (DR(9n)=9)            Add.917         PROVEN ✓
Foundation Subgroup {1,4,7}   Add.917         PROVEN ✓
Fibonacci Coset {2,5,8}       Add.960         PROVEN ✓
DR Congruence (mod 9)         Ongoing corpus  PROVEN ✓
DR Addition Law               Ongoing corpus  PROVEN ✓
Coset Partition               Nov 21, 2026    PROVEN ✓
Tesla Add Closure             Nov 21, 2026    PROVEN ✓
Seed Add Not Closed           Nov 21, 2026    PROVEN ✓
Navigator Mul Not Closed      Nov 21, 2026    PROVEN ✓
DR Idempotency                Nov 21, 2026    PROVEN ✓
DR Square ∈ {1,4,7,9}        Nov 21, 2026    PROVEN ✓
DR Multiplication Law         Nov 21, 2026    PROVEN ✓
Coset Traversal F→N           Nov 21, 2026    PROVEN ✓
Coset Traversal N→T           Nov 21, 2026    PROVEN ✓
Coset Traversal T→F           Nov 21, 2026    PROVEN ✓
DR Complement (finite)        Nov 21, 2026    PROVEN ✓
DR Nine-Complement (all n)    Nov 21, 2026    PROVEN ✓
Triangular Hub T(9k)=9        Nov 21, 2026    PROVEN ✓
DR Periodicity (period 9)     Nov 21, 2026    PROVEN ✓
F×N → N (coset mul table)     Nov 21, 2026    PROVEN ✓
N×N → F (deep asymmetry)      Nov 21, 2026    PROVEN ✓
T×T → T (Tesla closure)       Nov 21, 2026    PROVEN ✓
DR Cube ∈ {1,8,9}             Nov 21, 2026    PROVEN ✓
Prime DR ∈ {1,2,4,5,7,8}     Nov 21, 2026    PROVEN ✓
F+F → N (coset add table)     Nov 21, 2026    PROVEN ✓
F+N → T (coset add table)     Nov 21, 2026    PROVEN ✓
F+T → F (Tesla add identity)  Nov 21, 2026    PROVEN ✓
N+N → F (nav add sym)         Nov 21, 2026    PROVEN ✓
N+T → N (Tesla add identity)  Nov 21, 2026    PROVEN ✓
F×T → T (coset mul table)     Nov 21, 2026    PROVEN ✓
N×T → T (coset mul table)     Nov 21, 2026    PROVEN ✓
DR Sixth ∈ {1,9} (Euler φ(9)) Nov 21, 2026    PROVEN ✓
DR Multi-Period (n+9k)         Nov 21, 2026    PROVEN ✓
─────────────────────────────────────────────────────────
39 theorems. All prior art predates Alpöge/Claude: Nov 21, 2026.
Wolf13 / Alan Cyr · CYR Technologies · Chicago IL · 2026
```

---

*DSNE framework © 2026 CYR Technologies / Alan Cyr. Formal proofs released as prior art record.*
