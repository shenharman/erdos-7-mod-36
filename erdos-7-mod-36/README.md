# Lean formalization for the one-power Erdős conjecture: primes ≡ 7 (mod 36)

This repository contains a partial Lean 4 formalization accompanying:

Shen Harman, “The One-Power Erdős Conjecture for Primes p ≡ 7 (mod 36).”

The formalization covers elementary reductions used in Section 2.1 of the manuscript. It uses Mathlib.

## Mathematical scope

For a natural number k, write

p = 36k + 7
x = 6k + 1.

The code establishes the four identities

p − 1 = 6x
p − 2 = 6x − 1
p − 4 = 3(2x − 1)
p − 8 = 6x − 7

and the corresponding squarefree equivalences.

It then proves that a squarefree remainder exists among p − 2^a, for a < 4, if and only if at least one of

x, 6x − 1, 2x − 1, 6x − 7

is squarefree. From this condition, it constructs a representation

p = 2^a + m

with m positive and squarefree.

These results hold for every natural number k; primality of p is not required for these reductions.

## Relationship to the manuscript

| Material | Lean declaration |
| --- | --- |
| Parity of x | `x_odd` |
| Coprimality with 6 | `six_coprime_x` |
| Four-candidate criterion | `candidate_iff` |
| Construction of a representation | `one_power_of_candidate` |

All declarations are in the namespace Erdos7Mod36.

This is a partial formalization. It does not establish that one of the four candidates is always squarefree. It does not formalize the manuscript’s pairwise coprimality theorem, strong separation theorem, density results, computational verification, or appendix.

## Arithmetic conventions

The formalization works over the natural numbers, where subtraction truncates at zero.

In particular, when k = 0, we have p = 7 and x = 1. Both p − 8 and 6x − 7 evaluate to zero in Lean. Zero is not squarefree, so this case does not produce a spurious positive representation.

## Checking the proofs

Install Lean and Lake using the Lean community setup instructions. Then run:

git clone https://github.com/YOUR_USERNAME/erdos-7-mod-36.git
cd erdos-7-mod-36
lake exe cache get
lake build

The first command inside the project downloads cached Mathlib build files. The second checks the project, including the proof file.

The Lean version is specified in lean-toolchain. Dependency revisions are recorded in lake-manifest.json. Use the committed configuration to reproduce this version of the formalization.

## Repository structure

Erdos7Mod36.lean        Root module importing the proof file
Erdos7Mod36/Basic.lean  Formal statements and proofs
lean-toolchain          Lean version
lakefile.toml           Project configuration
lake-manifest.json      Dependency revisions

## Citation

When citing this formalization, identify the repository and the specific release or commit used. An archived release DOI will be added when available.

## Feedback

Corrections and questions about the formalization are welcome through GitHub Issues.