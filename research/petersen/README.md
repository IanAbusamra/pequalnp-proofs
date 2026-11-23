# Petersen graph circuit size

This is a research result for L-meta-651 of the P vs NP project. The Boolean function has ten inputs, one per vertex of the Petersen graph. It returns true when both endpoints of some edge are selected.

| Result | Verification |
| --- | --- |
| At least 15 binary AND/OR gates are necessary, even with free negations | Lean 4.36.0 kernel, including all four polarities of an extra gate on opposite six-cycle vertices |
| A circuit with 20 gates computes the function | Explicit witness checked by Lean |
| The minimum in the project’s ordinary AND/OR/NOT model is 20 | Exhaustive computational search, with source, inputs and replay logs |

The assigned statement excludes every ordinary circuit of at most 19 gates. The formal lower bound currently excludes circuits of at most 14 gates. Project acceptance for L-meta-651 remains pending.

## Inspect and reproduce

The two lower-bound theorems are in [AssemblyComplete.lean](verified-15/AssemblyComplete.lean). [Witnesses.lean](Witnesses.lean) contains the 20-gate circuit and the 16-gate witness after deleting one vertex.

From the pinned repository’s `lean` directory with Mathlib and the project definitions built, run `lake env python3 ../research/petersen/verified-15/check15.py` to replay the formal lower bound. The proof uses the definitions at upstream commit `4bb00a9073f9ee99966fde15f28f096b8c828981`.

For the computational result, extract [the replay archive](L-meta-651-exact-size.zip) and run `python3 replay_result.py` in the extracted directory. The archive contains the C++ and Python source, the final case inputs and verification logs. Its SHA-256 digest is `357444d75f958a06e56d55168dd577ca9b37a8075eeebd1a4a26fce875ceaa14`.
