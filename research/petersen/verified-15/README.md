# Petersen graph lower bound of 15 gates

Lean 4.36.0 verified that the Petersen edge function requires at least 15 binary gates even if every wire can be complemented for free. It also verified the corresponding result for ordinary fan-in-two AND/OR/NOT circuits. The statements are `PetersenSigned.Petersen.Fifteen.signed` and `PetersenSigned.Petersen.Fifteen.ordinary` in `AssemblyComplete.lean`. The circuit and size definitions come from the PEqualNP project's `PEqualNP.Defs`.

The proof restricts the ten-vertex problem to seven-vertex induced subgraphs. Its two smaller computations cover a five-cycle and the four polarities of a free gate joining opposite vertices on a six-cycle. Each search is checked by the Lean kernel. The project assignment requires a lower bound of 20 total gates.

Extract this archive. From the pinned PEqualNP repository's `lean` directory with Mathlib and `PEqualNP.Defs` already built, run `lake env python3 /absolute/path/to/check15.py`. The script checks the modules in dependency order in a temporary directory. Verification logs from the original build are under `results/`.
