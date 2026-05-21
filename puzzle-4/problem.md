# Trolley Retrieval — Problem Statement

Let c(1), c(2), ... be a sequence of positive integers in which every positive integer appears
exactly once. A one-way infinite sequence of cells is given, where for each positive integer n,
the n-th cell from the left is labelled with c(n).

At time t = 0, an invisible trolley is placed on an unknown cell, namely the k₀-th cell from
the left.

For each integer t ≥ 1, the following events occur in order:

1. Bob chooses a direction, either left or right, and the invisible trolley moves one cell in
   the chosen direction, arriving at the kₜ-th cell from the left.

2. The invisible trolley sends Bob the word **"Yes"** if the label of the cell it currently
   occupies is strictly less than the current time (that is, if c(kₜ) < t), and the word
   **"No"** otherwise.

If at any point the invisible trolley falls off the sequence of cells (that is, if kₜ = 0),
Bob immediately loses.

At any time, Bob may guess the position of the invisible trolley. If the guess is correct,
he safely retrieves the invisible trolley; if the guess is incorrect, he immediately loses.

**Determine all sequences (c(n))_{n≥1} for which Bob has a strategy to ensure the safe
retrieval of the invisible trolley.**
