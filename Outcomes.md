# Outcomes

Status at 2026-11-06, for [DDS](https://github.com/dds-bridge/dds) commit `ea66294`.

**In short:** any trick count from the opening lead, or par score, can now be proved correct deal by
deal, and the proof doesn't rely on DDS being right. Every DDS result checked so far has been correct,
and no DDS bug has been found. DDS itself has not been proved correct.

## 1. What has been proved

### Theorems that hold for every deal

Lean's kernel has checked these, with no `sorry` anywhere in the source. They use only Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`), and none relies on the compiler.

| Theorem | File | What it says |
|---|---|---|
| `checkClaim_sound` | [Checker.lean](DdsCheck/Checker.lean) | If the checker accepts a certificate, the deal is valid and its result is exactly as claimed. This holds for **any** certificate, so its source needn't be trusted |
| `nsTricks_eq_iff` | [Strategy.lean](DdsCheck/Strategy.lean) | "North-South take exactly `k`" means North-South have a strategy taking at least `k` against every defence, and East-West have one holding them to at most `k` |
| `minimax_eq_value` | [RulesProps.lean](DdsCheck/RulesProps.lean) | Rules that agree on legal cards and on what playing a card does give the same value, at any size |
| `legal_*`, `play_*`, `step_*`, `winner_*` | [RulesProps.lean](DdsCheck/RulesProps.lean) | What following suit, playing a card and winning a trick do, for every position |
| `value_canon` | [Canon.lean](DdsCheck/Canon.lean) | Only the relative order of ranks within a suit affects the value |
| `valid_deal_plays_out` | [PlaysOut.lean](DdsCheck/PlaysOut.lean) | On a valid deal, every line of play has exactly 52 cards and ends with all hands empty |
| `parScore_eq_parFast` | [Par.lean](DdsCheck/Par.lean) | The fast par evaluator always gives the same result as the auction game that defines par |

### Results for specific deals

Each result takes two proofs, one for each side's bound. All the results below match what DDS reported.

There are two levels of evidence:
- **Lean theorem:** a theorem about the deal, checked by Lean.
- **`ddscheck`:** the compiled checker accepted the certificate. This relies on the same soundness
  theorem, but its `PROVED` line is program output, not a statement Lean has checked.

| Deal | Results | Evidence |
|---|---|---|
| DDS reference deal | All 20 table results, using DDS's moves | Lean theorems |
| DDS reference deal | Par of -110 (2♠ by East-West), no vulnerability, North dealing | Lean theorem |
| DDS reference deal | All 20 table results and the same par, using the second solver's moves | `ddscheck` |
| DDS reference deal | 5 tricks for North-South in spades, East on lead, using the second solver's moves | Lean theorem |
| Random deal 1 | 11 tricks for North-South in spades, East on lead | Lean theorem and `ddscheck` |
| Random deals 1–4 | Notrump and spades by North: 8 results | `ddscheck` |

The reference deal is `N:QJ6.K652.J85.T98 873.J97.AT764.Q4 K5.T83.KQ9.A7652 AT942.AQ4.32.KJ3`. Its proved
table shows the tricks declarer takes:

| | North | East | South | West |
|---|---|---|---|---|
| Notrump | 6 | 6 | 6 | 6 |
| Spades | 5 | 8 | 5 | 8 |
| Hearts | 6 | 6 | 6 | 6 |
| Diamonds | 5 | 7 | 5 | 7 |
| Clubs | 7 | 5 | 7 | 5 |

The random deals are:

| Deal | Hands | North-South tricks, East on lead |
|---|---|---|
| 1 | `N:A643.KJT8.92.AK3 2.653.QJT7.T9842 KQ97.Q9.AK54.J75 JT85.A742.863.Q6` | Notrump 11, spades 11 |
| 2 | `N:AK.KQT.JT82.AT62 QJ875.9872.97.Q4 T9632.J53.Q3.J83 4.A64.AK654.K975` | Notrump 8, spades 6 |
| 3 | `N:J764.QT64.K95.KJ AQ2.KJ82.63.Q864 T93.A7.JT7.AT932 K85.953.AQ842.75` | Notrump 6, spades 7 |
| 4 | `N:9842.952.4.AKQ87 KJ.Q8.AKQ8653.J5 Q76.AJT3.JT7.T63 AT53.K764.92.942` | Notrump 4, spades 7 |

The generated theorem files aren't kept in the source. The commands in the [README](README.md) regenerate
them. The full table and par theorem were checked before the project was renamed. Since then, a
single-contract theorem has been checked under the new name, while the table and par were rerun with
`ddscheck` only.

### What these proofs rest on

- **[Rules.lean](DdsCheck/Rules.lean):** it has to state bridge correctly. Lean can't check that, so it
  relies on a person's review. [Rules.lean.md](DdsCheck/Rules.lean.md) is a guide.
- **[Par.lean](DdsCheck/Par.lean), down to `dealPar`:** it has to state the scoring and par correctly. See
  [Par.lean.md](DdsCheck/Par.lean.md).
- **Lean's kernel and compiler:** full-deal theorems use `native_decide`, so they also trust the compiler.
  `#print axioms` shows this on each theorem.

**The project owner has proofread these definitions and the theorem statements.** The rules and scoring have
also passed the tests in section 2. A proof is still only as good as that review, as Lean can't check whether
the definitions describe bridge.

### What has not been proved

- **That DDS is correct in general.** Nothing here models its C++ code, so a deal that hasn't been run has
  only DDS's word behind it.
- **DDS's other results:** `AnalysePlay`, mid-play positions and its lists of par contracts.
- **That the par model matches DDS on every table.** It's agreed on every comparison, but that's evidence,
  not a proof.
- **That the auction's maximizing and minimizing are the right way round.** Card play has a strategy
  theorem protecting against this, but the auction relies on review and testing.
- **East-West's tricks directly.** `declarerTricks` takes them as 13 minus North-South's. That's correct,
  but no theorem counts them separately and shows the two add up to 13.

## 2. Tests to date

### The rules and scoring

| Test | Amount | Result |
|---|---|---|
| Hand-checkable positions (ruffs, following suit, finesses), in the kernel | 9 positions | All pass |
| Scoring and auction examples (sacrifices, dealer decides), in the kernel | [ParExamples.lean](tests/ParExamples.lean) | All pass |
| Lean rules run directly, against DDS, on endgames of up to 4 tricks | 1,600 positions | All agree |
| Max and min swapped in a copy of the rules | 1 | Proofs stopped compiling |

### Certificates and the checker

| Test | Amount | Result |
|---|---|---|
| False trick counts | All 13 wrong values, on each of 5 test runs | All rejected |
| Wrong strain or opening leader | All alternatives, on each of those runs | All rejected |
| Random bit flips | 118 | 114 refused, 4 still proved the true result, **0 false proofs** |
| A card swapped between hands in a generated theorem | 1 | Failed to compile |
| Wrong par scores (`ddscheck`) | 4 | All rejected |
| Wrong par score in a generated theorem | 1 | Failed to compile, using a copy with the card-play proofs stubbed out |
| One table result missing from a par check | 1 | Refused |

The 4 surviving bit flips weren't investigated individually. They most likely changed something the proof
doesn't depend on.

### DDS itself

`SolveBoard` was compared with independent solvers on three things: the score of every legal card, the best
score and a card achieving it, and every possible target, including whether the returned card reaches it.
The positions were aimed at `quick_tricks` and `later_tricks`: uniform random, few suits, runs of top cards,
stranded winners and sparse ranks, some with a trick in progress.

| Compared with | Size | Positions | Differences |
|---|---|---|---|
| Brute force | Up to 6 tricks | 35,225 in the main run | 0 |
| Brute force and the second solver | Up to 6 tricks | 10,253 | 0 |
| The second solver | 7–10 tricks | 14,153 | 0 |
| The second solver | 10–12 tricks | 293 | 0 |
| The second solver | 13 tricks | 16 | 0 |

**Can this test find bugs?** Two bugs planted in copies of the DDS routines were both caught, one with 47
errors and the other 24, in about 1,000 positions each.

**Line coverage** was 97.1% of `quick_tricks.cpp` and 91.3% of `later_tricks.cpp`. Section 4 explains the
missed lines.

### Par

Par was compared with DDS's `DealerPar`. Altered tables matter here, because on the 4,000 real deals sampled
the dealer never changed par, so those alone can't test the dealer rule.

| Evaluator | Cases | Dealer-sensitive | Differences |
|---|---|---|---|
| C++ prototype, real deals | 64,000 | 0 | 0 |
| C++ prototype, altered tables | 400,000 | 610 | 0 |
| Lean evaluator, real and altered tables | 173,460 | 453 | 0 |

Of three bugs planted in the prototype, two were caught. The third, ignoring the dealer, wasn't caught by
the real-deal sample, which is what led to adding altered tables. It wasn't rerun against them.

### What hasn't been tested

- **`AnalysePlay` and batch calls.** The DDS README reports a past correctness fix to `AnalysePlay`, so it's
  the next place to look.
- **Multi-threaded use.** All these runs used one thread.
- **Every condition in the routines.** Running a line isn't the same as testing it at every boundary.
- **Whether the rules in `quick_tricks` and `later_tricks` are sound.** Section 4 maps which lines can run,
  and isn't an audit of their logic.
- **The DDS branch of `ddscert`'s contradiction error,** which has never fired. The same check in the second
  solver's branch did fire, on planted bugs.
- **DDS at full size.** Only a tiny share of all deals has been sampled.

## 3. The second solver

[altsolve.hpp](tools/altsolve.hpp) is a double-dummy solver of about 300 lines of C++ that shares no code with
DDS. It has two jobs: an independent check on DDS at sizes brute force can't reach, and a second source of
moves for certificates, so that a proof can be built with no DDS moves involved.

### How it works

It answers yes-or-no questions of the form "can North-South take at least `t` tricks?", and finds an exact
value by binary search. It uses:

- **Alpha-beta cutoffs:** it stops as soon as one card meets the target, or one reply refutes it.
- **A table of remembered positions:** it stores upper and lower bounds at the start of each trick.
- **Relative ranks:** positions that differ only in actual ranks share a table entry.
- **Touching cards:** it tries only one card from a run of equivalent cards.
- **Simple move ordering:** it tries likely winners first, such as the cheapest card that wins the trick.

It deliberately leaves out shortcuts like `quick_tricks` and `later_tricks`, and DDS's reuse of table entries
across partly matching positions. Those are hard to get right and are what's being tested. Leaving them out makes
it slower.

### Speed

On one core, per value:

| Tricks per hand | Time | Sample |
|---|---|---|
| 7 | 0.014 seconds | 40 positions |
| 10 | 0.064 seconds | 20 positions |
| 11 | 0.25 seconds | 10 positions |
| 13 | 7 seconds on average, 18 at worst | 5 deals |

For comparison, the brute-force solver took about 10 seconds per position at 7 tricks, and would take an
estimated week at 10. At small sizes, most of the solver's time goes on clearing its table.

Each technique reduces the search. At 6 tricks, the nodes per position fall as follows:

| Techniques | Nodes per position |
|---|---|
| Alpha-beta only | 133,292 |
| + remembered positions | 19,085 |
| + relative ranks | 5,401 |
| + touching cards | 4,313 |
| + move ordering | 2,518 |

### How far to trust it

It hasn't been proved correct. It's been checked in these ways:
- **Against brute force and DDS:** no differences, as in section 2.
- **Planted bugs:** four bugs in copies were all caught by the stress test, and in the certificate pipeline
  all four stopped with an error and no certificate. So none produced a false proof.
- **Through Lean:** a full 20-result table built from its moves was accepted by `ddscheck`.

For a certificate, it doesn't need to be trusted, because Lean checks the result. A plain comparison with DDS
does depend on its testing.

If it ever disagreed with DDS and Lean accepted its certificate, that would be a machine-checked proof that DDS
was wrong on that result. That hasn't happened, since they've never disagreed, so that path hasn't run for real.

## 4. Dead code in DDS

The tests never ran 48 lines of `quick_tricks.cpp` and `later_tricks.cpp`. Reading the code shows that none of
them can run in normal operation, so **the tests have run every line of these two routines that can run**.

This doesn't indicate a bug in DDS. The lines are harmless, and don't affect its answers. All of this comes from
reading the code, not from a formal proof.

| Kind | Lines | Can it run? |
|---|---|---|
| Dead code | 19 | No, whatever the data |
| Effectively dead | 1 | No, given the one place DDS calls the routine |
| Defensive guards | 20 | Only with invalid values |
| Consistency-dependent | 8 | Only if DDS's position data contradicted itself |

### Dead code: 19 lines

**`quick_tricks.cpp` 515–532 (17 lines).** This block handles a suit where partner and both opponents are void,
and is guarded by these local values:

```cpp
if ((countPart == 0) && ...)
    ...
    else if ((countRho == 0) && (countLho == 0))
```

But the loop has already handled that case near its top. `opps` is `countLho | countRho`, so when all three are
0, this earlier test is true, and every path through it ends in `continue`:

```cpp
if (!opps && (countPart == 0)) // line 253
```

So the code at line 514 can never see that case.

**`quick_tricks.cpp` 399 and 406 (2 lines).** These test `sum >= cutoff` and return. The same test, on the same
values, has already run at lines 320 and 327, and returned if it was true. Nothing changes those values in between.

### Effectively dead: 1 line

**`quick_tricks.cpp` 577.** This reads `if (qtricks >= cutoff) return qtricks;`. It can't be true by this point:
- **Every increase is already checked.** All 28 updates to the trick count in the helper functions, and the
  increases in `QuickTricks` itself, are followed immediately by this same test and a return.
- **`cutoff` is at least 1.** The entry checks in `ab_search.cpp` return early if the target is already reached
  or can't be reached, which guarantees this. So a count of 0 can't meet it either.

`ab_search.cpp:350` is the only call in DDS's solver. DDS's own unit tests also call `QuickTricks` directly, but
that doesn't affect real solving.

### Defensive guards: 20 lines

All of these are in `later_tricks.cpp`, and they protect against impossible values:

| Lines | Guard |
|---|---|
| 70–72, 241–243 | A winning seat outside 0–3 |
| 118, 140, 172, 291, 316, 347 | A seat outside 0–3 |
| 163–166, 338–341 | `aggr` of 8192 or more, when `aggr` is a 13-bit mask of ranks |

They'd only run if something else had already gone wrong, such as memory corruption. They're sensible to keep,
since they stop a bad value from causing a crash.

### Consistency-dependent: 8 lines

These could run only if DDS's records of a position disagreed with each other:

| Lines | Case | Why it can't happen |
|---|---|---|
| `later_tricks.cpp` 115, 288 | No second-best trump | One side holds the top trump and the other side holds a trump, so at least two exist |
| `later_tricks.cpp` 169, 344 | No third-best trump | One side holds the top trump and the other holds at least two, so at least three exist |
| `quick_tricks.cpp` 414–417 | A suit with no winner | An empty suit has already taken the `continue` at line 258 |

As with the guards, a position reaching these lines would be a symptom of a bug elsewhere, not the bug itself. A
wrong answer from such a bug should still show up in the comparisons with the other solvers.

### What this leaves open

- **Assumption:** the consistency-dependent lines assume that DDS's lengths, ranks and winners agree. That wasn't
  separately verified. DDS's input checks and these tests are consistent with it.
- **Line coverage only:** a wrong `<=` on a line that ran could still go unnoticed if its exact boundary never came up.
- **Not a soundness audit:** this shows which lines can run, not that each rule is right. The ruff and "can reach
  partner" rules would be the first to audit.

None of this has been reported to the DDS project. The dead code could be removed there with no change in behaviour.
