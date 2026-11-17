# Machine-checked proofs of DDS results

This project proves individual results from [DDS](https://github.com/dds-bridge/dds), the
double-dummy bridge solver, in the [Lean](https://lean-lang.org) theorem prover. For a given
deal, trump suit and declarer, it produces a Lean theorem that the double-dummy result is
exactly the number DDS reported.

It verifies DDS's *answers*, not its source code. Each result gets its own proof, so a
result is covered only if it has been run through these tools.

## How it works

Saying North-South take exactly `k` tricks takes two proofs: a North-South strategy that
wins at least `k` tricks against any defence, and an East-West strategy that wins at least
`13 - k` against any play. Those strategies are the *certificate*.

| Part | File | Role | Must you trust it? |
|---|---|---|---|
| Rules of play | [DdsCheck/Rules.lean](DdsCheck/Rules.lean) | Defines what "correct" means | **Yes: read this file** |
| Rule properties | [DdsCheck/RulesProps.lean](DdsCheck/RulesProps.lean) | Induction over game size, and plain statements of what the rules do in every position | Proved; **check that the statements are the rules of bridge** |
| Strategy theorems | [DdsCheck/Strategy.lean](DdsCheck/Strategy.lean) | `nsTricks_eq_iff`: a generated theorem means each side has a strategy guaranteeing that number | Proved; **check the definitions of lines and strategies** |
| Game length | [DdsCheck/PlaysOut.lean](DdsCheck/PlaysOut.lean) | `valid_deal_plays_out`: on a valid deal every line has exactly 52 cards and leaves every hand empty | No, proved |
| Scoring and par | [DdsCheck/Par.lean](DdsCheck/Par.lean) | Duplicate scoring and the auction game that defines par; `parScore_eq_parFast` proves the fast evaluator matches the game | **Yes for the scoring and the game: read down to `dealPar`** |
| Rank theorem | [DdsCheck/Canon.lean](DdsCheck/Canon.lean) | Only the relative order of ranks matters, so positions can share proofs | No, proved |
| Checker | [DdsCheck/Checker.lean](DdsCheck/Checker.lean) | `checkClaim_sound`: if the checker accepts, the claim is true | No, proved |
| Parser and CLI | [DdsCheck/Format.lean](DdsCheck/Format.lean), [Main.lean](Main.lean) | Read certificates | Not for theorems; see below for `ddscheck` |
| Generator | [tools/ddscert.cpp](tools/ddscert.cpp) | Asks a solver (DDS, altsolve or ddfast) for moves and writes certificates | No |
| DDS | [third_party/dds](third_party/dds) | Supplies the claims and moves | No |
| Second solver | [tools/altsolve.hpp](tools/altsolve.hpp) | An independent solver: checks DDS, and can supply claims and moves instead | No |
| ddfast | [third_party/ddfast](third_party/ddfast) | A fast exact solver: checks DDS, and can supply claims and moves instead | No |

`altsolve` shares no code with DDS and leaves out DDS's shortcuts. With
`ddscert --solver own` (or `SOLVER=own scripts/prove_deal.sh ...`), certificates are built from its
moves instead, and any disagreement with DDS's table is reported. If it disagrees and Lean accepts
its certificate, that is a proof that DDS was wrong on that result.

### ddfast as a move source

[ddfast](https://github.com/randalburns/ddfast) is a separate exact solver for full deals, several
times faster than DDS. With `ddscert --solver ddfast` (or `SOLVER=ddfast scripts/prove_deal.sh ...`)
the claims come from ddfast's table and the moves from its search, and any disagreement with DDS's
table is reported, as with `--solver own`.

ddfast only values positions at the start of a trick (`ddfast::solve_position`). `ddscert` picks a
card in the middle of a trick by searching the rest of that trick itself, trying every reply of
the opponents and asking ddfast for the value of each position at the start of the next trick.
Values are cached by position, with ranks reduced as in the rank theorem.

None of this is trusted: ddfast, the search in `ddscert` and the cache only choose cards. A wrong
value makes `ddscert` stop with an error or produces a certificate that `ddscheck` rejects; it
can never make Lean accept a false claim. ddfast is plain C++ with no Lean in it.

ddfast needs an x86-64 CPU with AVX-512 and BMI2, and Linux; `scripts/build.sh` builds `ddscert`
without it elsewhere. It loads ddclaim's endgame tables (about 1.2 GB of memory per process) from
`$DDCLAIM_DIR`, building them there first if they are missing (about 1.1 GB of files, a few
minutes). ddclaim's tables are part of ddfast (`extern/ddclaim`); ddfast's copy of DDS is not needed.

For the 20 certificates of the example deal under Usage, one core each (calls count the
questions put to a solver; `ddscert` caches DDS's and ddfast's answers by position):

| Move source | Solver calls per certificate | Time per certificate |
|---|---|---|
| DDS (`SolveBoard`, the value of every card) | 627,000 mean (355,000–1,230,000) | 124 s mean (67–222 s) |
| altsolve (`ns_reaches`, one card at a time) | 856,000 mean (400,000–1,759,000) | 5.6 s mean (0.4–18 s; its table is kept from one contract to the next) |
| ddfast (`solve_position`, start of a trick only) | 131,000 mean (55,000–316,000) | 1.1 s mean (0.6–2.5 s), plus about 3 s per process to load tables and solve the deal |

The ddfast and altsolve certificates came out byte for byte the same: both solvers are exact, and
`ddscert` takes the first card that works in the same order for both. On two random deals, ddfast
needed 1.3 s per certificate on average. Checking a certificate in Lean (`lake env lean`) takes
about 80 s and 0.7 GB, whatever the move source.

## Usage

You need Lean ([elan](https://github.com/leanprover/elan)) and `clang++`.

Clone with submodules, because DDS is one. Without them `third_party/dds` is empty, and the build fails:

```sh
git clone --recurse-submodules https://github.com/randalburns/ddscheck.git
cd ddscheck
```

If you've already cloned without them, run `git submodule update --init`. (`--recurse-submodules`
also fetches ddfast's own copy of DDS, which nothing here uses.)

```sh
scripts/build.sh

# Certify and check all 20 table results for a deal
scripts/prove_deal.sh "N:QJ6.K652.J85.T98 873.J97.AT764.Q4 K5.T83.KQ9.A7652 AT942.AQ4.32.KJ3" out

# Certify one contract and generate a Lean theorem for it
build/ddscert --pbn "N:QJ6.K652.J85.T98 873.J97.AT764.Q4 K5.T83.KQ9.A7652 AT942.AQ4.32.KJ3" \
  --strain S --declarer N -o spades.cert
.lake/build/bin/ddscheck spades.cert
.lake/build/bin/ddscheck --lean Spades.lean spades.cert
lake env lean Spades.lean
```

The generated file contains a theorem like this, and `lake env lean` prints the axioms it uses:

```lean
theorem S_E_leads : validDeal deal ∧ nsTricks (some .spades) deal .east = 5
```

Results are stated for North-South, with the opening leader to the left of declarer.

### Par scores

```sh
# Certify the table, get DDS's par score, and check it against the proved value
scripts/prove_par.sh "N:QJ6.K652.J85.T98 873.J97.AT764.Q4 K5.T83.KQ9.A7652 AT942.AQ4.32.KJ3" none N out

# Generate and check a Lean theorem for par (slow: it checks all 20 results)
.lake/build/bin/ddscheck --par-lean out/DealPar.lean none N -110 out/*.cert
lake env lean out/DealPar.lean
```

Vulnerability is `none`, `both`, `ns` or `ew`, and scores are from North-South's point of view:

```lean
theorem par : validDeal deal ∧ dealPar deal .none .north = (-110 : Int)
```

Par is defined as the result of an auction with open cards: clockwise from the dealer, each player
passes or bids higher and becomes declarer, ending after three passes (four if nobody has bid). A
failing contract scores doubled and a making one undoubled. This follows DDS's own definition.

## What you are trusting

- **[Rules.lean](DdsCheck/Rules.lean)**, to state bridge correctly. As a cross-check,
  [tests/RulesExamples.lean](tests/RulesExamples.lean) proves hand-checkable positions (ruffs,
  following suit, finesses), and [tests/SpecVsDds.lean](tests/SpecVsDds.lean) compares it
  directly with DDS on small endgames.
- **Lean's kernel.** The rules, the rank theorem and `checkClaim_sound` use only Lean's
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Lean's compiler, for full deals.** Generated theorems use `native_decide`, because
  certificates with hundreds of thousands of facts are expected to be impractical in the
  kernel (this has not been attempted). They therefore also depend on an axiom stating what
  the compiled checker returned, and `#print axioms` shows it.
- **`ddscheck` adds its own printing and file handling.** A `PROVED` line is the output of a
  program; only the generated theorems are statements checked by Lean. `ddscheck` is the fast
  way to check many results.

## Limits

- **Only trick counts from the opening lead and par scores are proved.** `AnalysePlay`,
  mid-play positions and DDS's lists of par contracts are not covered.
- **A wrong answer never yields a false proof.** With DDS supplying the moves, a wrong answer shows
  up as a generator error or a rejected certificate. To find the correct value, use `--solver own`
  or `--solver ddfast`.
- **Certificates are large:** 3–29 MB per contract in testing, depending on the deal.

## Tests

```sh
# Tamper tests: false claims and corrupted certificates must not be proved
python3 tests/tamper.py spades.cert 40

# Rules on hand-checkable positions (kernel only), and the axioms of the core theorems
lake env lean tests/RulesExamples.lean

# Scoring and auctions on hand-checkable cases (kernel only)
lake env lean tests/ParExamples.lean

# The par evaluator against DDS, on real and altered tables
mkdir -p build/par
clang++ -std=c++20 -O2 -Ithird_party/dds/library/src tests/par_vs_dds.cpp build/dds/libdds.a -o build/par/par_vs_dds
build/par/par_vs_dds 100 200 1 > build/par/cases.txt
lake build parvsdds && .lake/build/bin/parvsdds build/par/cases.txt

# DDS against independent solvers (seconds, seed, max tricks, solver, min tricks).
# `both` also compares altsolve with brute force, up to about 6 tricks; `smart` reaches 13.
clang++ -std=c++20 -O2 -Ithird_party/dds/library/src tests/dds_stress.cpp build/dds/libdds.a -o build/dds_stress
build/dds_stress 60 1 6 both
build/dds_stress 60 1 10 smart 7

# What each altsolve technique contributes, and how it scales
clang++ -std=c++20 -O2 tests/solver_bench.cpp -o build/solver_bench
build/solver_bench stages 6 40
build/solver_bench scale 13 5

# Rules against DDS on random endgames
clang++ -std=c++20 -O2 -Ithird_party/dds/library/src tests/spec_vs_dds.cpp build/dds/libdds.a -o build/spec_vs_dds
build/spec_vs_dds 300 > build/endgames.txt
lake build specvsdds && .lake/build/bin/specvsdds build/endgames.txt
```

## DDS version

`third_party/dds` is a git submodule, pinned to commit `ea66294` and unmodified. DDS has its own Apache-2.0
license. [scripts/build_dds.sh](scripts/build_dds.sh) compiles it directly, so Bazel isn't needed.

## ddfast version

`third_party/ddfast` is a git submodule that follows ddfast's `main` branch. ddclaim's endgame
tables are inside it (`extern/ddclaim`, no longer a submodule of their own), so nothing below it
needs initialising. ddfast and ddclaim have their own Apache-2.0 licenses.

## License

This project is licensed under the [Apache License 2.0](LICENSE).
