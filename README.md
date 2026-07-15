FreqHorn
========

Satisfiability solver for constrained Horn clauses (CHC) based on <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines syntax-guided methods to inductive invariant synthesis with data learning and quantified reasoning over arrays. Find more details at <a href="https://danielmriley.github.io/papers/elba.pdf">FSE'22</a>, <a href="http://www.cs.fsu.edu/~grigory/freqhorn-arrays.pdf">CAV'19</a> and <a href="http://www.cs.fsu.edu/~grigory/multi-freqhorn.pdf">FMCAD'18</a> papers.

Installation
============

Compiles as C++14. CMake automatically builds Boost 1.91.0, <a href="https://gmplib.org/">GMP</a> 6.3.0, and a recent pinned version of Z3 from the official repository when they are missing or too old. The dependency bootstrap is single-pass: a fresh checkout can be configured once and built with one build command. The bundled Z3 revision requires a recent C++ standard library; on Ubuntu, use GCC/G++ 13 or newer.

Out-of-tree build:

```sh
mkdir build
cd build
cmake .. \
  -DCMAKE_C_COMPILER=/usr/bin/gcc-13 \
  -DCMAKE_CXX_COMPILER=/usr/bin/g++-13 \
  -DCMAKE_PREFIX_PATH="$PWD/deps"
cmake --build . -j3
```

During the first build, CMake downloads and builds any missing bundled dependencies and then immediately continues with the FreqHorn targets. There is no need to rerun CMake or invoke the build command a second time.

On systems where the default compiler is already recent enough, the shorter form is sufficient:

```sh
cmake -S . -B build
cmake --build build -j3
```

The binaries of FreqHorn can be found at `build/tools/deep/` (invariant synthesizer) and `build/tools/bnd/` (bounded model checker).
We recommend running `freqhorn` and `expl` concurrently. Run `freqhorn --help` and `expl --help` for the usage info.

The default FreqHorn's options are `--disj --all-mbp --stren-mbp` (enabled automatically). To start from scratch, begin with `--v4` and experiment with custom setup.

FreqHorn supports both SMT-LIB and Datalog formats for CHCs. To avoid confusion with `sat`/`unsat` results, it print `Success ...` if the system is satisfiable.

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn` and `bench_horn_multiple`. FreqHorn is expected to eventually discover solutions for the systems. On the other hand, there are several unsatisfiable CHC systems at `bench_horn_cex`, for which `freqhorn` is expected to diverge (but `expl` should find counterexamples).
