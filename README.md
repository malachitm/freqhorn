FreqHorn
========

Satisfiability solver for constrained Horn clauses (CHC) based on <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines syntax-guided methods to inductive invariant synthesis with data learning and quantified reasoning over arrays. Find more details at <a href="http://www.cs.fsu.edu/~grigory/freqhorn-arrays.pdf">CAV'19</a> and <a href="http://www.cs.fsu.edu/~grigory/multi-freqhorn.pdf">FMCAD'18</a> papers.

Setup
------

FreqHorn itself is a native C++ project, but the phaserr algorithm also depends on the POLAR Python tool for closed-form generation. In this repository, both `tools/polar` and `pwa-horn-benchmarks` are tracked as Git submodules. A complete setup therefore has three pieces:

1. System packages required to build FreqHorn,
2. the POLAR repository and its Python environment,
3. optionally, the PWA benchmark repository if benchmark analysis is needed.

Quick Startup
-------------

The following set of instructions should be sufficient for setting up the system for Ubuntu/Debian and macOS operating systems.

```bash
git clone https://github.com/malachitm/freqhorn.git
cd freqhorn
./setup.sh
mkdir -p build
cd build
cmake ..
make
make
```

If this does not work, continue to the following instructions.

Preliminary
-----

FreqHorn is developed for Linux and also builds on macOS. Users should have:

* a C++ compiler with C++17 support,
* CMake,
* GNU Make,
* <a href="https://gmplib.org/">GMP</a>,
* Boost (including the system component),
* Armadillo.

If you have an Ubuntu/Debian or macOS system, you can use the following commands to install these dependencies.
-----------------------------------------

**Ubuntu/Debian:**

```bash
sudo apt-get update
sudo apt-get install -y build-essential cmake libgmp-dev libgmpxx4ldbl libboost-system-dev libarmadillo-dev python3 python3-venv python3-pip python3-setuptools gettext python-is-python3 gfortran pkg-config libopenblas-dev liblapack-dev python3-dev libssl-dev zlib1g-dev libbz2-dev libreadline-dev libsqlite3-dev libffi-dev liblzma-dev tk-dev uuid-dev curl wget xz-utils
```

When you use `./setup.sh`, it will automatically install Python 3.12 for POLAR. If `python3.12` is not available from your package repository, the script downloads CPython 3.12 source from python.org and installs it under `~/.local/python-3.12`.

**macOS (using Homebrew):**

```bash
brew update
brew install cmake gmp boost armadillo python3
```

You may also need to install Xcode command line tools if you haven't already:

```bash
xcode-select --install
```

Repository Bootstrap
--------------------

Clone the repository and initialize its submodules:

* `git clone https://github.com/malachitm/freqhorn.git`
* `cd freqhorn`
* `git submodule update --init --recursive`

This populates:
* `tools/polar` from `https://github.com/malachitm/polar.git`
* `pwa-horn-benchmarks` from `https://github.com/malachitm/pwa-horn-benchmarks.git`

If the repository was cloned earlier without submodules, running `git submodule update --init --recursive` later is sufficient.

FreqHorn Build
--------------
From the repository root:

* `mkdir -p build`
* `cd build`
* `cmake ..`
* `make`
* `make`

The first build step is often used to fetch and build dependencies such as Z3; the second builds FreqHorn itself.

The `freqhorn` binary will be located in `build/tools/deep/`.
Run `freqhorn --help` for usage information.

POLAR Setup
-----------

The phaserr flag requires the POLAR submodule to be present at `tools/polar` inside this repository.

POLAR should be set up with **Python 3.12** for compatibility with the pinned requirements. The repository `setup.sh` enforces this automatically.

To create and populate POLAR's virtual environment:

* `cd tools/polar`
* `python3.12 -m venv .venv`
* `source .venv/bin/activate`
* `pip install -r requirements.txt`

If `python3.12` is not on your `PATH` after running `setup.sh`, use:

* `~/.local/python-3.12/bin/python3.12 -m venv .venv`

After that, return to the FreqHorn root. The current `RndLearnerV5.hpp` workflow expects POLAR's interpreter at `tools/polar/.venv/bin/python3` and its script at `tools/polar/closedforms2.py`.

Optional Benchmark Repository
-----------------------------

If the goal is to run benchmark analysis over the PWA benchmark suite, the `pwa-horn-benchmarks` submodule should also be initialized in the workspace.

If it is missing, populate it with:

* `git submodule update --init pwa-horn-benchmarks`

This repository provides benchmark inputs and supporting data for comparing solver behavior; it is not required for building the core `freqhorn` binary.

Typical Workflow
----------------
For a user who wants the full setup, the expected sequence is:

* clone this repository,
* initialize submodules with `git submodule update --init --recursive`,
* set up the POLAR virtual environment in `tools/polar/.venv`,
* configure and build FreqHorn in `build/`,
* run `build/tools/deep/freqhorn` on SMT2 inputs or benchmark files.

FreqHorn does not automatically find counterexamples (unless the CHC system can be trivially simplified), but its supplementary tool `expl` tool does. We recommend running `freqhorn` and `expl` concurrently.

The tools print `Success ...` if the system is satisfiable.

Runthrough
==========

To run the benchmarks as described in Incremental Invariant Synthesis via Closed Forms, run the following command:

`python3 run_benchmarks.py --folder ./benchmark_generator/b01/ --filter-csv satisfiable_benchmarks.csv `