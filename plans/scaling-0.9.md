# Moving the benchmarks to `scaling` 0.9

Status: **implemented** on branch `scaling-0.9` (2026-10-10); what follows is the
plan it was built from, plus "As built" at the end for where it differs.
Planned for the long run: the first internment release whose benchmarks use
scaling 0.9 becomes the baseline every later release is measured against.

internment uses `scaling` only in `benches/bench.rs` (the other bench,
`get_container.rs`, is criterion). It calls two functions, `bench` and
`bench_gen_env`, from `scaling = "0.1.3"`. Neither exists in 0.9.0: the crate
was rewritten around declared benchmarks (`#[scaling::bench]`, `#[input]`,
groups, baselines) run from a `main` of one call. There is no compatibility
shim, so this is a rewrite of the bench file, not a version bump.

## Facts this rests on

- `scaling` / `scaling-macros` 0.9.0 are on crates.io; scaling's
  `rust-version` is 1.81 (internment's is 1.70).
- **Verified:** a crate with `scaling = "0.9.0"` as a *dev*-dependency fails
  `cargo +1.71.0 test --no-run` with "package `scaling-macros v0.9.0` cannot be
  built because it requires rustc 1.81". The `msrv` CI job runs `cargo test`,
  which builds dev-dependencies, so a plain dev-dependency bump would break
  it. Hence scaling must not be a dev-dependency.
- **Verified:** with scaling as an *optional normal* dependency, and the
  published release as another (below), `cargo +1.71.0 test --no-run` and
  `cargo +1.71.0 check` pass (in a scratch copy, see the caveat), and
  `cargo check --features bench` builds the library with both. Optional
  dependencies are only built when the feature is on.
- **Caveat, separate and already present on master:** a fresh resolve of the
  *unmodified* repo fails `cargo +1.71.0 test --no-run` because dev-dependency
  `criterion 0.4` pulls in `half 2.7.1` (needs 1.81) and `textwrap 0.16.4`
  (needs 1.88). So the `msrv` job's `cargo test` probably does not pass today
  regardless of scaling (`Cargo.lock` is gitignored, so CI resolves fresh); I
  could not see recent CI runs to confirm. My scratch check of scaling's effect
  was done with criterion removed. Decide separately whether to pin, drop
  criterion from the 1.70 job, or bump the job (see step 2).
- **Verified:** `cargo check --benches --features bench` already fails on
  master: `bench.rs` uses `arc_interner::ArcIntern`, but the `bench` feature
  does not enable the optional `arc-interner` dependency. Fixed in step 1.
- Reference suite of the shape we want, by the same author:
  `~/src/tinyset/benches/versions.rs` (this release against the previous one,
  one group per operation, `#[global_allocator]` for memory metrics).
  `~/src/compactly/plans/scaling-0.9.md` is the sibling plan; it verified that
  a renamed published copy of one's own crate can be a dependency
  (`published = { package = "...", version = "=x.y.z" }`).

## Design decisions

1. **No new workspace member; two features, everything optional.** In root
   `Cargo.toml`:
   ```toml
   [dependencies]
   scaling = { version = "0.9.0", optional = true }
   internment_old = { package = "internment", version = "=0.8.6", default-features = false, features = ["bench"], optional = true }
   # arc-interner already optional

   [features]
   bench = ["arc", "arena", "_experimental-new-intern", "dep:memorable-wordlist"]   # unchanged meaning
   benchmarks = ["bench", "dep:arc-interner", "dep:scaling", "dep:internment_old"]
   ```
   Remove `scaling = "0.1.3"` from `[dev-dependencies]`; the bench targets get
   `required-features = ["benchmarks"]`. A dev-dependency cannot be optional,
   hence `internment_old` is a normal optional dependency.
   **Why two features (verified in a scratch copy, builds on stable; 1.71
   `check`/`test --no-run` pass apart from the criterion caveat):**
   `benchmarking_only_clear_interns` is `#[cfg(feature = "bench")]` in both
   0.8.6 and master, so the old release must be built with *its* `bench`
   feature. If `bench` also pulled in scaling and the previous release, then
   once this version is published as "the old one", enabling its `bench` would
   pull *its* predecessor, and so on down every release. Keeping `bench` as the
   minimal hook and putting the suite in `benchmarks` makes each release's
   `bench` a leaf. Do this split in the very release that first ships the
   scaling benchmarks; it is the one decision that is hard to change later.
   - `rand` (0.7, used by the bench) stays a dev-dependency; benches can use
     dev-dependencies. `get_container.rs` (criterion) is untouched.
   - Anyone enabling `benchmarks` pulls scaling and the old release; it is an
     undocumented benchmarking feature, so mark it so in `Cargo.toml`.
   - The old release's API must be a subset: `Intern`, `ArcIntern`, `Arena`
     exist in 0.8.6; `Intern32` and `NewIntern` do not (see the release cycle).
2. **Comparisons are groups.** Every workload in the old file is already a
   matrix of interner type × {contended, uncontended}. In 0.9 that is one
   group per (workload, contention) with one candidate per interner, `Intern`
   as `baseline`. The old hand-aligned labels ("Uncontended &'stat... ArcIntern")
   disappear; the report names things by group and candidate.
3. **Macros stay, but emit attributes.** *(upstream, and built here)* A
   `macro_rules!` emitting `#[scaling::bench(group = .., name = ..)]` works,
   including for zero-argument candidates in a group with no `#[input]` (tried
   in a scratch crate: `fill  baseline: A`, `B (< 0.8%)`). Rules: `name =` must
   be a string literal, so the macro takes `$label:literal` (`stringify!` is
   rejected); idents cannot be pasted, so each fn name is passed as
   `$fn:ident`; and every candidate needs a distinct `name =` or the group is a
   `RegistrationError`. `types(A, B)` is for a candidate generic in its
   *input* type; it does not stamp one body over N interner types, so the
   workloads stay macro-generated functions.
4. **Global-state reset stays at the start of the candidate body**, as today
   (`$intern::<T>::benchmarking_only_clear_interns()` first) *(upstream)*.
   Not `make_input` / `#[input]`: a generator runs for a whole timed stretch's
   inputs up front and the stretch then calls back to back, so a reset there
   does not give each call a clean slate. The scheduler is single-threaded and
   runs one benchmark's round at a time, so there is no concurrent
   interference; but a leftover in a global table is seen by the next
   benchmark on that type, in random order each round. The clear is timed,
   equally for every candidate, which is fair if every candidate does it
   (the existing macros already do, except the `Arena` ones, which have no
   global table). Different interner types have different tables. The
   micro-benchmarks that call `Intern::new(random)` grow a table without
   clearing; either clear in the body or accept steady-state growth. If two
   workloads on one type must not see each other, run them separately with
   `Config::filter_groups`.
5. **Thread-spawning candidates** ("contended", 50 threads per call)
   *(upstream; the affinity inheritance is standard Linux, untested)*. Pinning
   only happens when a CPU reservation exists (`quiet-bench reserve`);
   without one, nothing is pinned and the 50 threads use all cores. With one
   reserved CPU they time-slice on it and "contended" means something else.
   So: contended groups run with `SCALING_NO_PIN=1` or with enough CPUs
   reserved (`reserve 2-5`). Note it in the benchmark README.
6. **Fixed-state micro benchmarks** (the `HashSet<String>` build/compare/sort
   benches using `bench_gen_env`) become `#[scaling::input]` + `&mut I`
   candidates. Their input is a `Clone` hash set cloned per iteration, so
   they take `&mut I` from a non-`reuse_input` input: timed on fresh inputs,
   the same thing `bench_gen_env` did. The pure `Intern::clone` / `eq` ones
   take `&I` and are pooled and warm; check that is acceptable.
7. **New capability: this release vs. the last** (see "The release cycle"). With `internment_old` as an
   optional dependency, each interner (`Intern`, `ArcIntern`, `Arena`) gets a group
   whose baseline is the 0.8.6 type and whose candidate is the current one,
   at the default 1% accuracy. This is the comparison most worth having
   during the in-progress refactor. `Intern32` (new, no old counterpart) is a
   plain extra candidate against `Intern`.
8. **`-C llvm-args=-align-all-functions=6`**: recommended in scaling's README
   (via `.cargo/config.toml` or `RUSTFLAGS`, documented in the benchmarking
   note rather than committed, since it would apply to every build in this
   directory), since the old-vs-new comparison
   of tiny functions is exactly where code placement shows up.

## Layout of the benchmark targets

Follow tinyset (`versions` / `libraries` / `controls`) rather than one 800-line
file. Each is its own binary with its own `Config`, all
`required-features = ["benchmarks"]`:

- `benches/versions.rs`: **this tree against `internment_old`**, at the
  default 1% accuracy. One group per operation and interner type (`new`,
  `from`, `clone`, `eq`/hash, set build, sort ...), baseline the old type. It
  is the suite whose answer is "did this change make anything slower or
  larger?". Installs `scaling::Allocator`, so the groups that build tables also
  report memory.
- `benches/libraries.rs`: the cross-library and cross-type picture at a rough
  10-20% accuracy (`String`/`HashSet` baselines, `arc_interner::ArcIntern`,
  the interners against each other, `Intern32` against `Intern`).
- `benches/controls.rs`: the same comparison, between code that should perform
  identically, to measure what separate compilation alone does (a type against
  its own twin built from the same source). Required before believing any
  small difference in `versions.rs`; scaling's README gives the recipe.
- `benches/contended.rs`: the ~50-thread workloads, in a binary of their own
  so they can be run with `SCALING_NO_PIN=1` (decision 5) and, if needed, a
  smaller `max_time`, without affecting the others. Uncontended variants live
  in `versions.rs` / `libraries.rs`.

## The release cycle (planning for the published version)

Right now the baseline is 0.8.6, which predates scaling. The next release
that ships these benchmarks (call it N) is the first one a later release can
be compared against *with the same harness*. Each release then runs:

1. **Before releasing N+1:** `cargo bench --features benchmarks --bench versions`
   (with `-C llvm-args=-align-all-functions=6`), plus `controls` to know the
   noise floor. Record the notable differences in the CHANGELOG entry; no
   committed numbers (machine-dependent).
2. **After publishing N+1:** bump `internment_old` to `=N+1` (and delete or
   `#[cfg]` out any group whose type did not exist in the old release; a type
   new in N+1 is a candidate-only entry until N+2). Same-name-same-version
   from two sources (path and registry) is supported (compactly verified it),
   so the pin may be bumped before or after the version bump in `Cargo.toml`.
3. **If the old release drops or renames API** the benchmark uses (e.g. the
   clear hook), `internment_old`'s calls break at compile time, which is the
   intended alarm; fix by adjusting the shim in one place: put every
   `internment_old::...` use in a small `old` module of re-exports in
   `benches/common/mod.rs`, so API drift between releases is a one-file edit.
4. **Published manifests carry the optional dependencies forever.** N's
   registry copy lists `scaling = "0.9"` and `internment_old = "=N-1"` as
   optional. Harmless: never built unless `benchmarks` is on, and
   `internment_old` enables only the leaf `bench` feature, so N-1's own
   benchmark dependencies are never pulled in. A later scaling 0.10 is an
   ordinary bump of the root dependency.
5. **Yanked pins:** `=N` pins to a specific release; if it is ever yanked,
   resolution for `benchmarks` breaks. Unlikely; bump the pin.

## Steps

1. **Unbreak the current bench** (separate commit, small): add
   `dep:arc-interner` to the `bench` feature; confirm
   `cargo check --benches --features bench` passes. (Interim only: this
   whole file is replaced in steps 3-5.)
2. **Switch the dependencies and split the features** as in decision 1
   (`benchmarks`, optional scaling and `internment_old`, scaling out of
   dev-dependencies). Do this together with step 1, in one change. Check `cargo +1.71 check`,
   `cargo +1.71 test --no-run` (with the criterion caveat above), and that
   `cargo test --all-features -- --test-threads=1` still passes on stable.
   Separately decide what to do about the criterion/MSRV failure.
3. **`benches/common/mod.rs` and `versions.rs` first** (the new capability):
   the `old` re-export module, then `Intern`, `ArcIntern`, `Arena` groups
   against `internment_old` for `new`, `from`, `clone`, and the string-set
   build/compare/sort workloads. Get one group end to end before the rest.
4. **`controls.rs`** for the same groups, so the noise floor exists before any
   result in `versions.rs` is believed.
5. **`libraries.rs`**: port the micro benchmarks (`HashSet<String>` build,
   compare, sort, any-eq; `Intern::new`, `clone`) with `String` / `HashSet` and
   `arc_interner::ArcIntern` as baselines and rough accuracy; add `Intern32`
   against `Intern`. Sanity-check numbers against the last recorded output of
   the old bench.
6. **`contended.rs`** and the uncontended macro workloads (static_str,
   few_strings, few_str_from, few_strings_from, strings, four_types,
   same_arrays, different_arrays): one group per workload, one candidate per
   interner, `Intern` baseline. Settle state-reset and pinning (decisions 4, 5)
   first, then measure how long a full run takes (see below).
7. **Delete `benches/bench.rs`** when its last piece is ported, and replace its
   `[[bench]]` entry with the four above.
8. **Docs and CI**: a "Benchmarking" note in README (the commands, the
   align-functions flag, `quiet-bench`, `SCALING_NO_PIN`); CHANGELOG notes the
   new `benchmarks` feature; CI gets
   `cargo check --benches --features benchmarks` on stable only (not on 1.70).

## Answers from the scaling session (2026-10-10)

1. No compat shim: `bench`, `bench_env`, `bench_gen_env`, `bench_scaling`,
   `Stats` are gone; `scaling::bench` is now an attribute macro.
2-5. Folded into the design decisions above. Also: a `&mut I` candidate is
   handed a fresh clone per call (built outside the timing, paid from
   `max_time`); `reuse_input` is only for candidates that put the input back,
   so not for ours; `&I` candidates are pooled automatically; and if any
   candidate of a group takes `&mut I` from a non-reuse input, the whole group
   is timed on fresh clones. Large inputs shorten the timed stretch.
6. MSRV: scaling resolves under cargo 1.66 and 1.71 and `cargo check` of the
   library passes there, but any job that builds tests/benches needs 1.81+,
   matching what I measured (the optional-dependency layout avoids it, above). The one real risk is a committed `Cargo.lock`
   written by a newer cargo (v4); ours is gitignored, so it does not apply.

Remaining open: whether the 1% default accuracy and the 10 s per-group limit
make the full suite tolerably long. The old macros do ~5M interns per call,
and the interleaved scheduler gives every benchmark the full budget, so
expect a full run to take `n` times `max_time`. Measure after step 4; the
likely answer is `with_max_time` and the `filter_groups` split above.

## Feedback on the 0.9.0 release (sent to the scaling session 2026-10-10)

- `rust-version = "1.81"` is a hard error for any crate that builds tests or benches on an older
  toolchain (verified; `cargo check` of the library alone is fine, as the
  scaling session confirmed).
  Worth a line in the README's install section, since the old 0.1 had no
  such floor.
- The README has no "migrating from 0.1" section; `bench` / `bench_gen_env`
  users hit a compile error with no pointer. A three-line mapping
  (`bench(|| f())` -> `#[scaling::bench] fn`, `bench_gen_env(gen, f)` ->
  `make_input = ..`) would save every old user the same hunt.

## As built

Differences from the plan above, found while implementing:

- `benches/contended.rs` holds both the contended and the uncontended
  variants of each workload (one group each), not just the contended ones;
  `versions.rs` and `libraries.rs` are the micro-benchmarks.
- scaling 0.9.0's attributes did not see through a `ty` fragment of
  `macro_rules!` (an invisible group): `x: &I` arrived as an input taken by
  value and was rejected, so `vs!` took types as token trees. Fixed in scaling
  0.9.1, which this uses; `vs!` and `twins!` take plain `$ty:ty`.
- `internment_old` needs its default features (for `Intern`) as well as
  `bench` (for `benchmarking_only_clear_interns`); `bench` alone does not
  enable `intern`.
- `Intern32` did not compile with `--features intern32` and without
  `deepsize` (an ungated `deepsize::DeepSizeOf` bound); fixed with a `cfg`.
  `--no-default-features --features intern` and `--features intern32` still
  fail on master (separate, in CI's `check` job as written).
- Workloads that did `HashSet<String>` removal (`compare/hash`) became
  `lookup`: the two sets had nothing in common, so the removals never found
  anything; `lookup` does the same hashing and comparing read-only, so the
  setup can be built once. `sort` sorts `&T` so that the baseline `String` is
  not charged for copying strings, and now starts from a fixed shuffled order
  (the old benchmark got a random one from `HashSet` iteration).
- No code runs the `controls` against a copy of the previous release built as
  a second package; they separate the benchmark code from the library only.
- The CI `msrv` job's `cargo test` is expected to fail from a fresh resolve
  because of `criterion`'s dependencies, independent of this change.
