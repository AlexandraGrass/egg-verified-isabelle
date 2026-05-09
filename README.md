# Cracking egg: Towards Verified Equality Saturation

**Abstract.** We present initial work on formally verifying the core of the egg framework in Isabelle/HOL. The egg framework uses e-graphs to perform fast, extensible equality saturation. Congruence closure is a core technique in program analysis and program optimization, serving as a foundation for rewriting systems and enabling efficient reasoning in equational logic. Optimization techniques such as egg's deferred rebuilding mechanism, however, obscure the computation and thus reduce confidence in the results. In this work, we aim to provide a comprehensive, extensible formalization of egg's data structures and algorithms, with a focus on the correctness of deferred rebuilding. Ultimately, we seek to export a verified implementation to Standard ML, enabling trustworthy, executable equality saturation.

With this artifact, we provide the proof files accompanying our paper *Cracking egg: Towards Verified Equality Saturation*. The proofs have been machine-checked with Isabelle2025-2.

## Structure and Content

This artifact includes the following adapted and newly added files:

- `UnionFind/Union_Find.thy`. The union-find data structure by Stevens and Ghidini, now augmented with an `extend` operation introducing new ids in an existing union-find instance.
- `Egg/*.thy`. The Isabelle/HOL theory of egg, including
    - `Base.thy`. In this file, we introduce the datatypes for e-nodes and terms. The raw type of an egg-style e-graph is defined as a 4-tuple. We then characterize the well-formedness of the raw e-graph datatype by introducing an invariant.
    - `RawEgg.thy` (corresponds to subsection *3.1 Raw Implementation of egg* of our paper). Our formalization currently covers e-graph initialization and the `canonicalize`, `find`, and `add` operations. To properly define the operations, we introduce predicates regarding the well-formedness of parameters.
    - `AbstractEgg.thy` (corresponds to subsection *3.2 egg as Abstract Datatype* of our paper). In this theory, previously defined operations and lemmas are lifted to the abstract datatype `'a egg`.
- `Egg/minimal-egg/`. A minimal toy implementation of egg in python, intended as a playground for refining the algorithms now implemented in the Isabelle/HOL theory files.

The proofs can be checked on the command line as well as viewed and checked in Isabelle's prover IDE `jedit`.

## Running the Formalization

### Prerequisites
The formalization uses Isabelle2025-2, which can be obtained from the [Isabelle website](https://isabelle.in.tum.de/).
Furthermore it relies on entries of the [*Archive of Formal Proofs* (AFP)](https://www.isa-afp.org), which can be obtained as described on the [download page](https://www.isa-afp.org/download/).

### Checking the Proofs with Isabelle's Command Line Tool

Let `$AFP` be the path you downloaded the AFP to. Run `isabelle build -d $AFP/thys -D . -v` from the artifact's root directory to build the formalization, which non-interactively checks all the proofs (this should take approximately 1 minute).

### Checking the Proofs with Isabelle's Prover IDE `jedit`

Let `$AFP` be the path you downloaded the AFP to. A theory file can be opened and checked in `jedit` by running `isabelle jedit -d .$AFP/thys -d . Egg/RawEgg.thy` from the artifacts root directory.

The bar next to the scrollbar on the right of the file editor view indicates whether a file was successfully processed. A light red color indicates that these parts were not yet checked. To check the entire file, either scroll to the bottom of the file (you will recognize the light red bar following the movement) or open the side tab *Theories* and check the opened theory. Both methods will trigger the automatic check of the file.

After the file was checked successfully, the bar next to the scrollbar should be plain gray indicating that no error was found.
If you find dark red lines in that bar next, then the checking was not successful. The *Theories* view on the right side shows an overview of checked theories with a similar color highlighting.

The *Sidekick* tab on the right gives an overview of the structure of a theory file. You can use it to jump to the section or lemma you are interested in.
