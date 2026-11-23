# Manuscript recovery for the next two-core obligation

## Result and provenance

The exact statements of Lemma 4.4 and Corollaries 4.5 and 4.6 have been recovered and matched to every corresponding pinned statement hash in `docs/coverage.json`. This is source recovery, not an additional Lean proof. This run report adds the relevant statement/proof excerpts below; the complete manuscript remains unbundled. Historical manifest wording saying that no manuscript text was reproduced describes the earlier checkpoint, before this recovery report.

The inspected source is `Four_Robust_Component_Cases_2026-11-21.tex`, version 19, reported size 273,361 bytes and modification time 2026-11-21T17:28:35.197866Z. It was found by a search for the repository's named manuscript and read at the exact line ranges below. It is a newer whole-file revision than the pinned November 20 manuscript. **The complete newer file's hash was not recomputed in this run.** The three statement-block hashes were independently computed from the retrieved UTF-8 text and exactly match the November 20 inventory; no inventory or assertion wording was changed.

The repository's historical whole-file identities remain those in `docs/manuscript-source.json` and `docs/few-exception-source.json`. This report establishes identity of these three statement blocks, not identity of the entire manuscripts or all their proof text.

## Actual hash check

Hashing convention: UTF-8, original internal newlines, from `\begin{lemma}` or `\begin{corollary}` through the corresponding end command, with no terminal line feed.

| Assertion | Bytes | Computed SHA256 | Comparison with pinned inventory |
| --- | ---: | --- | --- |
| 4.4 | 688 | `653e8b0aa8fa12f4368816ce9d9ce8b9d84a49015bce07638fd9c49e94523c2b` | exact match |
| 4.5 | 275 | `89d8e8281fc3e4b7d8b6a81bccac3eb1d49f92622106228a5bee504d3eff1d61` | exact match |
| 4.6 | 443 | `86700ed56e6cd9be513339e7c06b5af19d1d8cbe074fed3985ef21e5c9ad6e26` | exact match |

## Exact statement 4.4

Inspected source lines 2534–2546.

```tex
\begin{lemma}\label{two:short:fixed-pattern}
Fix $\alpha,c>0$, an integer $t$, and ordinary robust parameters
with sufficiently small range. For sufficiently small $\eps>0$
and large even $n$, let $G$ be a $k$-regular multigraph
of order $n$ with no $k$-overfull set, where $k\ge\alpha n$, with partition
$U_1\cup\cdots\cup U_q\cup Z_0$, $q\in\{1,2\}$,
$|Z_0|\le t$, and $|U_i|\ge\alpha n$. Suppose each core contains
a simple robust spanning graph of minimum degree at least $k-a$,
where $a+1\le\eps n$.
In a scaled perfect-matching decomposition, suppose a boundary
pattern of weight at least $ck$ has at most $4-q$ internal pairs
in $Z_0$. Then $G$ has a one-factorization.
\end{lemma}
```

## Exact statement 4.5

Inspected source lines 2735–2739.

```tex
\begin{corollary}\label{two:thm:two-four-exceptions}
An even-order $k$-regular multigraph with no $k$-overfull set, two
robust cores, and at most five other vertices has a one-factorization,
for sufficiently small core error and fixed positive density bounds.
\end{corollary}
```

## Exact statement 4.6

Inspected source lines 2748–2756.

```tex
\begin{corollary}\label{three:lem:bounded-input}
Fix positive density bounds and ordinary robust parameters with
sufficiently small range. For sufficiently small core error, an
even-order $k$-regular multigraph with no $k$-overfull set has a
one-factorization if
it has either one core and at most three other vertices,
or two cores and at most two other vertices. The degree
and core orders have the fixed linear lower bounds.
\end{corollary}
```

## Adjacent source proof reductions

These adjacent proof passages were read from the newer source. Their whole proof-text identity with the November 20 file was not checked. They give the intended route; they are mathematical arguments rather than completed Lean proofs.

### Corollary 4.5

```tex
\begin{proof}
Every boundary pattern has at most two internal pairs. The pattern
weights sum to $k$, so some pattern has weight at least $k/b_2(5)$.
Apply Lemma~\ref{two:short:fixed-pattern} with $c=1/b_2(5)$.
\end{proof}
```

### Corollary 4.6

```tex
\begin{proof}
For one core, a pattern on at most three exceptional vertices has at most one
internal pair, so Lemma~\ref{two:short:fixed-pattern} applies to a
maximum-weight pattern. For two cores, apply
Corollary~\ref{two:thm:two-four-exceptions}.
\end{proof}
```

## The assigned-part quotient in the source proof

The following relevant passage was read from lines 2636–2663 of the newer source. This proof passage was not compared with the November 20 proof-text bytes; only the three numbered statements above were hash-matched.

```tex
\textbf{Step 3: Compatible circuits on the assigned parts.}
Assign every unpaired vertex of $Z_0$ to its core in $\Pi_0$, making
parts $A_i$; keep each internal pair of $\Pi_0$ as a separate part.
There are at most four parts. By
\eqref{two:short:eq:reserve-size}, each vertex of $Z_0$ has at most
$a_1$ incidences outside its assigned part or pair. Every old core
vertex has outside degree at most $a$.

With one core all parts are even. With two cores both $A_i$ have
the parity of $p(\Pi_0)$. Contract the parts. If the two core parts
are odd, add $h$ virtual parallel edges between them, putting all
virtual incidences in one new class at each endpoint. All other
classes record original endpoints. The resulting quotient is
Eulerian. For an even union of original parts, toggling a vertex
of the original graph gives \eqref{two:eq:compatible-cut-condition}.
For an odd union
separating the two odd parts, the original cut has at least $h$
edges; its augmented cut has at least $2h$. Every incidence class
contributes at most $h$ incidences. These observations
verify every class inequality.

Decompose into compatible circuits. In the odd case a circuit
uses at most one virtual edge. Removing the virtual edges gives
exactly $h$ paths between $A_1,A_2$ in the quotient, and surplus
circuits. Each lifts to a matching in the original graph with at
most four edges. The matching corresponding to a path meets each
core part once and each pair part zero or twice; that corresponding
to a surplus circuit meets every part evenly.
```

**Concrete specialization to the two-core branch of 4.6 (mathematical argument, not a new Lean proof):** with `q = 2` and at most two exceptional vertices, a boundary matching has at most one internal exceptional pair. The source construction therefore creates the two assigned core parts and at most one pair part: at most three quotient labels. Unpaired exceptional vertices are assigned into core parts, not left as exceptional singleton labels. Adding the virtual parallel copies changes no vertex label. The new at-most-three compatible-circuit theorem is thus sufficient for this source circuit stage once the preceding reserve construction, parity, and all original endpoint-class cut bounds are established in Lean. This offers a focused route to 4.6 without requiring the full five-exception branch of 4.5 first. It does not complete the reserve selection, lifting, palette alignment, or factorization obligations.

## Consequences for continuation

- The label `two:thm:two-four-exceptions` does not specify the cardinality bound. The hash-matched original statement says **at most five other vertices**. Preserve five when formalizing full 4.5.
- The distinct two-core branch of 4.6 allows at most two other vertices. Its recorded proof invokes 4.5, which invokes the two-core case of fixed-pattern Lemma 4.4.
- For two cores, 4.4 permits at most two internal exceptional pairs (`4-q` with `q=2`), and assumes a boundary pattern of weight at least `c*k` in a scaled perfect-matching decomposition. Its parameter order and original-host robust spanning subgraphs must be retained.
- The new compatible-circuit theorem is a supporting construction. Its application still requires deriving even quotient degrees and every half-cut inequality from the source setup, then lifting and reassembling actual edge copies.
- Read `next-target-assessment.md` in this run directory for the checked Lean interfaces and the exceptional-singleton quotient obstruction. Source availability no longer blocks reading these three original statements; their remaining constructions and proofs remain unfinished.

## Reproduce the statement identity check

Run from the repository root. This extracts the three exact statement code blocks from this report and compares them with the committed inventory without modifying any file:

```sh
python3 - <<'PY'
import hashlib, json, re
from pathlib import Path
p = Path('verification/runs/20261122T235931Z/manuscript-recovery.md')
text = p.read_text()
expected = {a['number']: a['statement_sha256']
            for a in json.loads(Path('docs/coverage.json').read_text())['numbered_assertions']}
for number, block in re.findall(r'## Exact statement (4\.[456])\n.*?```tex\n(.*?)\n```', text, re.S):
    actual = hashlib.sha256(block.encode()).hexdigest()
    assert actual == expected[number], (number, actual)
    print(number, len(block.encode()), actual, 'MATCH')
PY
```
