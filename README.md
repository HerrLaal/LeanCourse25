# Lean Project for the Lean Course (WiSe 25/26, Bonn)

## In this repository

You will find the project in `LeanCourse25/Projects`.

- Everything in the `Prereq` folder has been imported from
  [Bhavik Mehta's ExponentialRamsey project](https://github.com/b-mehta/ExponentialRamsey/tree/master/ExponentialRamsey/Prereq), where they define the Ramsey numbers and some easy properties about those, which we only modified slightly to match our lean version.
- Our contributions are mainly in `Schur.lean`, where we state and prove [Schur's theorem](https://en.wikipedia.org/wiki/Schur's_theorem), following the proof published in wikibooks[^1]. Additionally, we formalize a generalized version of Schur's theorem by Jon Henry Sanders[^2].

## Project Details

As stated above, we worked on Schur's theorem and some generalizations.
The proof of Schur's theorem (`schur` in `Schur.lean`) is complete and uses the existence of Ramsey numbers from `Prereq` to deduce the statement. In the context of the paper by Jon Henry Sanders[^2], `schur` is Theorem 1.

Afterwards, we state Theorem 2 from Sanders[^2], which is `generalized_schur`, for which we only give
a partial proof, as the actual proof given in the paper is quite lengthy. However, we reduce the case
`n = 2` to Schur's theorem and therefore prove the base case.

Finally, we also state Corollary 1.1 from Sanders[^2] as `generalized_schur'`, which shows that from
`generalized_schur` we can deduce a version, for which the picked elements are pairwise distinct.
The proof of this corollary is complete except for depending on `generalized_schur`.

Apart from the built-in assists (`apply?`, ...), [leansearch.net](https://leansearch.net) and [loogle](https://loogle.lean-lang.org), we formalized everything ourselves, without the help of AI.

[^1]: Wikibooks contributors. Combinatorics/Schur's Theorem. 2017 Jun. [Used version: 2026 Feb 6](https://en.wikibooks.org/w/index.php?title=Combinatorics/Schur%27s_Theorem&oldid=3237602).

[^2]: Jon Henry Sanders. A Generalization of Schur's Theorem (preprint). 2017 Dec, [arXiv:1712.03620](https://arxiv.org/abs/1712.03620v1),
