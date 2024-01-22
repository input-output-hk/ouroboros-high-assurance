Overview
========

The `ouroboros-high-assurance` library contains formalizations related
to the Ouroboros family of blockchain consensus protocols. Concretely,
it comprises the following:

  * A proof of the chain selection property
  * Draft specifications of the following consensus protocols, using the
    [Þ-calculus][thorn-calculus]:
      - [Ouroboros BFT][ouroboros-bft]
      - [Ouroboros Praos][ouroboros-praos]
  * A specification of the Chain-Sync mini-protocol, using the
    Þ-calculus
  * A framework for specifying [mini-protocols][networking-protocol]
  * Specifications of the following mini-protocols, using the
    above-mentioned framework:
      - Chain-Sync
      - Ping-Pong
      - Request-Response

[thorn-calculus]:
    https://github.com/input-output-hk/thorn-calculus
    "A general-purpose process calculus with support for arbitrary data"
[ouroboros-bft]:
    https://iohk.io/en/research/library/papers/ouroboros-bft-a-simple-byzantine-fault-tolerant-consensus-protocol/
    "Ouroboros-BFT: A Simple Byzantine Fault Tolerant Consensus Protocol"
[ouroboros-praos]:
    https://iohk.io/en/research/library/papers/ouroboros-praos-an-adaptively-secure-semi-synchronous-proof-of-stake-protocol/
    "Ouroboros Praos: An Adaptively-Secure, Semi-Synchronous Proof-of-Stake Protocol"
[networking-protocol]:
    https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec
    "The Shelley Networking Protocol"


Requirements
============

You need Isabelle2022 to use this Isabelle library. You can obtain
Isabelle2022 from the [Isabelle website][isabelle].

[isabelle]:
    https://isabelle.in.tum.de/
    "Isabelle"

In addition, you need the following Isabelle sessions:

  * [`Finite-Map-Extras`](https://www.isa-afp.org/entries/Finite-Map-Extras.html)
  * [`Thorn_Calculus`](https://github.com/input-output-hk/thorn-calculus)


Setup
=====

To make this Isabelle library available to your Isabelle installation,
add the path of the `src` directory to the file
`$ISABELLE_HOME_USER/ROOTS`. You can find out the value of
`$ISABELLE_HOME_USER` by running the following command:

    isabelle getenv ISABELLE_HOME_USER


Building
========

Running `make` builds the PDF file that includes the documentation and
the code and places it in `$ISABELLE_BROWSER_INFO/IOG`. You can find out
the value of `$ISABELLE_BROWSER_INFO` by running the following command:

    isabelle getenv ISABELLE_BROWSER_INFO

The makefile specifies two targets: `properly`, which is the default,
and `qnd`. With `properly`, fake proofs (`sorry`) are not accepted; with
`qnd`, quick-and-dirty mode is used and thus fake proofs are accepted.
