# Design decisions of the Praos specification

The purpose of this document is to record the design decisions that
were made during the development of the current version of the
[**Ouroboros Praos**](https://eprint.iacr.org/2017/573.pdf) protocol
specification formalized in Isabelle/HOL. In particular, it is reported
what aspects were modeled (and how) and what aspects were left out.

## Original goal

The original goal for implementing a version of Ouroboros Praos in
Isabelle/HOL was to have a formalized version of the protocol that
would serve as a reference specification based directly on the
Ouroboros Praos paper and that would allow us to formally prove
properties of it.
