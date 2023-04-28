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

## Security analysis

In principle, such properties would be functional properties only, thus
a security analysis of the protocol was out of scope and, consequently,
we do not model concepts such as the environment $\mathcal{Z}$, the
adversary $\mathcal{A}$, etc. Moreover, we do not need to deal with
probabilities or computational complexity measures.

However, we retain the use of the Universal Composability (UC)
framework for the sake of design modularity. It is important to mention
that in the Praos paper the protocol is described in the so-called
*hybrid model*, in which the protocol assumes the availability of
idealized versions of some cryptographic primitives, called
*ideal functionalities*, that can be invoked by the protocol
participants, much like sub-routines. These ideal functionalities can be
replaced later with concrete implementations without affecting the
security properties of the protocol. Thus, we model these ideal
functionalities as Isabelle `locale`s.
