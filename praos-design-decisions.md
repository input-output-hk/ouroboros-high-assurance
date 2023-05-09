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

## Cryptographic primitives

### Public-key cryptography

The Ouroboros Praos protocol is based on a public-key cryptographic
system. We state a correctness property that establishes a relationship
between the generated verification and secret keys: if we generate the
keys using the key generation function then it is possible to retrieve
the verification key from the secret key. Although not explicitly
stated, the paper assumes this property holds. Another property that is
normally assumed is that it is infeasible (i.e., having a negligible
probability) to derive the secret key from the public key. However,
since this is a probabilistic security property, we leave it out.

Further, in cryptography, key generation is usually modeled as an
efficient probabilistic algorithm. However, we adopt a more realistic
approach and model the key generator as an ordinary, deterministic
algorithm.

### Digital signatures

The paper describes two digital signature schemes: A regular digital
signature scheme, denoted by $\mathcal{F}\_{\mathsf{DSIG}}$, which is
used to sign transactions, and a special digital signature scheme,
denoted by $\mathcal{F}\_{\mathsf{KES}}$, which is used to sign blocks
and has the capability of allowing the signing key to evolve, in such a
way that the adversary cannot forge past signatures. For our purposes,
though, we model a single, ordinary digital signature scheme for signing
both transactions and blocks.

In traditional cryptography, signing and verification procedures are
efficient algorithms. Moreover, the former is usually probabilistic (as
is the case in the paper). However, again, we model both procedures as
ordinary, deterministic algorithms. Regarding properties, and as stated
in the paper, we only require a correctness property stating that the
signature produced by signing a message can be checked to be valid,
provided that the verification key used to check the validity of the
signature is derived from the secret key used to sign the message. This
correctness property, though, changes a bit for the case of
$\mathcal{F}\_{\mathsf{KES}}$, a fact that we naturally ignore.

Finally, the paper states that the scheme $\mathcal{F}\_{\mathsf{DSIG}}$
is EUF-CMA-secure, and that the scheme $\mathcal{F}\_{\mathsf{KES}}$ is
secure with respect to a special definition of forward security. As
usual, we do not enforce this security properties but simply assume
them.

### Verifiable random functions (VRF)

In the Praos protocol, the stakeholders use a VRF for executing the
private lottery to check whether they're slot leaders for a particular
slot. Also, stakeholders use a VRF to include a pseudorandom value in
each block they produce. The paper uses a special VRF which is more
secure than standard VRFs, since it guarantees that VRF values cannot be
predicted even if the adversary is allowed to generate the secret and
verification keys. Naturally, for this work, we stick to the regular
definition of a VRF.

In traditional cryptography, evaluation of VRFs (and pseudorandom
functions in general) is an efficient algorithm; however we only assume
that. Regarding properties, and as stated in the paper, VRFs satisfy the
properties of uniqueness, provability, and pseudorandomness (i.e., it is
difficult for an efficient adversary to distinguish a VRF value from a
truly random value). Since this last property is probabilistic in nature,
we only require the first two properties.

Finally, in the paper, pseudorandom values produced by VRFs are
bit-strings, which can be regarded as values of any type and thus we
model them by using a type parameter. However, the paper loosely uses
such values in the comparison to a *real-valued* threshold to check for
slot leadership. Therefore, we require the existence of a function
`value_to_real` in the interface of VRFs that casts VRF values to real
numbers.

### Hash functions

The paper uses the *Random Oracle Model* (ROM). In the ROM, a hash
function is modeled as a random oracle, which is basically a magical
black box that implements a truly random function. As the ROM is used
just for the purposes of the security proof, we model a collision-free
cryptographic hash functions instead. Theoretically, cryptographic hash
functions have certain properties, e.g., they are one-way functions,
meaning that they are difficult to invert by an efficient adversary.
But, this property is probabilistic in nature, so we cannot enforce it
in the code.

## Protocol parameters

### Parameter $k$

As the paper states, the parameter $k$ establishes how deep in the chain
(in terms of number of blocks) a transaction needs to be in order to be
declared as stable. Although the paper does not explicitly say whether
$k$ must be positive (it does say that $k \in \mathbb{N}$), Theorem 7
(Chain quality) defines $\mu = 1/k$, therefore $k$ must be positive.

### Parameter $f$

The parameter $f$, called *active slot coefficient*, establishes the
probability that at least one stakeholder is elected as a slot leader in
each slot, that is, the probability that a slot is not empty. Although
the paper does not explicitly say so, we assume $f$ to be a strictly
positive probability; otherwise all slots would be empty. Moreover, for
example, Theorem 4 in the paper assumes $f \in (0, 1]$.

### Parameter $\epsilon$

The parameter $\epsilon$ represents the advantage in terms of stake of
the honest stakeholders against the adversarial ones. Although the paper
does not explicitly say so, we assume $\epsilon \in (0,1)$, as is the
case for example in Theorem 5 (Common prefix) in the paper. Finally,
although the parameter $\epsilon$ is used almost exclusively in the
security analysis of the protocol, we need to include it nevertheless,
since it is also used in the computation of the new epoch randomness
performed by the sub-protocol $\pi_{RLB}$.

## The static and dynamic stake cases

The paper describes and analyzes the protocol in two settings: The
_static stake_ case and the _dynamic stake_ case. In the former, the
initial stake distribution is hardcoded into the genesis block and
remains fixed during the whole execution (i.e., one epoch); in the
latter, the stake distribution is allowed to change over time and the
protocol execution spans multiple epochs. Since we are not interested in
the security analysis, we model the full protocol.

## Slots and epochs

For numbering slots and epochs, the paper uses the mathematician's
convention of starting from 1, and so we do in our formalization.
However, it is probably better to use the computer science's convention
of zero-based indexing in order to facilitate computations involving
indexes.

## Initialization phase and the functionality $\mathcal{F}\_\mathsf{INIT}$

The paper includes an ideal functionality $\mathcal{F}\_\mathsf{INIT}$,
which is passed the initial stakes of all stakeholders as parameters
and does the following:

 1. Receives the verification keys from each stakeholder during the
 first round of the protocol and stores them locally.
 2. When all stakeholders have sent their verification keys, it
 constructs a genesis block including these keys, the initial stakes,
 and an initial random value $\eta$.
 3. When asked by a stakeholder in later rounds, it sends the genesis
 block to the stakeholder.

On the other hand, the stakeholder's initialization phase comprises the
following steps:

 1. In the first round, the stakeholder sends requests to
 $\mathcal{F}\_\mathsf{VRF}$, $\mathcal{F}\_\mathsf{KES}$, and
 $\mathcal{F}\_\mathsf{DSIG}$ to generate their verification keys, and
 then sends them to $\mathcal{F}\_\mathsf{INIT}$.
 2. In the next round, the stakeholder obtains the genesis block from
 $\mathcal{F}\_\mathsf{INIT}$.

In our formalization, we have simplified this initialization protocol
in several ways:

1. We do not model $\mathcal{F}\_\mathsf{INIT}$.
2. Each stakeholder is parametrized with its secret keys. **NOTE**:
This may be an over-simplification, since the `generate` function of the
VRF and digital signature modules should be used instead.
3. The verification keys of each stakeholder reside only in the genesis
block, which is given to each stakeholder as a parameter. **NOTE**: This
may be an over-simplification, since the `generate` function of the VRF
and digital signature modules should be used instead. But then again,
some protocol similar to the one used with $\mathcal{F}\_\mathsf{INIT}$
in the paper should be used in order for stakeholders to be able to
publish their verification keys.
## Transactions and blocks

In the paper, the environment $\mathcal{Z}$ issues transactions on
behalf of any stakeholder $U_i$ by requesting a signature on the
transaction and handing the transaction data $d^\* \in \\{0,1\\}^\*$ to
stakeholders to put them into blocks. We decide not to model transaction
processing this way but use a more realistic approach instead:
Transactions are assumed to be received by stakeholders through the
network.

Regarding the application of a transaction to a stake distribution, the
paper does not define how this is done, so we use the intuitive
definition and assume that the source and target stakeholders exist in
the stake distribution and that the source stakeholder has enough stake
for the withdrawal.

Regarding the application of a block to a stake distribution, the paper
does not define how this is done, so we assume that it simply means
applying all transactions in the block to the stake distribution.

## Functionality $\mathcal{F}^{\tau,r}\_{RLB}$ and subprotocol $\pi\_{RLB}$

In the paper, the functionality $\mathcal{F}^{\tau,r}\_{RLB}$ models a
randomness beacon that basically provides a fresh nonce for each epoch
to (re)seed the election process. Furthermore, this beacon is resettable
and leaky in order to strengthen the adversary, as the purpose of the
beacon is to enable the security analysis of the full protocol. The
paper also presents a subprotocol $\pi\_{RLB}$ that simulates the beacon
in the $\mathcal{F}\_\mathsf{INIT}$-hybrid model via a simple algorithm
that collects randomness from the blockchain. Therefore, we choose to
directly model $\pi\_{RLB}$, which is ultimately used by implementations.

## Chain selection rule

According to the paper, the function $\mathsf{maxvalid}$ should favor the
current chain if it is the longest, otherwise choose arbitrarily. In the
latter case, we make a specific decision, namely, we choose a chain that
was delivered first out of those with maximal length (which is one of
the possible choices suggested by the paper). However, if the need
arises, it is possible to leave this choice unspecified.
