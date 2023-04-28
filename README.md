[![Formal Verification of Attestation Non-Slashability](https://github.com/ConsenSys/distributed-validator-specs-internal/actions/workflows/main.yml/badge.svg)](https://github.com/ConsenSys/distributed-validator-specs-internal/actions/workflows/main.yml)

# Formal Verification of the Distributed Validator Technology Protocol
​​
The Distributed Validator Technology (DVT) protocol is an implementation of an Ethereum Validator where a set of nodes, called Distributed Validator Clients (DVC), rather than a single node, co-operate to perform the Validator duties. This is to increase the resiliency of an Ethereum Validator by removing any single point of failure. The high-level description of the protocol and the related glossary can be found [here](https://github.com/ethereum/distributed-validator-specs).
​
This project focuses on the formal verification of the DVT protocol.

## Objectives
​
More specifically, the objectives of this project are to provide:
​
- A formal specification of the DVT protocol.
- A formal proof that as long as the number of Byzantine DVCs is less than 1/3, the above specification guarantees the following properties:
    - A Distributed Validator (DV) will never commit a slashable offense, and
    - Under partial synchrony, a DV will eventually produce valid blocks/attestations.
- An executable reference implementation.
- A formal proof that the executable reference implementation adheres to the specification.

## Status

### Specification

Currently, the specifications are for attestation creation and block signing.

### Reference Implementation

Currently, the reference implementations for attestation creation and block signing.

### Proofs

1. Under the following assumptions, slashable attestations and slashable blocks signed by the Distributed Validator singing key can never be created.
    - Signature unforgeability and uniqueness.
    - Sound `ceil(2N/3)`-of-`N` threshold signature scheme.
    - Correct BFT protocol: DVCs make decisions on attestations by running instances of a BFT consensus protocol. We assume that the implementation and execution of the BFT consensus instances are correct. That is, any of the BFT consensus instances executed ensure agreement, termination, and validity.
    - Single DVC: Each Co-Validator runs only one Distributed Validator Client software.
    - Single Remote Signer (RS): Every DVC has its own RS.
    - Single Beacon Node (BN): Every DVC has its own BN.
    - Less than 1/3 of the pairs (DVC, RS) are Byzantine.
    - Synchronous network between DVC, RS and BN.
    - Asynchronous networks (with lost messages) between the DVCs.

2. The reference implementation is correct with respect to the specification.

## How to run the Dafny verifier

The simplest way to check our specification is to install the following software and then run the commands indicated.
### Required Software

- git
- bash
- docker-compose

### Command
The user can check our specifications by executing the following steps.
1. Clone this repository via `git clone git@github.com:ConsenSys/distributed-validator-formal-specs-and-verification.git`
2. Execute `cd distributed-validator-formal-specs-and-verification`
1. Execute `./verify.sh`.

## Future work

Future work includes:

- Extending the formal specification and reference implementation to sync committees.
- Extending the proof of no slashability to sync committees.
- Proving that under partial synchrony Distributed Validators always eventually produce valid attestations and blocks.

## Our approach

In this work, we first provide both a specification and a reference implementation of the DVT protocol in the verification-aware programming language [Dafny](https://dafny.org). 
The specification formalizes the logical semantics of the DVT protocol.
In contrast, the reference implementation is executable and is written in way to resemble as close as possible the way that Python programs are written.

Then, we write formal proofs to verify the correctness of our specifications and mechanically check those proofs with the Dafny verifier. We follow the standard way for proving safety properties based on defining an inductive invariant. Intuitively, an inductive invariant is a conjunction of invariants in the system that are preserved by every system transition. If the inductive invariant implies a safety property, then the safety property is guaranteed in every reachable system state. Formally, our proof strategy for safety properties follows three steps:
1. We find an inductive invariant and prove that it implies the safety property.
2. We prove that the initialization implies the inductive invariant.
3. We prove that every system transition preserves the inductive invariant.

## Funding
​
This project is being carried out by ConsenSys R&D and is supported by a joint grant from the Ethereum Foundation, Obol and SSV Networks.