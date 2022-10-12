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
    - A Distributed Validator (DV) will never commit a slashable offence, and
    - Under partial synchrony, a DV will eventually produce valid blocks/attestations.
- An executable reference implementation.
- A formal proof that the the executable reference implementation adheres to the specification.

## Assumptions
​
The formal proof of the DVT protocol relies on the following assumptions:
​
- The BFT consensus protocol: DVCs make a decision on an attestation/block by running an instance of the BFT consensus protocol. We assume that the implementation and running of consensus instances are correct. That is, a consensus instance must satisfy the agreement, termination, and validity properties.
- M-of-N threshold signatures: We assume that M is greater than 2/3 of N and that the threshold signatures are implemented correctly, that is, the implementation satisfies signature unforgeability and uniqueness.
- DVC: Each Co-Validator runs only one the Distributed Validator Client software.
- Remote Signer (RS): Every DVC has its own RS.
- Beacon Node (BN): Every DVC has its own BN.
- Network latency: The network between DVC, RS, and BN are synchronous. However, the network between DVCs has no bound on message delay, and messages might be lost.

- Trusted Byzantine DVCs: We are currently assuming that Byzantine DVCs are reliable. This assumption makes our model less complicated and allows us to focus on writing proofs that require the anticipant of quorums, instead of all DVCs. We are adapting our model and proofs to cope with Byzantine behavior. This assumption should be changed soon.

## Our approach

In this work, we first specify the DVT protocol in the verification-aware programming language [Dafny](https://dafny.org). Our Dafny specifications are written at two levels of abstraction: the specification level and the reference implementation level. The specification files are written in the high level of abstraction and they formalize the logical semantics of the DVT protocol. In contrast, the reference implementation files are close to Python files in [here](https://github.com/ethereum/distributed-validator-specs/tree/dev/src/dvspec), and those files are executable.

Then, we write formal proofs to verify the correctness of our specifications and mechanically check those proofs with Dafny. We follow the standard way to prove a safety property that is based on an inductive invariant. Intuitively, an inductive invariant is a conjunction of invariants in the system that are preserved by every system transition. If the inductive invariant implies the safety, then the safety is guaranteed in every reachable system state. Formally, our proof strategy for the safety has three steps:
1. We find an inductive invariant and prove that it implies the safety.
2. We prove that the initialization implies the inductive invariant.
3. We prove that every system transition preserves the inductive invariant.


## Status

Our specifications are currently for attestation creation, and we prove the safety property against slashing under asynchrony. That safety property refers to that there exist no slashable attestations if more than 2/3rd of the Co-Validators are correct under asynchrony. Our proofs and results also work under different models of computation: synchrony and partial synchrony.

Moreover, we are working on the directions mentioned in [Future work](#future-work).

## Structure

 Those files are stored in two folders [src/dvc_implementation](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/dvc_implementation) and [src/specs](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/specs). Our Dafny proofs are stored in the folder [src/proofs](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/proofs).
 Finally, common materials for both specifications and proofs are stored in the folder [src/common](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/common).

### The reference implementation

The reference implementation is stored in the folder dvc_implementation.

- README.md: We recall important concepts and features of Dafny that are applied in our work. 
- attestation_creation.dfy: This file is close to the Python specifications for attestation creation. Moreover, we specify ghost variables that are helpful for the verification.

### The specifications

The specifications are written in files in the folder specs.
- consensus/consensus.dfy: We specify the behaviors of consensus instances. Instead of formalizing a consensus protocol in detail, we assume that consensus instances must satisfy desired properties, e.g., validity and agreement.
- dv/dv_attestation_creation.dfy: We specify DV for attestation creation at the logical level that uses only mathematical functions and logical predicate to formalize system transitions.
- dvc/dvc_attestation_creation.dfy: We specify the behavior of DVC for attestation creation at the logical level.
- network/network.dfy: We specify the network behaviors at a high-abstract level.


### The proofs
Our proofs are saved in the folder proofs.
- main_theorem.dfy: presents the proof of the safety of the DVT protocol for attestation creation.
- common: currently contains proofs of lemmas for set operators.
- implementation_refinement/attestation_creation: shows the proofs that the reference implemention adheres to the specifications.
- no_slashable_attestations: contains proofs of the safety of the DVT protocol for attestation creation.
    - common:
        - attestation_creation_instrumented: adds instruments for our proofs.
        - common_proofs: stores fundamental lemmas that are used in other proofs.
        - dvc_spec_axioms: formalizes all of our assumptions about the DVC behaviors.
    - supporting_lemmas: contains supporting lemmas that follow the standard approach to prove the safety.
        - inv.dfy: lists all interesting invariants used in main_theorem.
        - ind_inv.dfy: contains the inductive invariant used in main_theorem.
        - init_implies_ind_inv: shows that the DV initialization implies the inductive invariant.
        - dv_next_implies_ind_inv: proves that every DV transition preserves the inductive invariant.
        - ind_inv_implies_safety: proves that the inductive invariant implies the safety, i.e., no slashble attestations are created.

## How to run the Dafny verifier

### Prerequisites
The simpliest way to check our specification is to install the following software and then to run the provided Docker container.
- bash
- docker-compose

### Command
The user can check our specifications by running the following command `./verify.sh`.

## Future work

We are currently working on the following directions:
- Formalize the network faults and Byzantine DVCs, and extend our proofs with such untrusted components,
- Deadlocks of distributed validators for attestation creation, 
- Safety of distributed validators for block proposing under asynchrony, and
- Deadlocks of distributed validators for attestation creation.

Moreover, we are investigating on formal techniques to prove liveness of distributed validators for attestation creation and block proposing under partial synchrony.

## Funding
​
This project is being carried out by ConsenSys R&D and is supported by a joint grant from the Ethereum Foundation, Obol and SSV Networks.