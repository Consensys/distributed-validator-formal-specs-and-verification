[![Formal Verification of Attestation Non-Slashability](https://github.com/ConsenSys/distributed-validator-specs-internal/actions/workflows/main.yml/badge.svg)](https://github.com/ConsenSys/distributed-validator-specs-internal/actions/workflows/main.yml)

# Specification and Verification of Ethereum Distributed Validator Specification

Distributed Validators (DV) are a technique for distributing the job of an Ethereum validator among a set of distributed nodes in order to improve resilience (safety, liveness, or both) as compared to running a validator client on a single machine. Its specifications written in Python are provided at the repository [Ethereum Distributed Validator Specification](https://github.com/ethereum/distributed-validator-specs).

A shortcoming of writing specifications in Python is the lack of formal method frameworks and tools to reason about correctness of Python specifications. In this work, we specify Ethereum Distributed Validator in the verification-aware programming language [Dafny](https://dafny.org) and verify our specifications with Dafny's support tool. Our specifications are currently for attestation creation, and we prove the safety property against slashing under asynchrony. That safety property refers to that there exist no slashable attestations if more than 2/3rd of the Co-Validators are correct under asynchrony. Our proofs and results also work under different models of computation: synchrony and partial synchrony.

## Structure

Our Dafny specifications are written at two levels of abstraction: the reference implementation level and the specification level. Those files are stored in two folders [src/dvc_implementation](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/dvc_implementation) and [src/specs](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/specs). Our Dafny proofs are stored in the folder [src/proofs](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/proofs).Finally, common materials for both specifications and proofs are stored in the folder [src/common](https://github.com/ConsenSys/distributed-validator-specs-internal/tree/internal_dvt_proofs/src/common).

### The reference implementation

- README.md: We recall important concepts and features of Dafny that are applied in our work. 
- attestation_creation.dfy: This file is close to the Python specifications for attestation creation. Moreover, we specify ghost variables that are helpful for the verification.

#### The specifications

- consensus/consensus.dfy: We specify the behaviors of consensus instances. Instead of formalizing a consensus protocol in detail, we assume that consensus instances must satisfy desired properties, e.g., validity and agreement.
- dv/dv_attestation_creation.dfy: We specify DV for attestation creation at the logical level that uses only mathematical functions and logical predicate to formalize system transitions.
- dvc/dvc_attestation_creation.dfy: We specify the behavior of DVC for attestation creation at the logical level.
- network/network.dfy: We specify the network behaviors at a high-abstract level.

### The proofs

- 

## How to run the Dafny verifier

### Prerequisites

- bash
- docker-compose

### Command

`./verify.sh`

## Future work

We are currently working on the following directions:
- Deadlocks of distributed validators for attestation creation, 
- Safety of distributed validators for block proposing under asynchrony, and
- Deadlocks of distributed validators for attestation creation.

Moreover, we are investigating on formal techniques to prove liveness of distributed validators for attestation creation and block proposing under partial synchrony.

