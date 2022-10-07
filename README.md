[![Formal Verification of Attestation Non-Slashability](https://github.com/ConsenSys/distributed-validator-specs-internal/actions/workflows/main.yml/badge.svg)](https://github.com/ConsenSys/distributed-validator-specs-internal/actions/workflows/main.yml)

# Specification and Verification of Ethereum Distributed Validator Specification

Distributed Validators (DV) are a technique for distributing the job of an Ethereum validator among a set of distributed nodes in order to improve resilience (safety, liveness, or both) as compared to running a validator client on a single machine. Its specifications written in Python are provided at the repository [Ethereum Distributed Validator Specification](https://github.com/ethereum/distributed-validator-specs).

A shortcoming of writing specifications in Python is the lack of formal method frameworks and tools to reason about correctness of Python specifications. In this work, we specify Ethereum Distributed Validator in the verification-aware programming language [Dafny](https://dafny.org) and verify our specifications with Dafny's support tool. Our specifications are currently for attestation creation and we prove the safety property against slashing under asynchrony. That safety property refers to that there exist no slashable attestations if more than 2/3rd of the Co-Validators are correct under asynchrony. Our proofs and results also work under different models of computation: synchrony and partial synchrony.


