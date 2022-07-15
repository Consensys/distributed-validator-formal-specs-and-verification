# Dafny Reference Implementation for Distributed Attestations

This folder contains the Dafny reference implementation section of the DVT protocol that is concerned with generating attestations.

## Description

The bulk of the implementation logic is contained in the `DVCNode` class.
An instance of this class is meant to handle the attestation creation logic of the DVT protocol for a single Distributed Validator public key.

The only public method of the `DVCNode` class is the `process_event` method.
This method must be executed on an instance `I` of `DVCNode` any time that a new event concerning attestation creation for the Distributed Validator public key handled by instance `I` occurs.
The implementation is not thread-safe, that is, for any instance of `DVCNode`, only one `process_event` method must be executing at any point in time.
`process_event` returns a value of type `Status` which indicates whether any error occurred in the processing of the event.

The formal verification analysis will prove that, as long as the components external to the `DVCNode` class (i.e. network, consensus, beacon node and remote signer) behave as expected, no error can occur.
Therefore, if `process_event` indicates that an error occurred while processing the event, it means that one of the external components did not behave as expected.
Hence, recovery from error conditions is outside the scope of this reference implementation.

[comment]: <> (Not very happy with this title)
## Understanding-critical features of the Dafny language

This section covers features of the Dafny language that are critical to the understanding of the reference implementation.

- `:- <method call>`: The behaviour of this statement is similar to how exceptions work in other languages. If the method being called returns `Status.Failure`, then Dafny does not execute the rest of the caller-method code and it propagates the failure by immediately returning `Status.Failure`.
- `trait`: A `trait` is an abstract superclass analogous to Java interfaces. 
- `{<statement>}`: There is not any special meaning associated with statements being enclosed between curly braces. This is just an artifice used to allow most of the formal verification work to be carried out in separate files. Essentially, curly braces create a sort of an "anchor" in the code that a separate file can use to indicate where to insert formal verification statements.
- `requires <expression>`: These statements indicate that `<expression>` must evaluate to `true` every time that a method is called. Except for the first `requires` statement in the `constructor`, the rest of the `requires` statement are for formal verification purposes only.

## Understanding-NON-critical features of the Dafny language

This section covers features of the Dafny language that are NOT critical to the understanding of the reference implementation.

- `modifies` statements: They indicate the set of memory locations that a method may modify. These statements are needed for formal verification purposes only.
- `reads *`: This indicates that a function can access any memory location. These statements are needed for formal verification purposes only.

## TODOs

- Add documentation to the code.
- Add missing Dafny concepts.

