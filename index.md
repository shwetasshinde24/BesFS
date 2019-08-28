## BesFS Overview

New trusted computing primitives such as Intel SGX have shown the
feasibility of running user-level applications in enclaves on a
commodity trusted processor without trusting a large OS. The OS can
compromise the integrity of an enclave by tampering with the system
call return values. In fact, it has been shown that a subclass of
these attacks called Iago attacks enables arbitrary logic execution in
enclave programs. Existing enclave systems have very large TCB and
they implement ad-hoc checks at the system call interface which are
hard to verify for completeness. To this end, we present BesFS-—the
first filesystem interface which provably protects integrity against a
completely malicious OS. We prove 167 lemmas and 2 key theorems in
4625 lines of Coq proof scripts, which directly proves safety
properties of the BesFS specification. BesFS comprises of 15 APIs with
compositional safety and is expressive enough to support  real
applications. BesFS can serve as a reference implementation
for hand-coded API checks.

-----

## Before we begin with BesFS

### Software Requirements
Tested with _The Coq Proof Assistant, version 8.8+alpha_

### Install The Coq Proof Assistant
Download the code and follow the installation instructions [here](https://github.com/coq/coq/releases/tag/V8.8%2Balpha).

### Proof General 
Alternatively, you can use [Proof General](https://proofgeneral.github.io/) IDE with Emacs to step through the proof.

-----

## Build the Coq files
```
make depend

make all
```
