Dirac Notation for Quantum Theory and Machine Learning
------------------------------------------------------

The intent of this project is to provide a language processor that
takes Dirac (Bra-Ket) notation expression and can manipulate, either
symbolically or via matrix representation, such expressions. There are
two main objects in this work; firstly parsing and building a syntax
tree of the expressions, which are normally thought of as vectors and
operators in a Hilbert space and secondly all the mathematical
objects, definitions and results that are entailed.

We also wish to explore at least the SU(2) group of symmetries under
the operation of multiplication of unitary matrices and the eigenspace
(spectra) of observables which e.g. may be used to represent the
evolution of qubits in the unitary quantum theory. Tensor products of
state vectors should be supported to represent composite systems up to
some practical computational limit. 

It may be fruitful to extend this to Hilbert spaces of arbitrary
dimension so that more general theories that might be relevant to
machine learning and other applications may be explored. Indeed one
thesis under exploration is that there is much to share between these
two fields of enquiry.

The implementation language is Idris where all required mathematical
objects, (vectors, matrices, groups and their algebras) will be
defined along with the grammar, language processor, AST and semantics.
Which, rather than ad-hoc definitions will leverage the expressiveness
of dependent types and mathematical logic in order to
rigorously define and state proofs of all relevant results. 

This at the same time provides some guarantees of correctness but
perhaps more importantly places the entire endeavor under a rigorous
framework which allows it to be appreciated and inspected providing a
good pedagogical opportunity for both the subject matter and the
techniques of type based mathematical logic.

Visualizations of the mathematical objects should also be explored to
facilitate understanding and exploration.

_____________________________________________________________________
Simon Beaumont (datalligator@icloud.com) October 2018.


