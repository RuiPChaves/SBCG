# SBCG
CxG implementation

This is a proof-of-concept implementation of a (very!) small fragment of an English Sign-Based Construction Grammar, adapted to adhere to classic
CxG assumptions. The grammar is implemented in ProFIT, a Prolog extension with Features, Inheritance, and Templates originally developed 
by Gregor Erbach (Universitaet des Saarlandes) in 1994. The present version of ProFIT has been ported to modern SICStus Prolog (3.8 or higher) by Mats Carlson. None of these individuals have any knowledge of the present project or share any of the blame for any of
its shortcomings.

After loading SICStus, the interpreter must be loaded:

?- ['profit.pl'].

Then the grammar must be compiled:

?- fit 'grammar.fit'.

And finally, sentences can be parsed, for example:

?- parse([mia,sneezed], Output).

In which case the variable "Output" will be instantiated with a valid AVM describing the phonology, morphosyntax and semantics of the
clause. Because pragmatics is not implemented, a very large number of solutions are allowed, each corresponding to interpretations where 
arguments are semantically understood, but not syntactically realized. The current implementation allows null objects without restriction in order to illustrate how clusters of constructions can yield the full range of constructional variants.  A principled syntax-pragmatics interface theory (i.e. "Argument Realization Principle") is necessary to determine when null arguments are licensed, and when they are not, such as the account formalized in Chaves et al. (2020).

Chaves, Rui P., Paul Kay and Laura Michaelis. "Null Instantiation in Sign-Based Construction Grammar", In Stefan Müller (ed.), 27th International Conference on Head-Driven Phrase Structure Grammar, pp.22. Stanford: CSLI Publications.
