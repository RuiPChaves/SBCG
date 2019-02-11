# SBCG
CxG implementation

This is a proof-of-concept implementation of a (very!) small fragment of an English Sign-Based Construction Grammar, adapted to adhere to classic
CxG assumptions. The grammar is implemented in ProFIT, a Prolog extension with Features, Inheritance, and Templates originally developed 
by Gregor Erbach (Universitaet des Saarlandes) in 1994. The present version of ProFIT has been ported to modern SICStus Prolog (3.8 or higher) by Mats Carlson. None of these individuals have any knowledge of the present project or share any of the blame for any of
its shortcomings.

The grammar file "g.fit" was written by Rui P. Chaves (rchaves@buffalo.edu) at the University at Buffalo, SUNY. After loading SICStus, the interpreter must be loaded:

?- ['profit.pl'].

Then the grammar must be compiled:

?- fit 'grammar.fit'.

And finally, sentences can be parsed, for example:

?- parse([mia,sneezed], Output).

In which case the variable "Output" will be instantiated with a valid AVM describing the phonology, morphosyntax and semantics of the
clause. Because pragmatics is not implemented, a very large number of solutions are allowed, each corresponding to interpretations where 
arguments are semantically understood, but not syntactically realized. For example, "Mia laughed" can be interpreted as "Mia laughed the
kids off the stage" or "Mia laughed a hearty laugh" given that (in the present grammar) any dependents are allowed to be understood. A principled syntax-pragmatics interface theory (i.e. "Argument Realization Principle") is necessary to determine when null arguments are licensed, and when they are not. The current implementation allows null objects without restriction in order to illustrate how clusters of constructions can yield the full range of constructional variants. 
