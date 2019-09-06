STLC Shifted
==

An implementation of STLC using [Syntax with Shifted Name](http://tydeworkshop.org/2019-abstracts/paper16.pdf) for binding, which claims to eliminate the need for freshness conditions and eliminate dealing with arithmetic from de Bruijn.

So far, I've had to deal with arithmetic in two of the main identities and in
substitution lemmas, although a combination of ssreflect and omega solves it
pretty well.
The two main identities could probably be done "once and for all", so maybe they
don't count.

The substitution lemma requires lifting the open/close operations to the typing
environment.
It doesn't seem likely that this could be easily abstracted.
