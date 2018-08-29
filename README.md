Restricted permutations

(require ".../R.rkt")

A restricted permutation p is a bijection of the set
of all natural numbers onto the same set such that:

exists m: forall k: k>=m implies p(k)=k

R.rkt provides functions for restricted permutations
and finite groups of restricted permutations.

Restricted permutations are represented by procedures,
but in such a way that two procedures representing the same
mathematical permutation are the same in the sense of [eq?].
Groups are represented in a way that two representations of
the same mathematical group are the same in the sense of [eq?].

Download all files from https://github.com/joskoot/restricted-permutations.
Run module R.scrbl and make sure it produces a html file,
for example by opening it with DrRacket an clicking the scribble button.
Keep all files in the same directory.
More info in R.html as produced by R.scrbl.
R.scrbl may require some time and memory because of elaborated examples.

Have fun,
Jacob J. A. Koot
