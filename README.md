Restricted permutations

How to install?\
The scribble documentation uses format/fmt. Therefore install format before installing restricted-permutations.

Go to file/package manager.\
Choose Do what I mean,\
Enter : https://github.com/joskoot/format \
If needed choose defaults in all fields.\
Click Install.

Go to file/package manager.\
Choose Do what I mean,\
Enter https://github.com/joskoot/restricted-permutations.git \
If needed choose defaults in all fields.\
Click Install.

Require the package as follows:
(require restricted-permutations/R)

A restricted permutation p is a bijection of the set
of all natural numbers onto the same set such that:

exists m: forall k: k>=m implies p(k)=k

R.rkt provides functions for restricted permutations
and finite groups of restricted permutations.

Restricted permutations are represented by procedures,
but in such a way that procedures representing the same
mathematical permutation are the same in the sense of [eq?].
Groups too are represented in a way that representations of
the same mathematical group are the same in the sense of [eq?].

Have fun,
Jacob J. A. Koot
