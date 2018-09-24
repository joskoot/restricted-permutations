#lang scribble/manual

@(newline)
@(display " ┌────────────────────────────────────┐\n")
@(display " │ This may take some minutes and may │\n")
@(display " │ require up to 1.5 Gbyte of memory. │\n")
@(display " └────────────────────────────────────┘\n")
@(newline)
@(flush-output)
@(collect-garbage)

@(require
  scribble/core
  scribble/eval
  racket
  (only-in scribble/html-properties attributes)
  "R.rkt"
  (for-label
   "R.rkt"
   racket
   (only-in typed/racket Setof Natural Sequenceof Index))
  (for-syntax racket))

@; Nothing to be provided.

@(define lb linebreak)
@(define nb nonbreaking)
@; Below syntaxes are used such as to allow keyword arguments
@; without explicitly mentioning them in the definitions.
@(define-syntax-rule (nbsl x ...) (nb (seclink    x ...)))
@(define-syntax-rule (nbsr x ...) (nb (secref     x ...)))
@(define-syntax-rule (nbhl x ...) (nb (hyperlink  x ...)))
@(define-syntax-rule (nber x ...) (nb (elemref    x ...)))
@(define-syntax-rule (nbrl x ...) (nb (racketlink x ...)))
@(define-syntax-rule (nbr  x ...) (nb (racket     x ...)))
@(define (∈) (smaller "∈"))

@(define (make-color-style color)
  (define prop:color (color-property color))
  (define color-style (style #f (list prop:color)))
  (lambda (elem) (element color-style elem)))

@(define red   (make-color-style "red"))
@(define green (make-color-style "green"))
@(define black (make-color-style "black"))

@(define example-ns (make-base-namespace))

@(parameterize ((current-namespace example-ns))
  (namespace-require 'racket)
  (namespace-require '"R.rkt"))

@(define-syntax-rule (eval-example expr)
  (nb (element 'tt (begin (random-seed 0) (~s (eval 'expr example-ns))))))

@(define-syntax (example stx)
  (syntax-case stx ()
   ((_ a)
  #'(begin
     (nbr a)
     (hspace 1)
     "→"
     (hspace 1)
     (eval-example a)
     (lb)))))

@(define-syntax (color-example stx)
  (syntax-case stx ()
   ((_ color a)
  #'(begin
     (nbr a)
     (hspace 1)
     "→"
     (hspace 1)
     (elem #:style 'tt (color (eval-example a)))
     (lb)))))

@(define-syntax (example/n stx)
  (syntax-case stx ()
   ((_ a)
  #'(begin
     (nbr a)
     (hspace 1)
     "→"
     (lb)
     (eval-example a)))))

@(define-syntax-rule (Tabular ((e ...) ...) . rest)
  (tabular (list (list e ...) ...) . rest))

@(define-syntax-rule (example-table x ...)
  (Tabular ((@nbr[x] "→" (eval-example x)) ...) #:sep (hspace 1)))

@(define(minus) (element 'tt "-"))
@(define(-?) (element "roman" ?-))
@(define (note . x) (inset (apply smaller x)))
@(define (inset . x) (apply nested #:style 'inset x))
@(define-syntax-rule (linespacebreak) @↑{@(hspace 1)@(lb)})
@(define (expt-1) @↑{@(minus)1})
@(define ↑ superscript)
@(define ↓ subscript)
@(define ⇒ @larger{⇒})

@(define constr-style
 (nbhl "https://docs.racket-lang.org/drracket/output-syntax.html" "constructor style"))
        
@title[#:version ""]{Restricted Permutations}
@author{Jacob J. A. Koot}

@(defmodule "R.rkt" #:packages ())

Module @nbhl["R.rkt" "R.rkt"] imports the following modules and exports all its imports@(lb)
with exception of a minor modification related to @nbsl["Cleanup" "cleanup"].
@inset{@Tabular[
(("Module" "Documentation in section") 
 (@nbhl["N.rkt" "N.rkt"] @(nbsr "N"))
 (@nbhl["C.rkt" "C.rkt"] @(nbsr "C"))
 (@nbhl["P.rkt" "P.rkt"] @(nbsr "P"))
 (@nbhl["G.rkt" "G.rkt"] @(nbsl "G" "Finite subgroups"))
 (@nbhl["H.rkt" "H.rkt"] @(nbsr "H")))
 #:sep (hspace 3)
 #:row-properties (list 'top-border 'top-border '() '() '() 'bottom-border)]}

@section{Introduction}
In this docu@(-?)ment the word `permutation' is used in mathematical sense,
id est, such as to mean a bijection of a set onto the same set.

@elemtag["rearrangement" ""]
@note{The word `permutation' often is used for rearrangements.
For example, two lists like @nbr[(1 2 0)] and @nbr[(0 1 2)]
often are called permutations of each other.
In this docu@(-?)ment they are called rearrange@(-?)ments of each other,
the word `permutation' being reserved for bijections of a set onto the same set.
Rearrange@(-?)ments can represent permutations, though.
If there is no danger of confusion,
a representing object can be written or talked about
as though it were the object it represents,
@nb{but this} is avoided in this docu@(-?)ment.
However, no formal distinction will be made between
@nbsl["numbers"
#:doc '(lib "scribblings/guide/guide.scrbl")
"exact integer numbers of Racket"]
and the abstract integer numbers they represent.
@nb{See section} @nbsl["N" "Natural/integer numbers"].}

@elemtag["R" ""]
Let @bold{N} be the set of all natural numbers, 0 included.
Define a restricted permutation, @nb{say p},
as a permutation of @bold{N} with the following restriction:

@inset{@nb{∃m@(∈)@bold{N}: ∀k@(∈)@bold{N}: k≥m @⇒ p(k) = k}}

Let's call the least natural number m for which the restriction holds
@italic{the} restriction of p.
`R' is shorthand for `restricted permutation'
and `@bold{R}' for `the set of all Rs'.
@elemtag["composition"]Define the composition:

@inset{@nb{p,q@(∈)@bold{R} → pq@(∈)@bold{R}}}

as usual for functions p and q with compatible domain of p and range of q:

@inset{@nb{pq: k@(∈)@bold{N} → p@larger{(}q(k)@larger{)}@(∈)@bold{N}}}

@bold{R} always will be associated with this composition,
thus forming a @nber["group"]{group},
in particular a denumerable infinite group.
As required, the composition is associative.
For some groups the composition is commutative.
For @bold{R} it is not,
although it is commutative for many subgroups of @bold{R},
but certainly not for all of them.
For every finite group, @bold{R} has an isomorphic subgroup.

@note{In fact exactly one such subgroup
(consisting of the @nber["id"]{identity of @bold{R}} only)
if the order @nb{(= cardinality)} of the group is 1 and
an infinite number of them if the order is greater than 1.}

@note{@elemtag["group"]{The present document is not an introduction to group theory.
It refers to mathematical concepts without providing definitions and
mentions theorems without proofs.
See chapters 1 and 2 of
@nbhl[
 (string-append
  "https://ia800307.us.archive.org/18/items/"
  "GroupTheoryAndItsApplicationToPhysicalProblems/"
  "Hamermesh-GroupTheoryAndItsApplicationToPhysicalProblems.pdf")
 "Group Theory by Morton Hamermesh"].
If you know nothing about quantum mechanics,
you'd better skip its introduction.
Quantum mechanics play no role in chapter 1, nor in chapter 2.
As an alternative see @nbhl["finite-groups.doc" "finite-groups.doc"].}}

Let p and q be two Rs with restrictions r@↓{p} and r@↓{q} and
let r@↓{pq} be the restriction of the composition pq.
We have @nb{0 ≤ r@↓{pq} ≤ max(r@↓{p}@bold{,}r@↓{q}).}
The restriction of pq not necessarily equals that of qp.
See the @nber["P-example"]{example}
in the description of procedure @nbr[P-compose].
@elemtag["id" "The identity"] of @bold{R} is:

@inset{@nb{∀k@(∈)@bold{N}: k → k}}

This is the only R with restriction 0 and @nbrl[P-order "order"] 1.
For every other R the restriction and order are greater than 1,
but always finite. They are not necessarily the same.
@nbrl[P-inverse]{Inverses} of each other have the same order and restriction.
There are n! Rs with restriction less than or equal to natural @nb{number n}.
These form a finite subgroup of @bold{R} isomorphic to the
@nbrl[G-symmetric]{symmetric group} S@↓{n}.

@note{In every group, not only in @bold{R},
the identity is the only element of order 1 and
inverses of each other have the same order.}

@note{There is no R with restriction 1.
If p is a permutation of @bold{N}
with @nb{[∀k@(∈)@bold{N}: k≥1 @⇒ p(k) = k}], then @nb{[p(0) = 0]}
and hence @nb{[∀k@(∈)@bold{N}: p(k) = k]},
which means that p is the identity with restriction 0.
Let a(m) be the number of Rs with restriction m. We have:
@nb{a(0)=1} and @nb{∀m@(∈)@bold{N}: a(m+1) = (m+1)!@(minus)m! = mm!}.
This implies: @nb{a(1) = 0.}
Furthermore: @nb{@larger{Σ}@↓{(m=0@bold{..}n)}a(m) = n!},
where m runs from 0 up to and including n.}

@note{Do not confuse the @nbrl[P-order]{order of an element}
with the @nbrl[G-order]{order of a group}.
The latter is the cardinality of a group,
but it usually is called its @italic{order}.
The word `order' also is used for the consecution of elements in a list or vector.
In most cases it is clear with which meaning the word is used.
Where there is danger of confusion, a phrase is used that avoids confusion.}

An R is an abstract mathematical concept.@(lb)
The following @nber["representations" "representations"]
in terms of Racket objects are used:

@inset{@tabular[#:sep (list (hspace 1) ":" (hspace 1))
(list
 (list "P" @seclink["P"]{Function-representation})
 (list "C" @seclink["C"]{Cycle-representation})
 (list "H" @seclink["H"]{Hash-representation}))]}

A G is a Racket object representing a @seclink["G"]{finite subgroup of @bold{R}}.

@note{Hs are for internal use behind the screen. @red{Advice}: avoid explicit use of Hs.}

@note{@elemtag["representations"]{
In this docu@(-?)ment the word `representation' refers to the way abstract mathematical concepts
are expressed in terms of Racket objects.
In group theory the word has quite another meaning
(group of coordinate transformations in a linear space)
In this docu@(-?)ment the word is not used with the group theoretical meaning.}}

Notice that

@inset{
 @racketblock0[
(lambda ([k : Natural]) (code:comment #,(element 'roman (red "This is not an R.")))
 ((if (even? k) add1 sub1) k))]}

can represent a permutation of @bold{N} but does not represent an R
because it does not satisfy the above @nber["R" "restriction"].

@section[#:tag "N"]{Natural/integer numbers}

The
@nbsl[
"numbers"
#:doc '(lib "scribblings/guide/guide.scrbl")
"exact integer numbers of Racket"]
represent their abstract mathematical counter@(-?)parts exactly.
Although the representation cannot be complete because of memory and performance limits,
no distinction is needed between abstract integer numbers and
the exact integer numbers of Racket by which they are represented.
Therefore, in this docu@(-?)ment no distinction is made between
@nbrl[exact-integer? "exact integer numbers of Racket"] and abstract integer numbers nor between
@nbrl[exact-nonnegative-integer? "exact non-negative integers of Racket"]
and the corresponding abstract natural numbers.

@bold{N} is the set of all natural numbers,
@bold{N@↑{+}} the set of all positive natural numbers and
@bold{Z} the set of all integer numbers.
The following synonyms are provided by module @nbhl["N.rkt" "N.rkt"]
and used in the description of the procedures shown in this docu@(-?)ment,
particularly in their specifications of data types:

@deftogether[
 (@defproc[#:kind "predicate" (N?  (x any/c)) boolean?]
  @defproc[#:kind "predicate" (N+? (x any/c)) boolean?]
  @defproc[#:kind "predicate" (Z?  (x any/c)) boolean?])]{
@Tabular[
  (("Predicate" "Synonym of"                      "In the sense of")
   (@nbr[N?]    @nbr[exact-nonnegative-integer?]  @nbr[free-identifier=?])
   (@nbr[N+?]   @nbr[exact-positive-integer?]     @nbr[free-identifier=?])
   (@nbr[Z?]    @nbr[exact-integer?]              @nbr[free-identifier=?]))
  #:sep (hspace 3)
  #:row-properties (list '(top-border bottom-border) '() '() 'bottom-border)]}

@note{In this document @bold{R} is the group of @nber["R"]{restricted permutations}@(lb)
and has nothing to do with the set of real numbers.}

@section[#:tag "C"]{Cycle notation}

All objects described in this section are defined in module @nbhl["C.rkt" "C.rkt"].
`C' is shorthand for `cycle notation'.
A C represents an @nber["R" "R"] and is one of the following:

@itemlist[#:style 'ordered
(list
 @item{
  A single C, which is a list of distinct @nbsl["N"]{natural numbers}.
  It represents the @nber["R" "R"]
  that maps each element of the list onto the next one and the last element onto the first one.
  Every @nbsl["N"]{natural number} that is not part of the single C, is mapped onto itself. 
  The empty list and every single C of one element represent the
  @nber["id"]{identity} of @nber["R"]{@bold{R}}.
  The @nber["id"]{identity} has @nbrl[P-order "order"] 1.
  A non-empty single C of n elements represents an @nber["R" "R"] of @nbrl[P-order "order"] n.
  The @racket[reverse] of a single C represents the inverse
  of the @nber["R" "R"] represented by the original single C.}
 @item{
  A list of Cs.
  Represents the @nber["composition" "composition"] of the @nber["R" "Rs"] represented
  by its elements. An element of a list of Cs can be a list of Cs, but
  superfluous pairs of parentheses can be ignored,
  because the @nber["composition" "composition"] is associative.
  The order in which the single Cs appear in the list can be relevant,
  because they are not required to commute with each other.})]

@elemtag["normalized-C"]{A normalized C is one of the following:}

@itemlist[#:style 'ordered
(list
 @item{
  The empty list. It is the one and only normalized C representing the
  @nber["id"]{identity of @bold{R}}.}
 @item{
  A single C of at least two elements and the first element being the least one.
  @nb{A circular} shift of a single C represents the same @nber["R" "R"]
  as the original single C.
  Therefore a non-normalized single C of at least two elements can be normalized
  by shifting it circularly until its least element is in front.}
 @item{
  A list of two or more disjunct non-empty normalized single Cs,
  sorted in increasing order of their lengths
  and among normalized single Cs of the same length
  in increasing order of the first element.
  Sorting is possible because @nber["R" "Rs"] represented by disjunct single Cs
  commute with each other.
  The @nbrl[P-order "order"] of the represented @nber["R" "R"]
  is the least common multiple of the lengths of the single Cs.})]

@elemtag["Cs"]{For every C there is exactly one normalized C
(in the sense of @nbr[equal?]) representing the same @nber["R" "R"].
For every @nber["R" "R"] there is exactly one normalized C
(in the sense of @nbr[equal?] and ignoring memory limits).
See procedure @nbr[C-normalize] for examples.}

@deftogether[
 (@defproc[#:kind "predicate" (C?            (x any/c)) boolean?]
  @defproc[#:kind "predicate" (C-normalized? (x any/c)) boolean?])]{
Predicate @nbr[C?] does not discriminate between normalized and non-normalized Cs.@(lb)
Predicate @nbr[C-normalized?] returns @nbr[#t] for @nber["normalized-C" "normalized Cs"] only.}

@defproc[(C-normalize (c C?)) C-normalized?]{
Returns the normalized form of its argument.
Examples:}

@example-table[
(C-normalize '(1 0))
(C-normalize '(1 2 0))
(C-normalize '((1 2) (0 3)))
(C-normalize '((0 2) (0 1)))
(C-normalize '((0 1) (0 2)))
(C-normalize '((0 1) (0 1 2)))
(C-normalize '((0 2) (0 1 2)))
(C-normalize '((1 2) (0 1 2)))
(C-normalize '((0 1 2) (0 1)))
(C-normalize '((0 1 2) (0 2)))
(C-normalize '((0 1 2) (1 2)))
(C-normalize '(0 1 2 3))
(C-normalize '(1 2 3 0))
(C-normalize '(2 3 0 1))
(C-normalize '(3 0 1 2))
(C-normalize '((0 1) (1 2) (2 3)))
(C-normalize '((() () ())))
(C-normalize '(((9))))
(C-normalize '((1) (2) (3)))
(C-normalize '((0 1) (0 1)))
(C-normalize '((0 1 2) (3 4)))
(C-normalize '((4 2 3) (1 0)))
(C-normalize '((0 1 2) (0 1 2)))
(C-normalize '((0 1 2) (2 1 0)))
(C-normalize '((0 1 2) (1 2 3)))
(C-normalize '((0 1 2) (2 3 4)))
(C-normalize '((0 1 2) (2 3 0)))]

The Cs shown below represent the same @nber["R" "R"].
Therefore @nbr[C-normalize] produces the same normalized C for them
@nb{(in the sense of @nbr[equal?])}:

@example-table[
(C-normalize '((0 1) (1 2)))
(C-normalize '((0 2) (0 1)))
(C-normalize '((1 2) (0 2)))
(C-normalize '(0 1 2))
(C-normalize '(1 2 0))
(C-normalize '(2 0 1))]

@defproc[(C-identity? (x any/c)) boolean?]{
Same as @nbr[(and (C? x) (null? (C-normalize x)))]}

@defproc[(C-transpositions (c C?)) C?]{
Returns a list of normalized transpositions
representing the same @nber["R" "R"] as the argument.
A transposition is a single C of two elements.
For every C there is a list of transpositions
representing the same @nber["R" "R"].
In most cases the @nber["R" "R"]s represented by the transpositions do not commute.
Hence the order in which the transpositions appear in the list usually is relevant.
The list of transpositions is not uniquely defined.
@nbr[C-transpositions] returns one only,
but always the same one (in the sense of @nbr[equal?])
for Cs representing the same @nber["R" "R"]
and with no more transpositions than necessary.
An @nber["R" "R"] is either even or odd,
id est,
the length of its representation as a list of transpositions is either even or odd.

@note{@elemtag["parity"]{Every C can be written as a list of transpositions.
If it can be written as a list of an even number of transpositions,
it cannot be written as a list of an odd number of transpositions and reversely.
Hence every C, and consequently every @nber["R" "R"], has well defined parity.
Composition of two @nber["R" "Rs"] with the same parity yields an even @nber["R" "R"].
Composition of two @nber["R" "Rs"] with opposit parity yields an odd @nber["R" "R"].
The @nber["id"]{identity of @bold{R}} has even parity.}
A group containing at least one odd element has as many odd ones as even ones.
The subset of all even elements of a finite group is an
@nbrl[G-invariant-subg? "invariant subgroup"].}}

Examples:

@example-table[
(C-transpositions '())
(C-transpositions '(0 1))
(C-transpositions '(0 1 2))
(C-transpositions '(2 1 0))
(C-transpositions '(0 1 2 3 4))
(C-transpositions '(1 2 3 4 0))
(C-transpositions '(2 3 4 0 1))
(C-transpositions '((0 1) (2 3)))
(C-transpositions '((0 1) (0 1)))
(C-transpositions '((0 1 2) (3 4 5)))
(C-transpositions '((3 4 5) (0 1 2)))]

The Cs shown in the example below represent the same @nber["R" "R"].
Therefore procedure @nbr[C-transpositions] produces the same list of transpositions for them
@nb{(in the sense of @nbr[equal?])}:

@example-table[
(C-transpositions '((0 1) (1 2)))
(C-transpositions '((0 2) (0 1)))
(C-transpositions '((1 2) (0 2)))
(C-transpositions '(0 1 2))
(C-transpositions '(1 2 0))
(C-transpositions '(2 0 1))]

Because every @nber["R" "R"] represented by a transposition equals its inverse,
reversal of the list of transpositions always produces a C representing the inverse.
This implies that inverses of each other have the same parity.
Example:

@interaction[
(require racket "R.rkt")
(for/and ((p (in-G (G-symmetric 4))))
 (define c (P->C p))
 (define transpositions (C-transpositions c))
 (C-identity? (list transpositions (reverse transpositions))))]

@defproc[(H->C (h pseudo-H?)) C-normalized?]{
Returns the normalized C representing the same @nber["R" "R"] as @nbr[h].@(lb)
You probably never need this procedure.@(lb)@nb{@red{Advice: avoid it}.}}

@defproc[(C->H (c C?)) H?]{
Returns an @nbsl["H" "H"] representing the same @nber["R" "R"] as @nbr[c].@(lb)
You probably never need this procedure.@(lb)@nb{@red{Advice: avoid it}.}}

@section[#:tag "P"]{Function representation}

All objects described in this section are defined in
module @nbhl["P.rkt" "P.rkt"].
A P is a procedure @nbr[(-> N? N?)] representing an @nber["R" "R"].
Given the same argument, a P returns the same @seclink["N"]{natural number}
as the represented @nber["R" "R"], of course.
Every @nber["R" "R"] can be represented by a P (ignoring memory limits).
Although Ps are procedures,
those representing the same @nber["R" "R"] are the same in the sense of @nbr[eq?].
@red{Warning}: this may not remain true after @nbsl["Cleanup" "cleanup"].
In fact Ps are
@nbsl["structures" #:doc '(lib "scribblings/reference/reference.scrbl") "structures"]
with @nbrl[prop:procedure "procedure property"].
A P contains its @nbsl["H" "H-representation"].
It memorizes its normalized @nbsl["C" "C-representation"],
its @nbrl[P-order #:style #f]{order},
its @nbrl[P-period #:style #f]{period} and
its @nbrl[P-inverse #:style #f]{inverse},
but only after they have been needed for the first time.
A P is written, printed or displayed in @constr-style as:

@inset{@nb{@elem[#:style 'tt]{(@nbr[P] @bold{@literal{'}}@italic{c})}}}

where @elem[#:style 'tt @italic{c}] is the normalized @nbsl["C" "C-representation"].
@(lb)An exception is made for the @nbr[P-identity], which is written as:

@inset{@nbr[P-identity]}

which can be regarded as @constr-style too.

@defproc[(P (p (or/c P? C?)) ...) P?]{
Returns the P representing the @nber["R" "R"] formed by @nber["composition" "composition"] of the
@nber["R" "Rs"] represented by the arguments.
If no argument is given, the @nbr[P-identity] is returned.
If only one argument is given, the returned P represents the same
@nber["R" "R"] as the argument.
Examples:}

@interaction[
(require racket "R.rkt")
(define p (P '(2 3) '(4 5 6)))
(for ((k (in-range 10))) (printf "~s -> ~s~n" k (p k)))]

@example-table[
(P)
(P '())
(P '(0 1) '(0 1))
(P '(((0 1) (0 1))))
(P '(0 1))
(P '(1 0))
(P '(0 1) '(2 3 4))
(P '(0 1 2 3))
(P '(1 2 3 0))
(P '(2 3 0 1))
(P '(3 0 1 2))
(P '(0 1) '(1 2) '(2 3))
(P '(2 3) '(1 2) '(0 1))]

Let's do some checks that two Ps representing the same @nber["R" "R"]
are the same in the sense of @nbr[eq?]
(assuming that no disturbing @nbsl["Cleanup" "cleanup"] is made)

@interaction[
(require racket "R.rkt")
(define a (P '(3 4) '(4 5)))
(define b (P '(4 5 3)))
(code:comment #,(list "a and b represent the same " (elemref "R" "R") ":"))
(code:line (for/and ((k (in-range 10))) (= (a k) (b k))) (code:comment #,(green "ok")))
(code:comment "Hence:")
(code:line (eq? a b) (code:comment #,(green "ok")))]

Another example:

@interaction[
(require racket "R.rkt")
(define p (P '((0 2) (3 4 5))))
(define q (P-inverse p))
q
(code:comment "Because p and q are the inverses of each other, we have:")
(and
 (eq? (P-inverse p) q)
 (eq? (P-inverse q) p)
 (eq? (P p q) P-identity)
 (eq? (P q p) P-identity))]

@nbr[P] is associative, of course. For example:

@interaction[
(require racket "R.rkt")
(define in-S4 (in-G (G-symmetric 4)))
(for*/and ((a in-S4) (b in-S4) (c in-S4))
 (define x (P a (P b c)))
 (define y (P (P a b) c))
 (define z (P a b c))
 (and (eq? x z) (eq? y z)))]

@defproc[(P-compose (p (or/c P? C?)) ...) P?]{
Same as procedure @nbr[P] in the sense of @nbr[free-identifier=?].@(lb)
Some checks on the properties of @nber["composition" "composition"]s of Ps:}

@interaction[
(require racket "R.rkt")
(define S4 (G-symmetric 4))
(define in-S4 (in-G S4))
(for*/and ((p in-S4) (q in-S4))
 (define pq (P-compose p q))
 (define qp (P-compose q p))
 (define max-restriction
  (max
   (P-restriction p)
   (P-restriction q)))
 (and
  (G-member? pq S4)
  (G-member? qp S4)
  (=   (P-order pq) (P-order qp))
  (eq? (P-even? pq) (P-even? qp))
  (<= 0 (P-restriction pq) max-restriction)
  (<= 0 (P-restriction qp) max-restriction)))]

@elemtag["P-example"]{
The @nber["R" "restriction"] of pq not necessarily equals that of qp:}

@interaction[
(require racket "R.rkt")
(define p (P '((1 2) (3 4))))
(define q (P '( 1 2   3 4)))
(define pq (P-compose p q))
(define qp (P-compose q p))
(define-syntax-rule (print-restrictions x ...)
 (begin
  (printf "~s = ~s with restriction ~s~n" 'x x (P-restriction x))
  ...))
(print-restrictions pq qp)]

When composing two or more Ps with Racket's procedure @nbr[compose],
the result is a procedure that yields the same answers as when made
with procedure @nbr[P-compose] or @nbr[P],
but the result is not a P. Example:

@interaction[
(require racket "R.rkt")
(define a (P '(0 1 2)))
(define b (P '(1 2 3)))
(define c (P '(2 3 4)))
(define  abc (  compose a b c))
(define Pabc (P-compose a b c))
(for/and ((k (in-range 10))) (= (abc k) (Pabc k)))
(code:comment "But:")
(code:line (P? abc) (code:comment #,(red "alas:")))
(code:comment "whereas:")
(code:line (P? Pabc) (code:comment #,(green "ok:")))
(code:comment #,(list
 "Racket's procedure "
 (nbr compose)
 " does not return "
 (nbr equal?)
 " results for "))
(code:comment #,(list (nbr eq?) " arguments when called with two or more arguments."))
(code:line (equal? (compose a b c) (compose a b c)) (code:comment #,(red "alas:")))
(code:comment #,(list
 (nbr P)
 " does, even "
 (nbr eq?)
 " when the result represents the same "
 (elemref "R" "R")))
(code:comment #,(list
 "(and no disturbing "
 (nbsl "Cleanup" "cleanup")
 " interferes)"))
(eq? (code:comment #,(green "ok"))
 (P-compose (P-compose a b) c)
 (P-compose a (P-compose b c)))
(code:comment "also:")
(eq? (code:comment #,(green "ok"))
 (P-inverse (P-compose a b c))
 (P-compose (P-inverse c) (P-inverse b) (P-inverse a)))]

@note{Notice that (abc)@↑{@(minus)1} = c@↑{@(minus)1}b@↑{@(minus)1}a@↑{@(minus)1},
writing x@↑{@(minus)1} for the inverse of x.}

@defproc[#:kind "predicate" (P? (x any/c)) boolean?]

@defidform[#:kind "constant" P-identity]{
The P representing the @nber["id" "identity"] of @nber["R"]{@bold{R}.}
A P representing the identity always is the same as @nbr[P-identity]
in the sense of equivalence relation @nbr[eq?],
even after @nbsl["Cleanup" "cleanup"].}

@defproc[#:kind "predicate" (P-identity? (x any/c)) boolean?]{
Same as @nbr[(eq? x P-identity)].
The predicate remains valid after @nbsl["Cleanup" "cleanup"].}

@defproc[(P->C (p P?)) C-normalized?]{
Returns the normalized @nbsl["C" "C-representation"] of @nbr[p].}
Examples:

@example-table[
(P->C P-identity)
(P->C (P))
(P->C (P '(0 1)))
(P->C (P '(1 0)))
(P->C (P '(0 1) '(0 1)))
(P->C (P '(0 1) '(2 3 4)))
(P->C (P '(0 1 2 3)))
(P->C (P '(1 2 3 0)))
(P->C (P '(2 3 0 1)))
(P->C (P '(0 1) '(1 2) '(2 3)))
(P->C (P '(2 3) '(1 2) '(0 1)))]

@defproc[(P-order (p (or/c P? C?))) N+?]{
For every argument @nbr[p] there is a least
@nbsl["N"]{positive natural number} @nbr[k]
such that @nb{@nbr[(P-expt p k)] → @nbr[P-identity].}
@nbr[k] is called the order of the @nber["R" "R"] represented by @nbr[p].
The @nber["id" "identity"] of @nber["R"]{@bold{R}}
is the only @nber["R" "R"] of order 1.
For every other @nber["R" "R"] the order is greater than 1.}

@note{
The order of an element of a finite group always is a divisor of the
@nbrl[G-order "order of the group"].@(lb)
Do not confuse the order of a group element with the order of a group.}

Examples:

@interaction[
(require racket "R.rkt")
(define a (P '(0 1)))
(define b (P '(2 3 4)))
(define c (P '(5 6 7 8 9)))
(define e P-identity)
(define (show p)
 (printf "~a has order ~a~n"
  (~s #:min-width 27 #:align 'right (P->C p))
  (~s #:min-width 2  #:align 'right (P-order p))))
(for-each show
 (list
  e
  a
  b
  c
  (P-compose a b)
  (P-compose a c)
  (P-compose b c)
  (P-compose a b c)))]

@defproc*[(((P-period (p P?)) (and/c (vectorof P?) immutable?))
           ((P-period (c C?)) (and/c (vectorof P?) immutable?)))]{
If the argument is a @nbsl["C" "C"] it is first converted to a @nbsl["P" "P"].
@nbr[(P-period c)] is treated as @nbr[(P-period (P c))].
Procedure @nbr[P-period] returns an immutable vector of length @nbr[(P-order p)] containing the
powers of @nbr[p].
Element with index @nbr[i] of the vector contains @nbr[(P-expt p i)].
The period and the order of @nbr[p] are memorized in @nbr[p].
They are not computed again when already available.
The first element @nb{(index 0)} of the vector always is @nbr[P-identity].
If @nbr[p] is not the @nbr[P-identity],
the second element @nb{(index 1)} is @nbr[p] itself.
The last element always is the @nbrl[P-inverse "inverse"] of @nbr[p].
In fact, when omitting the first element (index 0, id est, the @nbr[P-identity]),
the elements taken from right to left are the inverses of the elements
taken from left to right.}
Examples:

@example-table[
(P-period P-identity)
(P-period (P '(0 1)))
(P-period (P '(3 5 7)))]

@interaction[
(require "R.rkt")
(for/and ((p (in-G (G-symmetric 4))))
 (define period (P-period p))
 (define order (P-order p))
 (and
  (P-identity? (vector-ref period 0))
  (for/and ((k (in-range 1 order)))
   (eq?
    (vector-ref period (- order k))
    (P-inverse (vector-ref period k))))))]

@defproc*[(((P-expt (p P?) (k Z?)) P?) ((P-expt (c C?) (k Z?)) P?))]{
@nbr[(P-expt c k)] is treated as @nbr[(P-expt (P c) k)].
Procedure @nbr[P-expt] computes @nbr[p]@(↑ (nbr k)).@(lb)
In fact @nbr[P-expt] collects the power from the @nbr[P-period] as in:
@(inset @nbr[(vector-ref (P-period p) (modulo k (P-order p)))])
The period and the order are memorized in @nbr[p].
If the period and order already are available, they are
recollected from @nbr[p] without computing them again.}

@note{Let x be a group element of finite order m.
Then @nb{∀k@(∈)@bold{Z}: x@↑{k} = x@↑{k @bold{modulo} m}}.}

Large exponents do no harm.
The power is computed almost as fast as for small exponents.
The computation of the modulus of an exponent with great absolute value may be somewhat slower,
though.

@(collect-garbage)

@interaction[
(require "R.rkt" racket)
(code:line (define big (* 6 (expt 10 1000000))) (code:comment "= #e6e1000000"))
(define exponents (range -6 7))
(define big-exponents (map (curry + big) exponents))
(define -big-exponents (map - big-exponents))
(define p (P '(0 1 2) '(3 4)))
(code:line (P-period p) (code:comment "Computes the order and all powers and memorizes them."))
(define (P-expt-p k) (P-expt p k))
(define-syntax-rule (timer exponents)
 (begin
  (collect-garbage)
  (time (for-each P-expt-p exponents))))
(begin
 (timer      exponents)
 (timer  big-exponents)
 (timer -big-exponents))]

For every group @bold{X} we have:

@inset{
∀p@(∈)@bold{X}: ∀k,m@(∈)@bold{Z}: (p@↑{k})@↑{m} = p@↑{km}@(hspace 3)and@(lb)
∀p@(∈)@bold{X}: ∀k,m@(∈)@bold{Z}: p@↑{k}p@↑{m} = p@↑{k+m}}

This applies to @nber["R" (bold "R")] too, of course. For example:

@interaction[
(require "R.rkt")
(define p (P '(0 1) '(3 4 5)))
(P-order p)
(define in-exponents (in-range -10 10))
(for*/and ((k in-exponents) (m in-exponents))
 (and
  (eq? (P-expt (P-expt p k) m)       (P-expt p (* k m)))
  (eq? (P (P-expt p k) (P-expt p m)) (P-expt p (+ k m)))))]

@defproc*[(((P-inverse (c C?)) P?) ((P-inverse (p P?)) P?))]{
If the argument is a @nbsl["C" "C"] it is first converted to a @nbsl["P" "P"].
@nbr[(P-inverse c)] is treated as @nbr[(P-inverse (P c))].
Procedure @nbr[P-inverse] returns the P representing the inverse of the
@nber["R" "R"] represented by the argument.
The inverse is memorized in @nbr[p].
When already available, it is recollected immediately from @nbr[p].
The @nbrl[P-order #:style #f]{order}, @nber["R" "restriction"],
@nbrl[P-even? #:style #f]{parity} and
@nbrl[P-non-fixed-points #:style #f]{non-fixed points}
of the inverse are the same as those of argument @nbr[p].}
Examples:

@example-table[
(P-inverse P-identity)
(P-inverse (P '(0 1)))
(P-inverse (P '(6 5)))
(eq? (P-inverse (P '(6 5))) (P '(6 5)))
(P-inverse (P '(0 1 2)))
(P-inverse (P '(0 1 2) '(3 4)))]

@interaction[
(require racket "R.rkt")
(define S4 (G-symmetric 4))
(G-order S4)
(for/and ((p (in-G S4)))
 (define q (P-inverse p))
 (and
  (P-identity? (P q p))
  (P-identity? (P p q))
  (equal? (P-non-fixed-points p) (P-non-fixed-points q))
  (=      (P-order            p) (P-order            q))
  (=      (P-restriction      p) (P-restriction      q))
  (eq?    (P-even?            p) (P-even?            q))))]

For every group @bold{X} we have:

@inset{@nb{∀a,b@(∈)@bold{X}: (ab)@(expt-1) = b@(expt-1)a@(expt-1)}}

This applies to @nber["R" @bold{R}] too:

@interaction[
(require racket "R.rkt")
(define in-S4 (in-G (G-symmetric 4)))
(for*/and ((a in-S4) (b in-S4))
 (eq?
  (P-inverse (P-compose a b))
  (P-compose (P-inverse b) (P-inverse a))))]

@defproc[(P-even? (p (or/c P? C?))) boolean?]{
Returns @nbr[#t] if the @nber["R" "R"] represented by the argument is even.@(lb)
Returns @nbr[#f] if the @nber["R" "R"] represented by the argument is odd.@(lb)
See the @nber["parity"]{note} in the description of procedure @nbr[C-transpositions].}
@(lb)Examples:

@example-table[
(P-even? P-identity)
(not (P-even? (P '(0 1))))
(P-even? (P '(0 1) '(2 3)))
(P-even? (P '(0 1) '(1 2)))
(not (P-even? (P '(0 1) '(1 2) '(1 0))))
(P-even? (P '(0 1 2)))
(eq? (P '(0 1 2)) (P '(0 2) '(0 1)))
(not (P-even? (P '(0 2 4 6))))
(eq? (P '(0 2 4 6)) (P '(0 6) '(0 4) '(0 2)))]

@interaction[
(require "R.rkt")
(define S3-list (G->list (G-symmetric 3)))
(filter P-even? S3-list)
(filter (compose not P-even?) S3-list)]

Let's check that a @nbsl["G" "G"] with at least one odd element
has as many odd as even elements.

@interaction[
(require "R.rkt" racket/set)
(code:comment "Procedure check returns \"all even\" if g has no odd elements or")
(code:comment "\"as many evens as odds\" if g has as many odd as even elements.")
(code:comment "Else raises an error, which should never happen.")
(define (check g)
 (define in-g (in-G g))
 (define  odd-set (for/seteq ((p in-g) #:unless (P-even? p)) p))
 (define even-set (for/seteq ((p in-g) #:when   (P-even? p)) p))
 (cond
  ((zero? (set-count odd-set)) "all even")
  ((and
    (= (set-count  odd-set)
       (set-count even-set)
       (/ (G-order g) 2))
    (for/and ((odd-p (in-set odd-set)))
     (equal?
      (for/seteq ((even-p (in-set even-set))) (P odd-p even-p))
      odd-set)))
   "as many evens as odds")
  (else (error 'check "this should never happen: ~s" g))))
(code:comment "Checks on some symmetric groups:")
(for/and ((n (in-range 2 6)))
 (equal? (check (G-symmetric n)) "as many evens as odds"))
(code:comment "The statement holds for all groups containing at least one odd element.")
(code:comment "Two checks on a non-symmetric group:")
(define g (G '((0 1) (2 3)) '((4 5) (6 7)) '(8 9)))
(G-order g)
(code:comment "This order shows that g is not a symmetric group,")
(code:comment "for the order of a symmetric group always is a factorial.")
(check g)
(code:comment "")
(define h (G '((0 1) (2 3)) '((4 5) (6 7)) '(0 1)))
(G-order h)
(code:comment "This order shows that h is not a symmetric group,")
(code:comment "for the order of a symmetric group always is a factorial.")
(check h)
(code:comment "")
(code:comment "Checks on groups without odd elements.")
(check G-identity)
(check (G '(0 1 2)))
(check (G '((0 1 2 3) (2 3 4 5))))
(check (G '(0 1 2) '(1 2 3)))]

@defproc[(P<? (p0 (or/c P? C?)) (p1 (or/c P? C?))) boolean?]{
Defines a sorting order among @nber["R" "Rs"].
The first sorting key is the @nbrl[P-even? "parity"].
Even @nber["R" "Rs"] come before odd @nber["R" "Rs"].
The second sorting key is the order of the @nber["R" "Rs"].
The third sorting key is @nbr[(p k)] for the least argument @nbr[k]
for which the two @nber["R" "Rs"] represented by the two arguments return different values.
@nbr[P<?] remains comparing correctly after @nbsl["Cleanup" "cleanup"].
See @nbr[P-sort] for an example.}

@defproc[(P-sort (ps (listof (or/c P? C?)))) (listof P?)]{
@(nbsl "C" "Cs") are converted to Ps before sorting.
Procedure @nbr[P-sort] returns a sorted list of Ps using @nbr[P<?].
It continues sorting correctly after @nbsl["Cleanup" "cleanup"].} Example:

@(define comment1
  (list
   (nbr P-equal?)
   " is not disturbed by "
   (nbr R-clear-hashes)
   "."))
@(define comment2
  (list "In both lists the first element is the identity, hence "
   (nbr eq?)
   "."))
@(define comment3a
  (list
   "Because of the cleanup none of the other"))
@(define comment3b
  (list
   "corresponding elements are "
   (nbr equal?)
   ", let alone "
   (nbr eq?)
   "."))

@interaction[
(require racket "R.rkt")
(random-seed 0)
(code:line (define S3-list0 (G->list (G-symmetric 3))) (code:comment "S3-list0 is sorted."))
(code:line (R-clear-hashes) (code:comment #,(list "Does not disturb procedure " (nbr P-sort))))
(code:line (define S3-list1 (G->list (G-symmetric 3))) (code:comment "S3-list1 is sorted."))
(code:comment "")
(map P->C S3-list0)
(code:comment "")
(code:line (define in-rearrangements in-permutations) (code:comment #,(list
  "See " (elemref "note" "note below")".")))
(code:comment "")
(for/and ((rearranged-S3-list1 (in-rearrangements S3-list1)))
 (define sorted-rearranged-S3-list1 (P-sort rearranged-S3-list1))
 (and
  (code:comment #,comment1)
  (andmap P-equal? S3-list0 sorted-rearranged-S3-list1)
  (code:comment #,comment2)
  (eq? (car S3-list0) (car sorted-rearranged-S3-list1))
  (code:comment #,comment3a)
  (code:comment #,comment3b)
  (not
   (ormap equal?
    (cdr S3-list0)
    (cdr sorted-rearranged-S3-list1)))))]

@elemtag["note"]
@note{According to the @nber["rearrangement" "terminology"] used in this docu@(-?)ment,
Racket's procedure @nbr[in-permutations] produces a sequence of
rearrangements rather than a sequence of permutations.}

@defproc[(P-restriction (p P?)) N?]{
Returns the @nber["R" "restriction"] of the @nber["R" "R"]
represented by @nbr[p].} Examples:

@example-table[
(P-restriction P-identity)
(P-restriction (P '(0 1)))
(P-restriction (P '(0 1 2)))
(P-restriction (P '(99)))
(P-restriction (P '(0 99)))
(P-restriction (P '(98 99)))]

Notice that @example[(P '(99))] and @example[(C-normalize '(99))]

@defproc[(P-non-fixed-points (p P?)) (listof N?)]{
Returns a sorted list of all @nbsl["N"]{natural numbers}
that are not a fixed point of @nbr[p].
If @nbr[k] is a non-fixed-point of @nbr[p],
then @nbr[(p k)] is a non-fixed-point of @nbr[p] too.
The @nbrl[P-inverse "inverse"] of @nbr[p]
has the same non-fixed-points as @nbr[p].}
Examples:

@example[(P-non-fixed-points P-identity)]
@example[(P-non-fixed-points (P '(5 6) '(0 1 2)))]

@interaction[
(require racket "R.rkt")
(define in-S4 (in-G (G-symmetric 4)))
(for/and ((p in-S4))
 (define nfps (P-non-fixed-points p))
 (and
  (equal? (sort (for/list ((k (in-list nfps))) (p k)) <) nfps)
  (equal?
   (P-non-fixed-points p)
   (P-non-fixed-points (P-inverse p)))))]

@defproc[(P-fixed-point? (p P?) (k N?)) boolean?]{
Same as @nbr[(= (p k) k)].
The @nber["R" "restriction"] implies that
every P has an infinite number of fixed points
including every @nbsl["N"]{natural number} equal to or greater than the
@nber["R" "restriction"].
One may want the fixed points less than some positive natural number n,
especially where n is the maximal @nber["R" "restriction"] of the @nber["R" "Rs"]
of some @nbsl["G"]{finite subgroup of @bold{R}}.
This can be done as follows:}

@interaction[
(require racket "R.rkt")
(define (fixed-points p n)
 (for/list ((k (in-range n)) #:when (P-fixed-point? p k)) k))
(fixed-points (P '(0 1) '(5 6 7)) 10)
(define (pad x k) (~s #:width k x))
(for ((n (in-range 1 4)))
 (printf "~n ~nS~s~n" n)
 (for ((p (in-G (G-symmetric n))))
  (printf "~a has fixed points ~a and every k≥~s~n"
   (pad p 12) (pad (fixed-points p n) 7) n))
 (newline))]

@defproc[(P->H (p P?)) H?]{
You probably never need this procedure. @(lb)@red{Advice: avoid it}.}

@defproc[(H->P (h pseudo-H?)) P?]{
You probably never need this procedure. @(lb)@red{Advice: avoid it}.}

@note{Nevertheless, procedure @nbr[H->P] can sometimes be useful.@(lb)
See the @elemref["H->P-example" "example"] in section @nbsl["C3v"]{Group C@↓{3v}}}

@(define sequenceref
  (nbhl "https://docs.racket-lang.org/reference/sequences.html" "sequence"))

@section[#:tag "G"]{Finite subgroups of @nber["R" (bold "R")]}

All objects described in this section are defined in
module @nbhl["G.rkt" "G.rkt"].
A G represents a finite subgroup of @nber["R" (bold "R")] and is
written, displayed or printed in @constr-style as:

@inset{@nb{@elem[#:style 'tt]{
(@nbr[G] @nbr[P-identity] (@nbr[P] @bold{@literal{'}}@italic{c}) ...)}}}

showing all @nber["R" "Rs"] of the G in @nbrl[P-sort]{sorted} order
and where each @elem[#:style 'tt @italic{c}] is a normalized @nbsl["C" "C"].@(lb)
An exception is made for the @nbr[G-identity], which is written as:

@inset{@nbr[G-identity]}

which can be regarded as @constr-style too.

Gs produced by the procedures of this section and representing the same subgroup of
@nber["R" (bold "R")] are the same in the sense of @nbr[eq?].
@red{Warning}: this may not remain true after a @nbsl["Cleanup" "cleanup"].
For every finite group there is an isomorphic G (ignoring memory limits).

@defproc[(G (p (or/c P? C?)) ...) G?]{
Forms the smallest group containing all @nber["R" "Rs"] represented by the arguments.
Duplicate arguments representing the same @nber["R" "R"] do no harm.
If no argument is given, the @nbr[G-identity] is returned.

@note{By definition, a group recursively includes the @nber["composition" "compositions"]
of all pairs of its elements,@(lb)
the @nber["composition" "composition"] of each element with itself included.}}

Examples:

@(example/n (G))

@(example/n (G '()))

@(example/n (G P-identity))

@(example/n (G '(0 1)))

@(example/n (G '(0 1 2) '(1 2 0) '(2 0 1)))

@(example/n (G '(0 1) '(2 3)))

@(example/n (G '(0 1) '(1 2)))

@(example/n (G '(0 1) '(0 1 2)))

@interaction[
(require racket "R.rkt")
(define g (G '(0 3) '(0 1 2)))
(G-order g)
(G->list g)
(define in-g (in-G g))
(for*/and ((p in-g) (q in-g)) (G-member? (P p q) g))]

Notice that @nbr[(G '(0 1) '(1 2))] yields the same as @nbr[(G '(0 1) '(0 1 2))].@(lb)
Hence: @(example (eq? (G '(0 1) '(1 2)) (G '(0 1) '(0 1 2))))

@red{Warning:} We have:@(lb)
@(color-example green (eq? (P '((0 1) (1 2))) (P '(0 1) '(1 2))))
@red{but:}@(lb)
@(color-example red (eq? (G '((0 1) (1 2))) (G '(0 1) '(1 2))))
In particular:@(lb)
@(example/n (G '((0 1) (1 2))))
@(lb)and@(lb)
@(example/n (G '(0 1) '(1 2)))

@defidform[#:kind "constant" G-identity]{
The @(nbsl "G" "G") consisting of the @nbr[P-identity] only.}

@defproc[#:kind "predicate"(G-identity? (x any/c)) boolean?]{
Same as @nbr[(eq? x G-identity)].
This predicate remains valid after @nbsl["Cleanup" "cleanup"].}

@defproc[#:kind "predicate"(G? (x any/c)) boolean?]

@defproc[(in-G (g G?)) (Sequenceof P?)]{
Returns an eagerly @nbrl[P-sort "sorted"] @sequenceref of the elements of @nbr[g].}

@defproc[(G-member? (p (or/c P? C?)) (g G?)) boolean?]{
Returns @nbr[#t] if the @nber["R" "R"] represented by @nbr[p]
is an element of the @nbsl["G" "G"] represented by @nbr[g],@(lb)
else returns @nbr[#f].}
Examples:

@interaction[
(require racket "R.rkt")
(define g (G '(0 1) '(0 2)))
(define in-g (in-G g))
(code:comment "By definition, for every pair of elements of g")
(code:comment "the composition is an element of g too.")
(for*/and ((p in-g) (q in-g)) (G-member? (P p q) g))]

@color-example[green (G-member? P-identity G-identity)]
@color-example[red   (G-member? '(2 3) G-identity)]

@red{Warning}: procedure @nbr[G-member?] can be confused by a @nbsl["Cleanup" "cleanup"]:

@interaction[
(require racket "R.rkt")
(define c '(0 1))
(define g (G c))
(code:line (G-member? c g)  (code:comment #,(green "ok")))
(code:line (R-clear-hashes) (code:comment #,(red "caution")))
(code:line (G-member? c g)  (code:comment #,(red "alas")))]

@defproc[(G-print-table (g G?) (output-port output-port? (current-output-port))) void?]{
The @nber["composition" "composition"] table of @nbr[g] is printed in normalized
@nbsl["C" "cycle-notation"] on the @nbr[output-port].
Every element is the @nber["composition" "composition"] pq
of element p in the left column and element q in the top row.
The left column and top row are @nbrl[P-sort "sorted"] and start with the
@nbrl[P-identity "identity"].
The columns are aligned.}

@note{For every group @bold{X} with identity e we have: @nb{∀x@(∈)@bold{X}: ex = x = xe}.
Hence with the identity as the first label for both columns and rows,
the first row and first column of the table proper are the same as the labels.
Therefore we can omit the labels.} Example:

@interaction[
(require racket "R.rkt")
(define C3v (G '(0 1) '(0 1 2)))
(G-print-table C3v)]

See section @nbsl["C3v"]{Group C@↓{3v}}
for a more elaborated discussion of this group.

@defproc[(G-table (g G?)) (listof (listof P?))]{
Returns the @nber["composition" "composition"]
table of @nbr[g] as a list of lists of @nbsl["P" "Ps"].
The first row, id est (@nbr[car (G-table g)]),
and the first column, id est @nbr[(map car (G-table g))],
of the table are @nbrl[P-sort "sorted"].}

@interaction[
(require racket "R.rkt")
(define C3v (G '(0 1) '(0 1 2)))
(G-table C3v)]

@defproc*[(((G-symmetric (n N?) (offset N? 0)) G?)
           ((G-symmetric (lst (listof N?))) G?))]{
The first form returns the symmetric group of all @nbr[n]! @nbsl["P" "Ps"]
of the @nbsl["N"]{natural numbers}
from @nbr[offset] up to but not including @nbr[(+ offset n)].
All @nbsl["N"]{natural numbers} outside this range are
@nbrl[P-fixed-point?]{fixed points} of all elements of the group.
@nbr[(G-symmetric 0 offset)] and @nbr[(G-symmetric 1 offset)]
both evaluate to the @nbr[G-identity].
Obviously @nbr[G-symmetric] yields isomorphic groups when
called with the same value for @nbr[n].
The order of the returned G is @nbr[n]!.

The second form returns the symmetric group corresponding to all rearrangements of @nbr[lst].
Duplicate elements are ignored.
All @nbsl["N"]{natural numbers} not in the @nbr[lst]
are @nbrl[P-fixed-point?]{fixed points} of all elements of the group.
If the @nbr[lst] has less than two distinct elements, the @nbr[G-identity] is returned.
The order of the returned G is n! where n is the number of distinct elements of @nbr[lst].

@note{@red{Warning}: @nbr[G-symmetric] is not lazy. Because @nb{15! = 1,307,674,368,000},@(lb)
@nbr[(> n 15)] and
@nbr[(> (length (remove-duplicates lst =)) 15)]
almost certainly cause memory problems,
thrashing on virtual memory and slowing down the processor to
a few per cent of its capacity, eventually aborting because of lack of memory.}}

Example:

@interaction[
(require "R.rkt" racket)
(define g0 (G-symmetric 3))
(define g1 (G-symmetric 3 1))
(define g2 (G-symmetric 3 2))
(define gn (G-symmetric '(0 3 6)))
g0
g1
g2
gn
(and
 (G-isomorphism g0 g1)
 (G-isomorphism g0 g2)
 (G-isomorphism g0 gn)
 #t)
(code:comment "")
(and
 (eq? (G-symmetric '()) G-identity)
 (eq? (G-symmetric '(0 1 2)) (G-symmetric 3))
 (eq? (G-symmetric '(4 5 6)) (G-symmetric 3 4)))]

The order of a group being a factorial does not imply that the group is symmetric.@(lb)
For example:

@interaction[
(require "R.rkt" racket)
(define S3 (G-symmetric 3))
(define C3h (G '(0 1 2) '(3 4)))
(code:line (G-order C3h) (code:comment "The order is a factorial:"))
(code:comment "But:")
(G-isomorphism C3h S3)
(code:comment "On the other hand we do have:")
(define C3v (G '(0 1 2) '(0 1)))
(and (G-isomorphism C3v S3) #t)
(code:comment "In this special case we even have:")
(eq? C3v S3)]

@defproc[#:kind "predicate" (G-abelean? (g G?)) boolean?]{
A group is abelean if and only if all its elements commute with each other.
Sufficient is that all elements of a @nbrl[G-base]{base} commute with each other.
Examples:}

@color-example[green (G-abelean? (G '(0 1 2) '(3 4)))]
because: @color-example[ green (eq? (P '(0 1 2) '(3 4)) (P '(3 4) '(0 1 2)))]

But: 
@color-example[red (G-abelean? (G '(0 1 2) '(0 1)))]
because: @color-example[red (eq? (P '(0 1 2) '(0 1)) (P '(0 1) '(0 1 2)))]
In particular:@(lb)
@example[(P '(0 1 2) '(0 1))]
@example[(P '(0 1) '(0 1 2))]

@defproc[(G-base (g G?)) (Setof P?)]{
Returns a @nbr[seteq] with a minimal base for @nbr[g].
@(nbsl "G" "G")s of order greater than 2 always have more than one minimal base.
@nbr[G-base] returns one of them only. See @nbr[G-bases].} Example:

@interaction[
(require racket "R.rkt")
(random-seed 0)
(define g (G '(4 5) '(0 1) '(2 3)))
(define g-base (G-base g))
(code:comment #,(list
                 "The returned base not necessarily is the "
                 (elemref "simplest base" "simplest one") ":"))
g-base
(code:comment "Nevertheless it is a correct base:")
(eq? (apply G (set->list g-base)) g)]

@elemtag["proof"]{The symmetric groups S@↓{0}, S@↓{1} and S@↓{2} have minimal bases of one element.
Every symmetric group S@↓{m} with m≥3
has at least one minimal base of two elements, @nb{for example:}}

@interaction[
(require racket "R.rkt")
(G-base (G-symmetric 0))
(G-base (G-symmetric 1))
(G-base (G-symmetric 2))
(for/and ((m (in-range 3 8)))
 (define m-1 (sub1 m))
 (define Sm (G-symmetric m))
 (and (= (set-count (G-base Sm)) 2)
  (code:comment "As an example take base {(0 m-1), (0 .. m-1)},")
  (code:comment "where (0 .. m-1) is the list of natural numbers")
  (code:comment "from 0 up to but not including m-1.")
  (eq? Sm (G (list 0 m-1) (range 0 m-1)))))]

The following example is not a proof,
but shows how to prove the above @nber["proof" "above statement"].

@interaction[
(require racket "R.rkt")
(code:comment "")
(unless
 (for/and ((m (in-range 2 8)))
  (printf " ~nm = ~s~n" m)
  (define m-1 (sub1 m))
  (define transposition (P (list 0 m-1)))
  (define cycle (P (range 0 m-1)))
  (define inversed-cycle (P-inverse cycle))
  (define base
   (for/fold
    ((transposition transposition)
     (base (list transposition))
     #:result base) ((k (in-range m-1)))
    (printf "~s~n" transposition)
    (define new-transposition (P cycle transposition inversed-cycle))
    (values new-transposition (cons new-transposition base))))
  (eq? (apply G base) (G-symmetric m)))
 (error 'example "failed!"))]

Obviously, for m>1 the set of @nbrl[C-transpositions]{transpositions}
@nb{{(k m@(minus)1): 0 ≤ k < m@(minus)1}}
forms a base for @nbr[(G-symmetric m)] (but not minimal for m>3).

@defproc[(G-bases (g G?)) (listof (Setof P?))]{
Returns a list of all minimal bases of @nbr[g].} Examples:

@interaction[
(require"R.rkt" racket)
(define (G-order+bases g)
 (define bases (G-bases g))
 (values
  (format "order: ~s" (G-order g))
  (format "nr of bases ~s" (length bases))
  bases))
(code:comment " ")
(G-order+bases (G))
(code:comment " ")
(G-order+bases (G '(0 1)))
(code:comment " ")
(G-order+bases (G '(0 1 2)))
(code:comment " ")
(G-order+bases (G '(0 1) '(2 3)))
(code:comment " ")
(G-order+bases (G '(0 1) '(0 1 2)))
(code:comment " ")
(G-order+bases (G '((0 1 2 3) (4 5 6 7)) '((0 4 2 6) (1 7 3 5))))
(code:comment " ")
(define g (G '(0 1) '(0 1 2)))
(andmap
 (lambda (base) (eq? (apply G (set->list base)) g))
 (G-bases g))]

@elemtag["simplest base"]{To find one of the simplest bases:}

@interaction[
(require "R.rkt" racket)
(code:comment "")
(define (find-simple-base g)
 (define bases (G-bases g))
 (for/fold
  ((base (car bases))
   (n (string-length (~s (car bases))))
   #:result base)
  ((b (in-list (cdr bases))))
  (define m (string-length (~s b)))
  (if (< m n) (values b m) (values base n))))
(code:comment "")
(find-simple-base (G '(0 1) '((0 1) (2 3)) '((2 3) (4 5))))
(find-simple-base (G '(0 1) '(0 1 2)))
(find-simple-base (G-symmetric 4))
(find-simple-base (G-symmetric 5))]

@defproc[(G-order (g G?)) N+?]{
Returns the order of @nbr[g], id est, its number of elements.

@note{Do not confuse the order of a G with the order of a
@nbsl["P" "P"] (See @nbr[P-order]).
The order of every @nbsl["P" "P"] of a G is a divisor of the order of that G.
This is a consequence of the more general theorem of group theory that
the order of an element of a finite group always is a divisor of the order of that group.
This theorem holds for all finite groups, not only for Gs.}}

@defproc[(G-subg? (g0 G?) (g1 G?)) boolean?]{
@nbr[#t] if @nbr[g0] is a subset of @nbr[g1].
@red{Warning}: procedure @nbr[G-subg?] can be confused by a @nbsl["Cleanup" "cleanup"]:}

@interaction[
(require racket "R.rkt")
(define g0a (G '(0 1)))
(define g1  (G '(0 1) '(0 2)))
(code:line (G-subg?  g0a g1)  (code:comment #,(green "ok")))
(code:line (R-clear-hashes)   (code:comment #,(red "caution")))
(code:line (G-subg?  g0a g1)  (code:comment #,(green "ok")))
(define g0b (G '(0 1)))
(code:line (G-equal? g0a g0b) (code:comment #,(green "ok")))
(code:line (  equal? g0a g0b) (code:comment #,(red "alas")))
(code:line ( G-subg? g0b g1)  (code:comment #,(red "alas")))]

@defproc[(G-proper-subg? (g0 G?) (g1 G?)) boolean?]{
@nbr[g0] is a proper subgroup of @nbr[g1]
if and only if it is a @nbr[G-subg?] of @nbr[g1]
but not the @nbr[G-identity] and not the same as @nbr[g1].
@red{Warning}: procedure @nbr[G-proper-subg?]
can be confused by a @nbsl["Cleanup" "cleanup"].}

@defproc[(G-even-subg (g G?)) G?]{
Returns the G representing the subgroup of all even Ps of @nbr[g].
Same as:
@inset{@nbr[(list->G (filter P-even? (G->list g)))]}
Example:}

@interaction[
(require "R.rkt")
(define g (G '(0 1) '(0 1 2)))
(define h (G-even-subg g))
g
h
(code:line (for/and ((p (in-G g))) (P-even? p)) (code:comment #,(red "False.")))
(code:line (for/and ((p (in-G h))) (P-even? p)) (code:comment #,(green "True.")))]

@defproc[(G-subgroups (g G?)) (listof G?)]{
Returns a list of all subgroups of @nbr[g]. Example:

@interaction[
(require racket "R.rkt")
(define g (G '(0 1 2) '(0 1)))
(code:comment #,(list "Print subgroups in " (nbsl "C" "C-notation.")))
(define (proper?    subg) (if (   G-proper-subg? subg g) 'yes 'no))
(define (invariant? subg) (if (G-invariant-subg? subg g) 'yes 'no))
(define line
 "─────────────────────────────────────────────────────────────~n")
(begin
 (printf line)
 (printf "Proper? Invariant? Order Subgroup (in C-notation)~n")
 (printf line)
 (for
  ((subg
    (in-list
     (sort (G-subgroups g)
      (lambda (x y) (< (G-order x) (G-order y)))))))
  (printf "~a ~a  ~a"
   (~a #:min-width 7 #:align 'center (proper?    subg))
   (~a #:min-width 9 #:align 'center (invariant? subg))
   (~a #:min-width 5 #:align 'center (G-order    subg)))
  (for ((p (in-G subg))) (printf " ~s" (P->C p)))
  (newline))
 (printf line))]

@note{The order of a subgroup always is a divisor of the order of the group it is part of.}}

@defproc[(G-class (p P?) (g G?)) (Setof P?)]{
Returns the conjugation class of @nbr[g] containing @nbr[p].@(lb)
If @nbr[p]∉@nbr[g], @nbr[G-class] returns an empty set.

@note{
Two elements a and b of a group @bold{X} are conjugates of each other if and only if:
@nb{∃c@(∈)@bold{X}: ac = cb}.
This is an equivalence relation, which defines conjugation classes in @bold{X}.
Two elements belong to the same class if and only if they are conjugates of each other.
All elements of a conjugation class of a finite group
have the same order and the same normalized cycle structure.
The number of elements in a conjugation class of a finite group
always is a divisor of the order of the group.
If element x commutes with all elements of @bold{X} its class consists of x only.
Reversely, if the class of element x consists of x only, it commutes with all elements.
In an abelean group every class consists of one element.
The identity always is lonesome in its class;
it is a conjugate of itself only.}}

Examples:

@interaction[
(require racket "R.rkt")
(define g (G '(0 1) '(0 2)))
(G-class P-identity g)
(G-class (P '(0 1)) g)
(G-class (P '(0 1 2)) g)
(code:comment "Empty set if p∉g:")
(G-class (P '(0 1)) (G '(0 1 2)))]

@defproc[(G-classes (g G?)) (listof (Setof P?))]{
Returns a list of all conjugation classes of @nbr[g]. Example:

@interaction[
(require "R.rkt" racket)
(define (print-G-classes g)
 (for ((class (in-list (G-classes g))) (n (in-naturals 1)))
  (printf "Class ~s: " n)
  (for ((p (in-set class))) (printf "~s " (P->C p)))
  (newline)))
(code:comment "All elements of a conjugation class")
(code:comment "have the same normalized cycle structure:")
(print-G-classes (G '(0 1) '(0 2)))
(code:comment "There may be more than one class with.")
(code:comment "the same normalized cycle structure.")
(code:comment "Below the two classes:")
(code:comment "#<seteq: (P '((0 1) (2 3))) (P '((0 3) (1 2)))> and")
(code:comment "#<seteq: (P '((0 2) (1 3)))>")
(print-G-classes (G '(1 3) '(0 1 2 3)))
(print-G-classes (G '((0 1 2 3) (4 5 6 7)) '((0 4 2 6) (1 7 3 5))))
(code:comment "For a symmetric group two elements belong to the same conjugation")
(code:comment "class if and only if they have the same normalized cycle structure:")
(print-G-classes (G-symmetric 4))]}

@defproc[(G-invariant-subg? (g0 G?) (g1 G?)) boolean?]{
@nbr[g0] is an invariant subgroup of @nbr[g1] if it is a subgroup of @nbr[g1] and
@nb{∀p@(∈)@nbr[g1]: {pq: q@(∈)@nbr[g0]} = {qp: q@(∈)@nbr[g0]}}.
The two sets (indicated by curly braces) are called `cosets'.

@note{
Another way to state that @nbr[g0] is an invariant subgroup of @nbr[g1] is
that @nbr[g0] is a subgroup consisting of
the conjunction of complete conjugation classes of @nbr[g1].
See @nbr[G-classes].}}
Examples:

@color-example[red   (G-invariant-subg? (G '(0 1  )) (G '(0 1) '(0 2)))]
@color-example[green (G-invariant-subg? (G '(0 1 2)) (G '(0 1) '(0 2)))]

The subset of all even elements of a G is an invariant subgroup. For example:

@interaction[
(require racket "R.rkt")
(define g (G-symmetric 4))
(define h (G-even-subg g))
(G-order g)
(G-order h)
(G-invariant-subg? h g)]

@defproc[(G-isomorphism (g0 G?) (g1 G?) (name0 symbol? 'no-name) (name1 symbol? 'no-name))
         (or/c #f (cons/c (-> P? P?) (-> P? P?)))]{
If @nbr[g0] and @nbr[g1] are isomorphic,
a pair of two isomorphisms is returned,
the car mapping the @nbsl["P" "P"]s of @nbr[g0] onto those of @nbr[g1]
the cdr being the inverse of the car.
The two iso@(-?)mor@(-?)phisms are procedures and @nbr[name0] and @nbr[name1] their names.
If @nbr[g0] and @nbr[g1] are not iso@(-?)mor@(-?)phic, @nbr[#f] is returned.
Two iso@(-?)mor@(-?)phic Gs may have more than one iso@(-?)mor@(-?)phism.
Procedure @nbr[G-isomorphism] returns one only plus its inverse.

@note{@elemtag["iso"]{Two groups @bold{X} and @bold{Y} are isomorphic to each other
if and only if there is a bijection @nb{ξ: @bold{X} ↔ @bold{Y}} such that:
@nb{∀p,q@(∈)@bold{X}: ξ(pq) = ξ(p)ξ(q).}
Because ξ is a bijection, we also have:@(↑ (hspace 1))
@nb{∀a,b@(∈)@bold{Y}: ξ@(expt-1)(ab) = ξ@(expt-1)(a)ξ@(expt-1)(b).}
Isomorphism is an
@nbhl["https://en.wikipedia.org/wiki/Equivalence_relation" "equivalence relation."]}}} Examples:

@interaction[
(require racket "R.rkt")
(code:comment "Abelean group of 4 elements, called the `four group' or `V'.")
(code:comment "Every element of V is its own inverse.")
(define V (G '(0 1) '(2 3)))
(G-order V)
(G-abelean? V)
(for/and ((p (in-G V))) (eq? (P-inverse p) p))
(code:comment "There are two isomorphically distinct groups of order 4.")
(code:comment "An example of the other one is:")
(define C4 (G '(0 1 2 3)))
(G-order C4)
(G-abelean? C4)
(code:comment "C4 is not isomorphic to V")
(code:line (G-isomorphism V C4) (code:comment #,(red "false")))
(code:comment "In particular (P '(0 1 2 3)) is not its own inverse:")
(code:line (let ((p (P '(0 1 2 3)))) (eq? (P-inverse p) p)) (code:comment #,(red "false")))]

@interaction[
(require racket "R.rkt")
(define g0 (G '(0 1) '(2 3)))
(define g1 (G '((1 2) (7 8)) '((5 6) (3 4))))
(define iso+inverse (G-isomorphism g0 g1 'p0->p1 'p1->p0))
(define p0->p1 (car iso+inverse))
(define p1->p0 (cdr iso+inverse))
(eq? (list->G (map p0->p1 (G->list g0))) g1)
(eq? (list->G (map p1->p0 (G->list g1))) g0)
(code:comment "If the two Gs are not isomorphic, G-isomorphism returns #f.")
(code:line (G-isomorphism (G '(0 1) '(2 3)) (G '(0 1 2 3))) (code:comment #,(red "false")))
(code:comment "An error is reported if the argument")
(code:comment "is not in the domain of the isomorphism.")
(code:line (p1->p0 (P '(0 1))) (code:comment #,(red "error")))]

@red{Warning}: after @nbsl["Cleanup" "cleaning up"]
isomorphisms made before do not recognize newly constructed @nbsl["P" "P"]s:

@interaction[
(require "R.rkt" racket)
(define iso
 (G-isomorphism
  (G '(0 1 2))
  (G '(1 2 3))
  '012->123
  '123->012))
(define p (P '(0 1 2)))
((car iso) p)
(code:line (R-clear-hashes) (code:comment #,(red "Caution")))
((car iso) p)
(code:comment "but because of the cleanup the following raises an exception:")
((car iso) (P '(0 1 2)))
(code:comment "because after cleanup:")
(code:line (equal? p (P '(0 1 2))) (code:comment #,(list (red "alas"))))
(code:comment "although:")
(code:line (P-equal? p (P '(0 1 2))) (code:comment #,(green "ok")))]

@defproc[(G->list (g G?)) (listof P?)]{
Returns a sorted list of all elements of @nbr[g] using @nbr[P-sort].}

@defproc[(list->G (p-list (listof P?))) G?]{
If the @nbsl["P" "Ps"] of the argument form a group
the corresponding G is returned, else an exception is raised.
Duplicate arguments do no harm.
Examples:}

@interaction[
(require "R.rkt")
(list->G (list P-identity (P '(0 1 2)) (P '(0 2 1))))
(code:comment "duplicates do no harm:")
(list->G (list P-identity P-identity (P '(0 1)) (P '(0 1))))
(code:comment "Error when the list does not form a group:")
(code:comment #,(list "In the following example " @nbr[(P '((0 1) (2 3)))] " is missing."))
(list->G (list P-identity (P '(0 1)) (P '(2 3))))]

@section[#:tag "Cleanup"]{Cleanup}

@defproc*[
 (((R-hashes-count) N?)
  ((R-clear-hashes) void?))]{
Modules @nbhl["P.rkt" "P.rkt"] and @nbhl["G.rkt" "G.rkt"]
use hashes in order to avoid repeated identical computations
and to guarantee that
@nbsl["P" "P"]s and @nbsl["G" "G"]s that represent the same @nber["R" "R"]s and
groups of @nber["R" "R"]s are the same in the sense of @nbr[eq?].
The procedures allow inspection of the total number of keys in the hashes
and to clear the hashes.
However, the @nbr[P-identity] and the @nbr[G-identity] are not removed.
@red{Warning}: after clearing the hashes,
newly constructed @nbsl["P" "P"]s and @nbsl["G" "G"]s
no longer will be the same (not even in the sense of @nbr[equal?]) as equivalent
@nbsl["P" "P"]s and @nbsl["G" "G"]s
that were constructed before cleaning up.
@nbrl[G-isomorphism "Isomorphisms"]
will not recognize newly constructed @nbsl["P" "P"]s.
Therefore @nbr[R-clear-hashes] should not be used preceding code that refers to
@nbsl["P" "P"]s or @nbsl["G" "G"]s made before cleanup.
Procedures @nbr[P-equal?], @nbr[G-equal?], @nbr[P<?] and @nbr[P-sort]
remain comparing correctly after cleanup.

See section @nbsr["Distinct-instances"] too.}

@deftogether[
(@defproc[#:kind "equivalence relation" (P-equal? (p0 P?) (p1 P?)) boolean?]
 @defproc[#:kind "equivalence relation" (G-equal? (g0 G?) (g1 G?)) boolean?])]{Example:}

@interaction[
(require "R.rkt")
(define p (P '(0 1 2)))
(define g (G '(0 1 2) '(0 1)))
(eq? p (P '(1 2 0)))
(eq? g (G '(0 1) '(0 2)))
(R-clear-hashes)
(code:line (equal? p (P '(0 1 2))) (code:comment #,(red "alas:")))
(code:line (equal? g (G '(0 1 2) '(0 1))) (code:comment #,(red "alas:")))
(code:line (P-equal? p (P '(2 0 1))) (code:comment #,(green "ok")))
(code:line (G-equal? g (G '(0 1) '(1 2))) (code:comment #,(green "ok")))]

@section[#:tag "Distinct-instances"]{Distinct instances of @nbhl["R.rkt" "R.rkt"]}
Two distinct instances of module @nbhl["R.rkt" "R.rkt"]
do not recognize each others @nbsl["P" "Ps"] or @nbsl["G" "Gs"],
not even their @nbrl[P-identity "P-identities"] and @nbrl[G-identity "G-identities"]:

@interaction[
(require racket "R.rkt")
(define other-eval
 (let ((namespace (make-base-namespace)))
  (parameterize ((current-namespace namespace))
   (namespace-require 'racket)
   (namespace-require '"R.rkt"))
  (lambda (expr) (eval expr namespace))))
(define other-P-identity  (other-eval 'P-identity))
(define other-G-identity  (other-eval 'G-identity))
(define other-P-identity? (other-eval 'P-identity?))
(define other-G-identity? (other-eval 'G-identity?))
(code:line (other-P-identity? other-P-identity) (code:comment #,(green "ok")))
(code:line (other-G-identity? other-G-identity) (code:comment #,(green "ok")))
(code:line (equal? P-identity other-P-identity) (code:comment #,(red "alas:")))
(code:line (equal? G-identity other-G-identity) (code:comment #,(red "alas:")))
(code:line (P-identity? other-P-identity) (code:comment #,(red "alas:")))
(code:line (G-identity? other-G-identity) (code:comment #,(red "alas:")))
(code:line (other-P-identity? P-identity) (code:comment #,(red "alas:")))
(code:line (other-G-identity? G-identity) (code:comment #,(red "alas:")))
(code:comment "")
(code:comment #,(list "Even " (nbr P-equal?) " and " (nbr G-equal?) " go wrong:"))
(code:comment "(with an error message that may be obscure, although it does")
(code:comment " indicate the mixing of different structures of the same name)")
(P-equal? P-identity other-P-identity)
(G-equal? G-identity other-G-identity)]

@section[#:tag "H"]{Hash representation}

All objects described in this section are defined in
module @nbhl["H.rkt" "H.rkt"].
The H-representation is used internally for operations like application,
@nber["composition" "composition"] and inversion.
@red{Advice}: don't use the H-representation explicitly.
Use the @nbsl["P" "P-representation"].
It represents @nber["R" "Rs"] by means of functions
and avoids multiple copies in memory of Hs, @nbsl["C" "Cs"] and
@nbsl["P" "Ps"] representing the same @nber["R" "R"]:
@nbsl["P" "Ps"] representing the same @nber["R" "R"]
are the same in the sense of @nbr[eq?].
 
@note{@elemtag["inversion"]{
In this docu@(-?)ment the word `@italic{inversion}' applies to bijections.
The same word often is used for a special kind of symmetry-operation:
reflection in the origin of a linear space.
In order to avoid confusion,
for the latter the word `@italic{inversion-symmetry}' will be used.}}

@elemtag["H-definition" ""] An H is an immutable @nbr[hasheqv] representing an @nber["R" "R"].
Its keys and values are @seclink["N"]{natural numbers}.
The represented @nber["R" "R"] maps each key onto its value
and every @seclink["N"]{natural number} not present as a key onto itself.
In order to represent a bijection, every key must appear as a value and every value as a key.
A key is not supposed to be mapped onto itself.
If there is such key=value pair, the hash is called a pseudo H.

@deftogether[
 (@defproc[#:kind "predicate" (H? (x any/c)) boolean?]
  @defproc[#:kind "predicate" (pseudo-H? (x any/c)) boolean?])]{
See the @nber["H-definition" "definitions above"].}

@defproc[(H-normalize (h pseudo-H?)) H?]{
Removes key/value pairs with key=value.}

@defproc[(H-apply (h pseudo-H?) (k N?)) N?]{
Returns the image of @nbr[k] under the @nber["R" "R"] represented by @nbr[h].@(lb)
Same as: @nbr[(hash-ref h k k)].}

@defproc[(H-compose (h pseudo-H?) ...) H?]{
Returns an H representing the @nber["R" "R"] formed by @nber["composition" "composition"]
of the @nber["R" "R"]s represented by the arguments.
When called without argument @nbr[H-compose] returns the @nbr[H-identity].
When called with one argument, the normalized from of the argument is returned.}

@defproc[(H-inverse (h pseudo-H?)) H?]{
Returns the H representing the inverse of the @nber["R" "R"] represented by @nbr[h].
Same as @nbr[(for/hasheqv (((k v) (in-hash (H-normalize h)))) (values v k))]}

@defidform[#:kind "constant" H-identity]{
Empty @nbsl["H" "hash"] representing the @nber["id"]{identity of @bold{R}}.}

@defproc[#:kind "predicate" (H-identity? (x any/c)) boolean?]{
Same as @nbr[(and (pseudo-H? x) (equal? (H-normalize x) H-identity))]}

@defproc[(H-restriction (h pseudo-H?)) N?]{
Returns the @nber["R" "restriction"] of the @nber["R" "R"] represented by @nbr[h].}

@section{Elaborated examples}
@subsection{Symmetries of a cube}

Number the vertices of a cube as shown in the following figure:

@nested[#:style 'inset (image "cube.gif")]

All symmetries of the cube can be found with a
@nbrl[G-bases "minimal base"] of two elements.
Below a base is used consisting of a
rotation about 90° around the vertical axis through the center of the cube,
in particular @nbr[(P '((0 1 2 3) (4 5 6 7)))], and
reflection in the diagonal plane containing the vertices 2, 3, 4 and 5,
id est, @nbr[(P '((0 7) (1 6)))].

@interaction[
(require racket "R.rkt")
(define rotation (P '((0 1 2 3) (4 5 6 7))))
(define reflection (P '((0 7) (1 6))))
(define cube-symmetries (G rotation reflection))
(code:comment "")
(code:comment "The following table associates one member")
(code:comment #,(list "of each " (nbrl G-class "conjugation class") " with a name"))
(code:comment "later to be associated with the whole")
(code:comment "conjugation class of this member.")
(code:comment "")
(define classocs
 (list
  (cons (P '((0 1 2 3) (4 5 6 7)))
   "Rotation 90° or 270°, axis // to an edge.")
  (cons (P '((0 2) (1 3) (4 6) (5 7)))
   "Rotation 180°, axis // to an edge.")
  (cons (P '((0 1) (2 3) (4 5) (6 7)))
   "Reflection, plane // to a side.")
  (cons (P '((0 7) (1 6)))
   "Reflection, diagonal plane.")
  (cons (P '((0 2 5) (3 6 4)))
   "Rotation 120° or 240°, axis a diagonal.")
  (cons (P '((0 7 2 5) (1 4 3 6)))
   "Rotation 90° or 270°, axis // to an edge, * inversion-symmetry.")
  (cons (P '((0 1) (2 4) (3 5) (6 7)))
   (string-append
    "Rotation 90° or 270° * rotation 180°,\n"
    "axes // to an edge and perpendicular to each other."))
  (cons (P '((1 7) (0 4 5 6 2 3)))
   "Rotation 120° or 240°, axis a diagonal, * inversion-symmetry.")
  (cons P-identity
   "Identity")
  (cons (P '((0 6) (1 7) (2 4) (3 5)))
   "Inversion-symmetry.")))
(code:comment "")
(define class-names (map cdr classocs))
(define (get-class classoc) (G-class (car classoc) cube-symmetries))
(define conj-classes (map get-class classocs))
(code:comment "")
(code:comment "Check that all classocs refer to distinct conjugation classes")
(code:comment "and that all conjugation classes are present.")
(code:comment "")
(unless (set=? conj-classes (G-classes cube-symmetries))
 (error 'cube-symmetries "incorrect classocs table"))
(code:comment "")
(code:comment "The following table maps each conjugation class to its name.")
(code:comment "")
(define conj-name-table
 (make-hash (map cons conj-classes class-names)))
(code:comment "")
(define (get-class-name conj-class)
 (hash-ref conj-name-table conj-class))
(code:comment "")
(define S8 (G-symmetric 8))
(code:comment "")
(code:comment "Procedure print-group-info prints some information about group g.")
(code:comment "classes must be a list of all conjugation classes of g.")
(code:comment "")
(define (print-group-info g classes name print-classes?)
 (define conj-classes (sort classes conj-class<?))
 (define g-order (G-order g))
 (define in-g (in-G g))
 (printf " ~nInfo about group: ~a~n ~n" name)
 (printf "Order of the group: ~s~n" g-order)
 (printf "Number of conjugation classes: ~s~n" (length conj-classes))
 (printf
  "Order of each element divisor of the order of the group? ~s~n"
  (for/and ((p in-g)) (divisor? (P-order p) g-order)))
 (printf "Proper subgroup of S8? ~s~n"
  (G-proper-subg? g S8))
 (printf "All elements even? ~s~n"
  (for/and ((p in-g)) (P-even? p)))
 (printf "Size of each conjugation class divisor ")
 (printf "of order of the group? ~s~n"
  (for/and ((conj-class (in-list conj-classes)))
   (divisor? (set-count conj-class) g-order)))
 (when print-classes?
  (printf " ~nThe conjugation classes are:~n")
  (for ((conj-class (in-list conj-classes)))
   (printf " ~n~a~n" (get-class-name conj-class))
   (printf "Order: ~s, collection-size: ~s~n"
    (P-order (set-first conj-class))
    (set-count conj-class))
   (for ((p (in-list (P-sort (set->list conj-class)))))
    (printf "~s~n" (P->C p)))))
 (printf " ~n"))
(code:comment "")
(define (conj-class<? x y)
 (and (not (eq? x y))
  (or
   (eq? (set-first x) P-identity)
   (< (set-count x) (set-count y))
   (and
    (= (set-count x) (set-count y))
    (< (P-order (set-first x)) (P-order (set-first y)))))))
(code:comment "")
(define (divisor? divisor multiple)
 (zero? (modulo multiple divisor)))
(code:comment "")
(print-group-info cube-symmetries conj-classes "cube-symmetries" #t)
(code:comment "Subgroup consisting of rotations only:")
(code:comment "")
(define other-rotation '((0 1 5 4) (3 2 6 7)))
(define rotations-only (G rotation other-rotation))
(code:comment "rotation and other-rotation are rotations about 90°")
(code:comment "with intersecting axes perpendicular to each other.") 
(define rotation-classes (G-classes rotations-only))
(print-group-info rotations-only rotation-classes "rotations-only" #f)
(code:comment "rotations-only is an invariant subgroup of all cube-symmetries.")
(G-invariant-subg? rotations-only cube-symmetries)
(code:comment "Each conjugation class of the group of rotations-only")
(code:comment "also is a conjugation class of the group of all cube-symmetries")
(proper-subset? rotation-classes conj-classes)]

There are ten conjugation classes, of which five are conjugation classes
of subgroup @element['tt "rotations-only"] too.
Elements belonging to the same class have the same normalized cycle structure.
The @nbr[P-identity] always is the only member of its class.
The inversion-symmetry @nbr[(P '((0 6) (1 7) (2 4) (3 5)))],
which does not occur in subgroup @element['tt "rotations-only"], is lonesome too.
This implies that it commutes with all elements.
It maps each vertex to the one in opposit position with respect to the center of the cube.
The inversion-symmetry, rotations about 180° and reflections in the planes
containing the center of the cube and parallel to a side of the cube
have the same normalized cycle structure.
Possibly you did not expect three-fold rotation axes as symmetries of a cube, but they are there.
Even subgroup @element['tt "rotations-only"] has threefold symmetries.
In particular, @nber["composition" "composition"] of two rotations about 90° with intersecting
axes orthogonal to each other produces a rotation about 120°, for example:

@example/n[(P-compose (P '((0 1 2 3) (4 5 6 7))) (P '((0 3 7 4) (1 2 6 5))))]

This is a rotation about 120° around axis 0-6.
Composition of this rotation with the inversion-symmetry,
which is not part of subgroup @element['tt "rotations-only"], produces:

@example/n[(P-compose (P '((1 3 4) (2 7 5))) (P '((0 6) (1 7) (2 4) (3 5))))]

This is a symmetry of order 6.
Let's check that the inversion-symmetry commutes with all symmetries of the cube:

@interaction[
(require racket "R.rkt")
(define rotation (P '((0 1 2 3) (4 5 6 7))))
(define reflection (P '((0 7) (1 6))))
(define cube-symmetries (G rotation reflection))
(define inversion-symmetry (P '((0 6) (1 7) (2 4) (3 5))))
(for/and ((p (in-G cube-symmetries)))
 (eq?
  (P inversion-symmetry p)
  (P p inversion-symmetry)))]

There are @nb{9×24 = 216} distinct minimal bases for the symmetries of the cube.
They can be grouped in 9 collections of symmetrically equivalent minimal bases,
each collection containing 24 bases.
Two minimal bases @nb{{a ...}} and @nb{{b ...}} are symmetrically equivalent
if the group contains a symmetry x such that @nb{{x@↑{@(minus)1}ax ...} = {b ...}}.
(This is an equality of two sets:
the order in which the elements appear between the curly brackets is irrelevant.)
It is not difficult to prove that this indeed is an equivalence relation of the minimal bases.
Symmetrically equivalent minimal bases have the same normalized cycle structure.
The number of collections of symmetrically equivalent minimal bases of the group of
@tt{cube-symmetries} is one less than the number of conjugation classes.
This is no coincidence, because both the identity and the inversion-symmetry
leave every minimal base as it is.

@elemtag["seq" ""]
The number of minimal bases in a collection of symmetrically equivalent
minimal bases of group @tt{cube-symmetries} equals the order of group @tt{rotations-only}.
Indeed, for every pair of symmetrically equivalent minimal bases
there is a @tt{rotations-only}-symmetry showing the equivalence.
In addition, given a minimal base, every @tt{rotations-only}-symmetry
produces a dictinct symmetrically equivalent minimal base.
The following example shows the details:

@interaction[
(require racket "R.rkt")
(define rotation (P '((0 1 2 3) (4 5 6 7))))
(define reflection (P '((0 7) (1 6))))
(define cube-symmetries (G rotation reflection))
(define bases (G-bases cube-symmetries))
(code:comment "")
(define ((make-base-eqv g) a b)
 (for/or ((p (in-G g)))
  (equal? a
   (for/seteq ((c (in-set b))) (P (P-inverse p) c p)))))
(code:comment "")
(define (eqv-classes lst eq) (group-by values lst eq))
(code:comment "")
(define base-collections
 (eqv-classes bases (make-base-eqv cube-symmetries)))
(code:comment "")
(define collection-size (/ (length bases) (length base-collections)))
(code:comment "")
(define (pad3 datum) (~s #:align 'right #:min-width 3 datum))
(begin
 (printf " ~n")
 (printf "nr of bases                     ~a~n"
  (pad3 (length bases)))
 (printf "nr of base-collections          ~a~n"
  (pad3 (length base-collections)))
 (printf "all base-collections same size? ~a~n"
  (pad3
   (apply = collection-size (map length base-collections))))
 (printf "size of each base-collection    ~a~n"
  (pad3 collection-size)))
(code:comment "")
(code:comment #,(list "Print the base classes in " (nbsl "C" "C-notation") ", one base per line."))
(code:comment "")
(for ((base-collection (in-list base-collections)) (i (in-naturals)))
 (printf " ~nbase-collection ~s~n" (add1 i))
 (for ((base (in-list base-collection))
       (n (in-naturals (add1 (* collection-size i)))))
  (apply printf "~a ~s and ~s~n"
   (~s n #:min-width 3 #:align 'right)
   (map P->C (P-sort (set->list base))))))
(code:comment "")
(code:comment #,(list "Let's check the " @nber["seq" "above statement"]
                      " about the size"))
(code:comment "of each collection of symmetrically equivalent bases.")
(code:comment "")
(define other-rotation '((0 1 5 4) (3 2 6 7)))
(define rotations-only (G rotation other-rotation))
(define order-rotations-only (G-order rotations-only))
(for/and ((b (in-list bases)))
 (define n
  (set-count
   (for/set ((r (in-G rotations-only)))
    (for/set ((b (in-set b))) (P (P-inverse r) b r)))))
 (= n order-rotations-only))
(code:comment "")
(code:comment "Using the rotations only we find the same collections of bases:")
(code:comment "")
(equal?
 (apply set
  (map set base-collections))
 (apply set
  (map set
   (eqv-classes bases (make-base-eqv rotations-only)))))
(code:comment "")
(code:comment "This is consistent with the fact that adding the inversion-symmetry to")
(code:comment "a base of group rotations-only yields the group of all cube-symmetries.")
(code:comment "")
(define inversion-symmetry (P '((0 6) (1 7) (2 4) (3 5))))
(eq? cube-symmetries (G rotation other-rotation inversion-symmetry))
(code:comment "")
(code:comment "In fact adding an arbitrary rotation-reflection will do.")
(code:comment "A rotation-reflection is a reflection or")
(code:comment "the composition of a rotation with a reflection.")
(code:comment "The inversion-symmetry is a rotation-reflection too,")
(code:comment "for example: reflection in the horizontal plane")
(code:comment "followed by 180° rotation around the vertical axis,")
(code:comment "both containing the center of the cube.")
(code:comment "")
(eq? (P-compose '((0 2) (1 3) (4 6) (5 7))  (code:comment "rotation 180°")
                '((0 4) (1 5) (2 6) (3 7))) (code:comment "reflection")
     inversion-symmetry)
(code:comment "")
(define rotation-reflections
 (remove* (G->list rotations-only) (G->list cube-symmetries)))
(code:comment "")
(for/and ((p (in-list rotation-reflections)))
 (eq? cube-symmetries (G rotation other-rotation p)))]

@subsection{The quaternion group}

@(define Q-comment
  (list
   "Q is (a group isomorphic to) the "
   (nbhl "https://en.wikipedia.org/wiki/Quaternion_group" "quaternion group") "."))

@interaction[
(require "R.rkt" racket)
(define i (P '((0 1 2 3) (4 5 6 7))))
(define j (P '((0 4 2 6) (1 7 3 5))))
(code:comment #,Q-comment)
(define Q (G i j))
(G-order Q)
(for ((p (in-G Q))) (printf "order = ~s, p = ~s~n" (P-order p) p))
(G-classes Q)]

In the quaternion group, make the following identifications:

@(let ()
  (define | i| (P '((0 1 2 3) (4 5 6 7))))
  (define | j| (P '((0 4 2 6) (1 7 3 5))))
  (define | k| (P | i| | j|))
  (define | 1| P-identity)
  (define |-1| (P | i| | i|))
  (define |-i| (P |-1| | i|))
  (define |-j| (P |-1| | j|))
  (define |-k| (P |-1| | k|))
  (define Ps    (list | 1| |-1| | i| |-i| | j| |-j| | k| |-k|))
  (define names (list " 1" "-1" " i" "-i" " j" "-j" " k" "-k"))
  (define P->name-table (make-hash (map cons Ps names)))
  (define (P->name p) (hash-ref P->name-table p))
  (define op (open-output-string))
  (parameterize ((current-output-port op))
   (for ((p (in-list Ps)))
    (for ((q (in-list Ps)))
     (printf "~a " (P->name (P p q))))
    (unless (eq? p |-k|) (newline))))
  (define table (get-output-string op))

@nested{@nested[#:style 'inset]{
Identify @hspace[1]@element['tt "1"]  with @element['tt (~s | 1|)].@(lb)
Identify           @element['tt "-1"] with @element['tt (~s |-1|)].@(lb)
Identify @hspace[1]@element['tt "i"]  with @element['tt (~s | i|)].@(lb)
Identify @hspace[1]@element['tt "j"]  with @element['tt (~s | j|)].@(lb)
Identify @hspace[1]@element['tt "k"]  with @element['tt "(P i j)"].}

We have @element['tt "ii=jj=kk=-1"], @element['tt "ij=k"], @element['tt "jk=i"]
and @element['tt "ki=j"].
With these @nber["composition" "composition"]s
all others are defined as shown in the following table:

@nested[#:style 'inset (verbatim table)]})

@note{This table has been @italic{computed} in module @nbhl["R.scrbl" "R.scrbl"].
It has @italic{not} been typed @italic{manually}.}

Because @element['tt "1"] is the identity, it commutes with all elements.
@element['tt "-1"] commutes with all elements too,
which is verified by the fact that the second row of the table
equals the second column.
Notice that
@nb[@element['tt "ji=(-ii)ji=-i(ij)i=-iki=-ij=-k"]].
Likewise @nb[@element['tt "kj=-i"]] and @nb[@element['tt "ik=-j"]].
The @nbrl[G-classes "conjugation classes"] are:

@nested[#:style 'inset]{@verbatim|{
{1    }
{   -1}
{i, -i}
{j, -j}
{k, -k}}|}

We can verify this as follows:

@interaction[
(require racket "R.rkt")
(define i (P '((0 1 2 3) (4 5 6 7))))
(define j (P '((0 4 2 6) (1 7 3 5))))
(define Q (G i j))
(define |-1| (P i i))
(for/and ((g-class (in-list (G-classes Q))))
 (case (set-count g-class)
  ((1)
   (define x (set-first g-class))
   (or (P-identity? x) (eq? x |-1|)))
  ((2)
   (define-values (p q) (apply values (set->list g-class)))
   (eq? (P |-1| p) q))
  (else #f)))]

In the quaternion group the @nbrl[P-period "period"]
of each element forms an @nbrl[G-invariant-subg? "invariant subgroup"]:

@interaction[
(require racket "R.rkt")
(define i (P '((0 1 2 3) (4 5 6 7))))
(define j (P '((0 4 2 6) (1 7 3 5))))
(define Q (G i j))
(code:comment "(G p) = subgroup consisting of the period of p.")
(for/and ((p (in-G Q))) (G-invariant-subg? (G p) Q))]

@subsection[#:tag "C3v"]{Group C@↓{3v}}

C@↓{3v} is the group of symmetries of an equilateral triangle,
with subscript `3' indicating that it has a three-fold axis of rotation and
subscript `v' indicating it has a vertical plane of reflection containing
the axis of rotation and one of the vertices, in fact three such reflections
and assuming the triangle to be located in a horizontal plane.
Naming the vertices 0, 1 and 2 we can map the symmetries isomorphically onto @nber["R" "Rs"]:

@interaction[
(require racket "R.rkt")
(define C3v (G '(0 1) '(0 1 2)))
(G-print-table C3v)
(code:comment #,(list "C" (↓ "3v") " is isomorphic to S" (↓ "3") ". In this case we even have:"))
(eq? C3v (G-symmetric 3))]

The represented symmetries are:

@elemtag["C3v-table" ""]
@inset{@Tabular[
(("label" (nbsl "C" "C") "symmetry")
 ("0"     @nbr[()]       "the identity")
 ("1"     @nbr[(0 1 2)]  "rotation about 120°")
 ("2"     @nbr[(0 2 1)]  "rotation about 120° in reversed direction")
 ("3"     @nbr[(1 2)]    "reflection in perpendicular from vertex 0")
 ("4"     @nbr[(0 1)]    "reflection in perpendicular from vertex 2")
 ("5"     @nbr[(0 2)]    "reflection in perpendicular from vertex 1"))
#:row-properties '((bottom-border top-border) () () () () () bottom-border)
#:sep (hspace 2)]}

According to @nbhl["https://en.wikipedia.org/wiki/Cayley%27s_theorem" "Cayley's theorem"]
every group of finite order m is isomorphic to
a subgroup of the symmetric group S@↓{m}.
For every group, every row of the table of @nber["composition" "composition"]s
is a distinct @nber["rearrangement" "rearrangement"] of the elements of the group.
Likewise every column is a distinct @nber["rearrangement" "rearrangement"].
Therefore every element of a group @bold{X}
can be associated with one or two permutations of set @bold{X}:

@inset{
∀x@(∈)@bold{X}: (y@(∈)@bold{X}: → xy) is a permutation of set @bold{X} (column of x)@(lb)
∀x@(∈)@bold{X}: (y@(∈)@bold{X}: → yx) is a permutation of set @bold{X} (row of x)}

If the group is abelean, the @nber["rearrangement" "rearrangements"]
in the rows are the same as those in the columns.
Hence, if the group is abelean, every element corresponds to one permutation only,
else some elements correspond to two distinct permutations of @bold{X}.
Because C@↓{3v} is not abelean, the set of @nber["rearrangement" "rearrangements"]
in the rows is not the same as that in the columns:
the table is not invariant under transposition, id est, reflection
in the diagonal from the upper left corner to the lower right corner.
Labeling the elements of C@↓{3v}
as shown in the @nber["C3v-table" "table"] above,
the @nber["rearrangement" "rearrangements"] in columns and those in rows
can be expressed as @nbsl["C" "Cs"].
Both sets of @nbsl["C" "Cs"] form groups isomorphic to C@↓{3v}.
Let's check this:

@(define C3v-comment1 "procedure correspondence computes a list of Ps corresponding to the")

@(define C3v-comment2
(list
 @nber["rearrangement" "rearrangements"]
 " of g in the rows/columns of its composition table."))

@(define C3v-comment3
  @(elemtag "H->P-example" (list
   "Use of "
   @nbr[H->P]
   " is "
   (red "discouraged")
   ", but here it is "
   (green "useful")
   ".")))

@interaction[
(require racket "R.rkt")
(define (pad7-P->C p) (~s #:width 7 (P->C p)))
(define C3v (G '(0 1) '(0 1 2)))
(define in-C3v (in-G C3v))
(code:comment "-------------------------------------------------------------------")
(code:comment "(correspondence g) ->")
(code:comment "(values (hasheq P? N? ... ...) (listof P?) (listof P?))")
(code:comment "g : G?")
(code:comment #,C3v-comment1)
(code:comment #,C3v-comment2)
(define (correspondence g)
 (define in-g (in-G g))
 (code:comment #,(list "h maps the Ps of g onto the " @nbsl["N"]{natural numbers}))
 (code:comment "0 up to but not including the order of g.")
 (define h (for/hasheq ((p in-g) (k (in-naturals))) (values p k)))
 (code:comment #,C3v-comment3)
 (define (correspondence compose-for-row-or-column)
  (for/list ((p in-g))
   (H->P
    (for/hasheqv ((q in-g))
     (values
      (hash-ref h q)
      (hash-ref h (compose-for-row-or-column p q)))))))
 (define rows    (correspondence (lambda (p q) (P p q))))
 (define columns (correspondence (lambda (p q) (P q p))))
 (values h rows columns))
(code:comment "")
(define-values (h rows columns) (correspondence C3v))
(code:comment "-------------------------------------------------------------------")
(code:comment "Let's print map h:")
(code:comment "")
(for ((p in-C3v))
 (printf "~a is mapped onto ~s.~n" (pad7-P->C p) (hash-ref h p)))
(code:comment "")
(code:comment "Using this map, the composition table can be simplified by representing")
(code:comment #,(list "the elements of C" (↓ "3v") " by the natural numbers they are mapped onto."))
(code:comment "")
(for ((p in-C3v))
 (for ((q in-C3v)) (printf " ~s" (hash-ref h (P p q))))
 (newline))
(code:comment "")
(code:comment #,(list "Let's show the correspondence of the elements of C"(↓ "3v")))
(code:comment #,(list "to permutations of the set of C"(↓ "3v")","))
(code:comment #,(list "representing them by the " @nber["C3v-table" "labels shown above"] "."))
(code:comment "")
(for ((p in-C3v) (row (in-list rows)))
 (printf "   row of ~a corresponds to ~s~n"
  (pad7-P->C p) (P->C row)))
(code:comment "")
(for ((p in-C3v) (column (in-list columns)))
 (printf "column of ~a corresponds to ~s~n"
  (pad7-P->C p) (P->C column)))
(code:comment "")
(code:comment "Let's check that we have isomorphic groups here.")
(code:comment "")
(define (G-isomorphic? x y) (and (G-isomorphism x y) #t))
(define row-group    (list->G rows))
(define column-group (list->G columns))
(and
 (G-isomorphic? C3v    row-group)
 (G-isomorphic? C3v column-group))
(code:comment "This implies:")
(G-isomorphic? row-group column-group)]

@subsection[#:tag "C3h"]{Group C@↓{3h}}

Group C@↓{3h} has a three-fold axis of rotation and a plane of reflection
perpendicular to the axis of rotation. The subscript `h' indicates that
with vertical axis of rotation, the plane of reflection is horizontal.
A minimal base of C@↓{3h} consists of one element only.
This implies that C@↓{3h} is circular and abelean.
There are two minimal bases (consisting of inverses of each other)
C@↓{3h} is isomorphic to the group of the natural numbers from 0 up to 6 (excluded),
0 as identity and addition modulo 6 as @nber["composition" "composition"].

@interaction[
(require racket "R.rkt")
(define rotation (P '(0 1 2) '(3 4 5)))
(define reflection (P '(0 3) '(1 4) '(2 5)))
(eq? (P rotation reflection) (P reflection rotation))
(define C3h-base (P rotation reflection))
(define C3h (G C3h-base))
(G-order C3h)
(G-abelean? C3h)
(G-bases C3h)
(define period (P-period C3h-base))
(define h
 (make-immutable-hasheq
  (for/list ((p (in-vector period)) (k (in-naturals)))
   (printf "~s : ~s~n" k p)
   (cons p k))))
(for ((p (in-vector period)))
 (for ((q (in-vector period)))
  (printf "~s " (hash-ref h (P p q))))
 (newline)) 
(define C6 (G (range 6)))
(and (G-isomorphism C3h C6) #t)
(define other-C3h (G '(0 1 2) '(3 4)))
(and (G-isomorphism C3h other-C3h) #t)]

@bold{@larger{@larger{@larger{The end}}}}
@(collect-garbage)
