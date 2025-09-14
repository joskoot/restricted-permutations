#lang scribble/manual
@;----------------------------------------------------------------------------------------------------
@(require
   scribble/core
   scribble/eval
   racket
   "R.rkt"
   (for-label
     "R.rkt"
     racket
     (only-in typed/racket Setof Natural Sequenceof Index))
   (for-syntax racket))

@(define-for-syntax local #f)

@(define-syntax (nbhll stx)
   (syntax-case stx ()
     ((_ x y ...)
      (if local
        #'(nb (hyperlink x y ...))
        #'(nb (hyperlink (string-append "../../" x) y ...))))))

@(require (only-in scribble/racket make-element-id-transformer))
@(define-syntax CLASS
  (make-element-id-transformer
   (lambda _ #'(tt "class"))))

@(define-syntax (Defmodule stx)
   (if local
     #'(defmodule "R.rkt" #:packages ())
     #'(defmodule restricted-permutations/R #:packages ())))

@(define-syntax-rule
   (Interaction x ...)
   (interaction/no-prompt
     #:eval
     (make-base-eval
       #:lang
       '(begin
          (require racket "R.rkt" format/fmt)
          (print-reader-abbreviations #f)
          (print-as-expression #f))) x ...))

@(define-syntax-rule
   (Interaction* x ...)
   (interaction/no-prompt #:eval evaller x ...))

@(define (make-evaller)
   (make-base-eval
     #:pretty-print? #f
     #:lang
     '(begin
        (require racket "R.rkt" format/fmt)
        (print-reader-abbreviations #f)
        (print-as-expression #f))))

@(define evaller (make-evaller))
@(define (reset-Interaction*) (set! evaller (make-evaller)))

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
   "R.rkt"
   format/fmt
   (for-label
     "R.rkt"
     racket
     format/fmt
     (only-in typed/racket Setof Natural Sequenceof Index))
   (for-syntax racket))

@(define lb linebreak)
@(define (↑lb) (list (↑ (hspace 1)) (lb)))
@(define nb nonbreaking)
@; ignore is a syntax such as to prevent arguments to be evaluated.
@(define-syntax-rule (ignore x ...) (void))
@; Below syntaxes are used such as to allow keyword arguments
@; without explicitly mentioning them in the definitions.
@(define-syntax-rule (nbsl x ...) (nb (seclink    x ...)))
@(define-syntax-rule (nbsr x ...) (nb (secref     x ...)))
@(define-syntax-rule (nbhl x ...) (nb (hyperlink  x ...)))
@(define-syntax-rule (nber x ...) (nb (elemref    x ...)))
@(define-syntax-rule (nbrl x ...) (nb (racketlink x ...)))
@(define-syntax-rule (nbr  x ...) (nb (racket     x ...)))

@(define (make-color-style color)
   (define prop:color (color-property color))
   (define color-style (style #f (list prop:color)))
   (lambda (elem) (element 'roman (element color-style elem))))

@(define (make-small-color-style color)
   (define prop:color (color-property color))
   (define color-style (style #f (list prop:color)))
   (lambda (elem) (element 'roman (element (list color-style smaller) elem))))

@(define red   (make-color-style "red"))
@(define green (make-color-style "green"))
@(define black (make-color-style "black"))

@(define example-ns (make-base-namespace))

@(parameterize ((current-namespace example-ns))
   (namespace-require 'racket)
   (namespace-require 'restricted-permutations/R))

@(define-syntax-rule (eval-example expr)
   (begin
     (random-seed 1)
     (nb (element 'tt (begin (random-seed 1) (~s (eval 'expr example-ns)))))))

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
@(define (expt-1) @↑{@(minus)1})
@(define ↑ superscript)
@(define ↓ subscript)

@(define constr-style
   (nbhl "https://docs.racket-lang.org/drracket/output-syntax.html" "constructor style"))

@title[#:version ""]{Restricted Permutations}
@author{Jacob J. A. Koot}

@(Defmodule)

Module @nbhll["R.rkt" "R.rkt"] @nbrl[require]{requires} the following modules
and @nbrl[provide]{provides} all imports@(lb)
with exception of a minor modification related to @nbsl["Cleanup" "cleanup"].
@inset{@Tabular[
 (("Module" "Documentation in section") 
  (@nbhll["N.rkt" "N.rkt"] @(nbsr "N"))
  (@nbhll["C.rkt" "C.rkt"] @(nbsr "C"))
  (@nbhll["P.rkt" "P.rkt"] @(nbsr "P"))
  (@nbhll["H.rkt" "H.rkt"] @(nbsr "H"))
  (@nbhll["G.rkt" "G.rkt"]@(nbsl "G" "Finite groups of restricted permutations")))
 #:sep (hspace 3)
 #:row-properties '(top-border top-border () () () bottom-border)]}

@section{Introduction}
In this document the word `permutation' is used in mathematical sense, id est,@(lb)
such as to mean a bijection of a set onto the same set.

@elemtag["rearrangement" ""]
@note{The word `permutation' often is used for rearrangements.
 For example, two lists like @nb{(1 2 0)} and @nb{(0 1 2)}
 often are called permutations of each other.
 In this document they are called rearrange@(-?)ments of each other,
 the word `permutation' being reserved for bijections of a set onto the same set.
 Rearrangements can represent permutations, though.
 If there is no danger of confusion,
 @nb{a representing} object can be written or talked about
 as though it were the object it represents,
 @nb{but this} is avoided in this document.
 However, no formal distinction will be made between
 @nbsl["N" "exact integer numbers of Racket"]
 and the abstract integer numbers they represent.}

@elemtag["R" ""]
Let @bold{N} be the set of all natural numbers, 0 included.@(lb)
Define a restricted permutation, @nb{say p}, as a permutation of @bold{N}@(lb)
with finite number of non-fixed points, id est, with a restriction as follows:

@inset{@nb{∃m∈@bold{N}: ∀k∈@bold{N}: k≥m ⇒ p(k) = k}}

Let's call the smallest m∈@bold{N} for which this holds,
@nb{@italic{the} restriction} @nb{of p.}
@nb{`R' is shorthand for `restricted permutation'.}
@nb{Let @bold{R} be the set of all Rs.}
@nb{@elemtag["composition"]Define the composition:}

@inset{@nb{p,q∈@bold{R} → pq∈@bold{R}}}

as usual for functions p and q with compatible domain of p and co-domain of q:

@inset{@nb{pq: k∈@bold{N} → p@larger{(}q(k)@larger{)}∈@bold{N}}}

In this document @bold{R} always will be associated with this composition,
thus forming @nb{a @nber["group"]{group}},
in particular a denumerably infinite group.
As required, the composition is associative.
For some groups the composition is commutative.
For @bold{R} it is not,
although it is commutative for many subgroups of @bold{R},
but certainly not for all of them.
For every finite group there is an isomorphic subgroup of @bold{R}.

@note{In fact exactly one such subgroup
 consisting of the @nber["id"]{identity of @bold{R}} only
 if the order @nb{(= cardinality)} of the group is 1 and
 an infinite number of them if the order is greater than 1.}

@note{In this document @bold{R} is the group of @nber["R"]{restricted permutations}@(lb)
 and has nothing to do with the set of real numbers.}

@elemtag["group"]
@note{The present document is not an introduction to group theory.
 It frequently refers to mathematical concepts without their definitions
 and mentions theorems without their proofs.
 @nb{For a simple} introduction see chapter 1 of
 @hyperlink[
 "../../Hamermesh-GroupTheory.pdf"
 "Group Theory and its Application to Physical Problems by Morton Hamermesh"].
 @nb{If you} know nothing about quantum mechanics,
 you'd better skip the intro@(-?)duction.
 Quantum mechanics play no role in chapter 1.
 @;@nb{As an} alter@(-?)native see @nbhl["finite-groups.pdf" "finite-groups.pdf"].}
 @nb{As an} alter@(-?)native see @nbhll["finite-groups.pdf" "finite-groups.pdf"].}

@ignore{Nevertheless a brief summary:@(lb)
 @bold{Definition:} a group is a system @nb{(@bold{X}, φ)} where:@(↑lb)
 @(hspace 3)@bold{X} is a non-empty set and@(↑lb)
 @(hspace 3)φ a composition x,y∈@bold{X} → φ(x,y)∈@bold{X}@(lb)
 such that:@(↑lb)
 @(hspace 3)∃e∈@bold{X} : ∀x∈@bold{X} : (φ(e,y) = x) @bold{and}
 (∃x@↑{@(minus)1}∈@bold{X} : φ(x@↑{@(minus)1},x) = e) and@(↑lb)
 @(hspace 3)∀x,y,z∈@bold{X} : φ(φ(x,y),z) = φ(x,φ(y,z)) (associativity of the composition).@(lb)
 e is called identity. x@↑{@(minus)1} is called inverse of x. We write @nb{xy ≡ φ(x,y)}.
 Because the composition is associative, parentheses can be omitted: @nb{xyz ≡ x(yz) = (xy)z}.
 If it is obvious or irrelevant which composition a group has,
 the latter can be identified by its set only.
 The definition implies all of the following:@(lb)
 @(hspace 3)∀x∈@bold{X} : ex = x = xe,@(↑lb)
 @(hspace 3)∀x∈@bold{X} : x@↑{@(minus)1}x = e = xx@↑{@(minus)1},@(↑lb)
 @(hspace 3)∀x,y∈@bold{X} : ∃|z∈@bold{X} : zx = y, in particular z=yx@↑{@(minus)1} and@(↑lb)
 @(hspace 3)∀x,y∈@bold{X} : ∃|z∈@bold{X} : xz = y, in particular z=x@↑{@(minus)1}y.@(↑lb)
 This implies that @bold{X} has one identity only and
 that every element of @bold{X} has one inverse only:@(↑lb)
 @(hspace 3)∀x,y∈@bold{X} : xy=y ⇒ x=e,@(↑lb)
 @(hspace 3)∀x,y∈@bold{X} : xy=x ⇒ y=e,@(↑lb)
 @(hspace 3)∀x,y∈@bold{X} : xy=e ⇒ x=y@↑{@(minus)1} and@(↑lb)
 @(hspace 3)∀x,y∈@bold{X} : xy=e ⇒ y=x@↑{@(minus)1}.@(↑lb)
 Two groups @bold{X} and @bold{Y} are isomorphic to each other if there is a bijection@(↑lb)
 @(hspace 3)@nb{ξ : x∈@bold{X} → y∈@bold{Y}} such that:@(↑lb)
 @(hspace 3)∀p,q∈@bold{X} : ξ(pq) = ξ(p)ξ(q).@(↓ (hspace 1))@(lb)
 We have:@(↑lb)
 @(hspace 3)∀r,s∈@bold{Y} : ξ@↑{@(minus)1}(rs) = ξ@↑{@(minus)1}(r)ξ@↑{@(minus)1}(s).
 @(↓ (hspace 1))@(↑lb)
 Isomorphism is an equivalence relation. Every group @bold{X} is isomorphic to a subgroup
 of the symmetric group of all permutations of the set of @bold{X}.
 In particular the following two sets of maps:@(lb)
 @(hspace 2) {(y∈@bold{X} → xy∈@bold{X}) : x∈@bold{X}} and@(↑lb)
 @(hspace 2) {(y∈@bold{X} → yx∈@bold{X}) : x∈@bold{X}}@(↓ (hspace 1))@(↑lb)
 are sets of permutations of the set of @bold{X}.
 With composition as usual for permutations,
 they form two groups isomorphic to each other and to group @bold{X}.
 The two sets are the same if and only if group @bold{X} is abelean.
 @nb{For every x∈@bold{X}:}@(lb)
 @(hspace 3)the permutations y∈@bold{X} → x@↑{@(minus)1}y∈@bold{X}
 and y∈@bold{X} → xy∈@bold{X} are inverses of each other;@(↑lb)
 @(hspace 3)the permutations y∈@bold{X} → yx@↑{@(minus)1}∈@bold{X}
 and y∈@bold{X} → yx∈@bold{X} are inverses of each other.}

@elemtag["id" "The identity"] of @bold{R} is:

@inset{@nb{∀k∈@bold{N}: k → k}}

This is the only R with restriction 0 and order 1.
For every other R the restriction and order are greater than 1,
but always finite. They are not necessarily the same.
Inverses of each other have the same order and the same restriction.
There are n! Rs with restriction less than or equal to natural @nb{number n}.
These form a finite subgroup of @bold{R} isomorphic to the
@nbhl["https://en.wikipedia.org/wiki/Symmetric_group"]{symmetric group} S@↓{n}.

@note{In every group the identity is the only element of order 1 and
 inverses of each other have the same order.
 Do not confuse the order of an element with the order of a group.
 The latter is the cardinality of a group, but usually it is called its @italic{order}.
 The word `order' also is used for the consecution of elements in a list or vector.
 In most cases it is clear with which meaning the word is used.
 Where appropriate, the present document uses a phrase that avoids confusion.}

Let p and q be two Rs with restrictions r@↓{p} and r@↓{q} and
let r@↓{pq} be the restriction of pq.@(lb)
We have: @nb{0 ≤ r@↓{pq} ≤ max(r@↓{p}@bold{,} r@↓{q}).}
The restriction of pq not necessarily equals that of qp.@(lb)
See the @nber["P-example"]{example} in the description of procedure @nbr[P].

There is no R with restriction 1.@(lb)
If p is a permutation of @bold{N} with @nb{∀k∈@bold{N}: k≥1 ⇒ p(k) = k},@(lb)
then necessarily @nb{p(0) = 0} and hence @nb{∀k∈@bold{N}: p(k) = k},@(lb)
which means that p is the identity with @nb{restriction 0.}

Let @nb{a(m)} be the number of Rs with restriction m.@(lb)
We have: @nb{a(0)=1} and @nb{∀m∈@bold{N}: a(m+1) = (m+1)!@(minus)m! = mm!}.@(lb)
This implies: @nb{a(1) = 0.}
Furthermore: @nb{∀n∈@bold{N}: @larger{Σ}@↓{(m=0@bold{..}n)}a(m) = n!},@(lb)
where m runs from 0 up to and including n.

An R is an abstract mathematical concept.@(lb)
The following @nber["representations" "representations"]
in terms of Racket objects are used:

@inset{@tabular[#:sep (list (hspace 1) ":" (hspace 1))
                (list
                  (list "C" @seclink["C"]{Cycle-representation of Rs})
                  (list "P" @seclink["P"]{Function-representation of Rs})
                  (list "H" @seclink["H"]{Hash-representation of Rs})
                  (list "G" @seclink["G"]{Representation of finite subgroups of @bold{R}}))]}

H is for internal use behind the screen. @red{Advice}: avoid explicit use of H.

@note{@elemtag["representations"]{
  In this document the word `representation' refers to the way abstract mathematical concepts
  are expressed in terms of Racket objects.
  In group theory the word has quite another meaning
  (homorphic group of coordinate transformations in a linear space).
  In this document the word is not used with the group theoretical meaning.}}

Notice that:

@inset{
 @racketblock0[
 (lambda ([k : Natural]) (code:comment #,(red "This is not an R."))
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
Although the representation is not complete because of memory limits,
no distinction will be made between abstract integer numbers and
the exact integer numbers of Racket by which they are represented nor between
@racketlink[exact-nonnegative-integer? "exact non-negative integers of Racket"]
and the corresponding abstract natural numbers.

@inset{@Tabular[
 ((@bold{N}      "is the set of all natural numbers, 0 included.")
  (@bold{N@↑{+}} "is the set of all positive natural numbers.")
  (@bold{Z}      "is the set of all integer numbers."))
 #:sep (hspace 1)]}

@deftogether[
 (@defproc[#:kind "predicate" (N?  (x any/c)) boolean?]
   @defproc[#:kind "predicate" (N+? (x any/c)) boolean?]
   @defproc[#:kind "predicate" (Z?  (x any/c)) boolean?])]{
 @Tabular[
 (("Predicate" (list "Synonym in the sense of " @nbr[free-identifier=?] " of"))
  (@nbr[N?]    @nbr[exact-nonnegative-integer?])
  (@nbr[N+?]   @nbr[exact-positive-integer?])
  (@nbr[Z?]    @nbr[exact-integer?]))
 #:sep (hspace 3)
 #:row-properties (list '(top-border bottom-border) '() '() 'bottom-border)]}

The synonyms are provided by module @nbhll["N.rkt" "N.rkt"].
They are used as shorthands in the description of the procedures shown in this document,
particularly in their specifications of contracts.

@note{In this document @bold{R} is the group of @nber["R"]{restricted permutations}@(lb)
 and has nothing to do with the set of real numbers.}

@section[#:tag "C"]{Cycle notation}

All objects described in this section are defined in module @nbhll["C.rkt" "C.rkt"].
`C' is shorthand for @nb{`cycle notation'}.
A C represents an @nber["R" "R"] and is one of the following:

@itemlist[#:style 'ordered
 (list
   @item{
  A single C, which is a list of distinct @nbsl["N"]{natural numbers}.
  It represents the @nber["R" "R"]
  that maps each element of the list onto the next one, the last element onto the first one
  and every @nbsl["N"]{natural number} that is not part of the single C, onto itself. 
  The empty list and all single Cs of one element represent the
  @nber["id"]{identity} of @nber["R"]{@bold{R}}, which has order 1.
  A non-empty single C of n elements represents an @nber["R" "R"] of order n.
  The @racket[reverse] of a single C represents the inverse
  of the @nber["R" "R"] represented by the original single C.}
   @item{
  A list of Cs.
  Represents the @nber["composition" "composition"] of the @nber["R" "Rs"] represented
  by its elements. @nb{An element} of a list of Cs can be a list of Cs,
  but superfluous pairs of parentheses can be ignored,
  because the @nber["composition" "composition"] is associative.
  The order in which the single Cs appear in the list can be relevant,
  because the represented @nber["R" "Rs"] are not required to commute with each other.})]

@elemtag["normalized-C"]{A normalized C is one of the following:}

@itemlist[#:style 'ordered
 (list
   @item{
  The empty list. It is the one and only normalized C representing the
  @nber["id"]{identity of @bold{R}}.}
   @item{
  A single C of at least two elements and the first element being the smallest one.
  @nb{A circular} shift of a single C represents the same @nber["R" "R"]
  as the original single C.
  Therefore, @nb{a non-normalized} single C of at least two elements can be normalized
  by shifting it circularly until its smallest element is in front.}
   @item{
  A list of two or more disjunct non-empty normalized single Cs
  sorted in increasing order of their lengths
  and among normalized single Cs of the same length
  in increasing order of the first element.
  Sorting is possible because @nber["R" "Rs"] represented by disjunct single Cs
  commute with each other.
  The order of the represented @nber["R" "R"]
  is the least common multiple of the lengths of the single Cs.})]

Every @nber["R" "R"] can be represented by a C (in fact by many of them and ignoring memory limits).
For every C there is exactly one (in the sense of @nbr[equal?])
normalized C representing the same @nber["R" "R"].
For every @nber["R" "R"] there is exactly one representing @nb{normalized C}
(in the sense of @nbr[equal?] and ignoring memory limits).

@deftogether[
 (@defproc[#:kind "predicate" (C?            (x any/c)) boolean?]
   @defproc[#:kind "predicate" (C-normalized? (x any/c)) boolean?])]{
 Predicate @nbr[C?] does not discriminate between normalized and non-normalized Cs.@(lb)
 Predicate @nbr[C-normalized?] returns @nbr[#t] for normalized Cs only.}

@defproc[(C-normalize (c C?)) C-normalized?]{
 Returns the normalized form of its argument.
 Examples:}

@example-table[
 (C-normalize '(1 0))
 (C-normalize '(1 2 0))
 (C-normalize '((1 2) (0 3)))
 (C-normalize '((0 2) (0 1)))
 (C-normalize '((0 1) (0 2)))
 (C-normalize '((0 1 2) (0 1)))
 (C-normalize '((0 1 2) (0 2)))
 (C-normalize '((0 1 2) (1 2)))
 (C-normalize '((0 1) (0 1 2) (0 1)))
 (C-normalize '((0 1) (1 2) (2 3)))
 (C-normalize '(((0 1) (1 2)) (2 3)))
 (C-normalize '((0 1) ((1 2) (2 3))))
 (C-normalize '((() () ())))
 (C-normalize '(((99999999))))
 (C-normalize '((1) (2) (3)))
 (C-normalize '((0 1) (0 1)))]

The Cs shown below represent the same @nber["R" "R"].
Therefore procedure @nbr[C-normalize] returns the same normalized C for them
@nb{(in the sense of @nbr[equal?])}:

@example-table[
 (C-normalize '((0 1) (1 2)))
 (C-normalize '((0 2) (0 1)))
 (C-normalize '((1 2) (0 2)))
 (C-normalize '(0 1 2))
 (C-normalize '(1 2 0))
 (C-normalize '(2 0 1))
 (C-normalize '((0 1) (1 2) (0 1) (0 1)))]

The same holds for the following examples:

@example-table[
 (C-normalize '((0 1) (0 1 2)))
 (C-normalize '((0 2) (0 2 1)))
 (C-normalize '((0 2 1) (0 1)))
 (C-normalize '((0 1 2) (0 2)))]

@defproc[#:kind "predicate" (C-identity? (x any/c)) boolean?]{
 Same as @nbr[(and (C? x) (null? (C-normalize x)))].}

@defproc[(C-transpositions (c C?)) C?]{
 Returns a list of normalized transpositions
 representing the same @nber["R" "R"] as the argument.@(lb)
 A transposition is a single C of two elements.
 For every C there is a list of transpositions
 representing the same @nber["R" "R"].
 In many cases not all of the @nber["R" "R"]s represented
 by the transpositions commute with each other.
 Hence, the order in which the transpositions appear in the list, usually is relevant.
 The list of transpositions is not uniquely defined.
 Procedure @nbr[C-transpositions] returns one only,
 but always the same one (in the sense of @nbr[equal?])
 for Cs representing the same @nber["R" "R"]
 and with no more transpositions than necessary.

 Examples:

 @example-table[
 (C-transpositions '())
 (C-transpositions '(0 1))
 (C-transpositions '(0 1 2))
 (C-transpositions '(2 1 0))
 (C-transpositions '(0 1 2 3))
 (C-transpositions '(2 3 4 0 1))
 (C-transpositions '((0 1) (2 3)))
 (C-transpositions '((0 1) (0 1)))
 (C-transpositions '((0 1 2) (3 4 5)))
 (C-transpositions '((3 4 5) (0 1 2)))]

 The Cs shown in the example below represent the same @nber["R" "R"].
 Therefore procedure @nbr[C-transpositions] produces the same list of transpositions for them
 @nb{(in the sense of @nbr[equal?]):}

 @example-table[
 (C-transpositions '((0 1) (1 2)))
 (C-transpositions '((0 2) (0 1)))
 (C-transpositions '((1 2) (0 2)))
 (C-transpositions '(0 1 2))
 (C-transpositions '(1 2 0))
 (C-transpositions '(2 0 1))]}

Because every @nber["R" "R"] represented by a transposition equals its inverse,
reversal of the list of transpositions produces a C representing the inverse.
Example:

@Interaction[
 (for/and ((p (in-G (G-symmetric 4))))
   (define c (P->C p))
   (define transpositions (C-transpositions c))
   (C-identity? (list (reverse transpositions) transpositions)))]

@defproc[(C-even? (c C?)) boolean?]{
 Same as @nbr[(even? (length (C-transpositions c)))] but faster,
 because procedure @nbr[C-even?] does not form the intermediate list of transpositions
 nor does it normalize the argument.}

@note{For every C there is a list of transpositions representing the same @nber["R" "R"].
 A C that can be written as a list of an even number of transpositions
 cannot be written as a list of an odd number of transpositions and vice versa.
 Hence, every C, and consequently every @nber["R" "R"], has well defined parity.
 Composition of two @nber["R" "Rs"] with the same parity yields an even @nber["R" "R"].
 Composition of two @nber["R" "Rs"] with opposit parity yields an odd @nber["R" "R"].
 The @nber["id"]{identity of @bold{R}} has even parity.
 @nb{A finite group} containing at least one odd element has as many odd ones as even ones.
 Combined with the same composition,
 the subset of all even elements of a finite group forms an
 @nbrl[G-invariant-subg? "invariant subgroup"].
 Inverses of each other have the same parity. The same holds for conjugate elements.}

Examples:

@Interaction[
 (for/and ((p (in-G (G-symmetric 4))))
   (define c (P->C p))
   (define c-inverse (P->C (P-inverse p)))
   (eq? (C-even? c) (C-even? c-inverse)))]
@Interaction[
 (for/and ((n (in-range 5)))
   (define Sn (G-symmetric n))
   (G-invariant-subg? (G-even-subg Sn) Sn))]

@defproc[(H->C (h pseudo-H?)) C-normalized?]{
 Returns a normalized C representing the same @nber["R" "R"] as @nbr[h].@(lb)
 You probably never need this procedure.@(lb)@nb{@red{Advice: avoid it}.}}

@defproc[(C->H (c C?)) H?]{
 Returns an @nbsl["H" "H"] representing the same @nber["R" "R"] as @nbr[c].@(lb)
 You probably never need this procedure.@(lb)@nb{@red{Advice: avoid it}.}}

@section[#:tag "P"]{Function representation}

All objects described in this section are defined in
module @nbhll["P.rkt" "P.rkt"].
A P is a procedure @nbr[(-> N? N?)] representing an @nber["R" "R"].
Given the same argument, a P returns the same
@seclink["N"]{@nb{natural number}} as the represented @nber["R" "R"], of course.
For every @nber["R" "R"] there is a representing P (ignoring memory limits).
In fact Ps are opaque
@nbsl["structures" #:doc '(lib "scribblings/reference/reference.scrbl") "structures"]
with @racketlink[prop:procedure "procedure property"].
Nevertheless, Ps representing the same @nber["R" "R"] are the same in the sense of @nbr[eq?].
@red{Warning}: this may not remain true after @nbsl["Cleanup" "cleanup"].
A P contains its @nbsl["H" "H-representation"].
It memorizes its  @nber["normalized-C" "normalized C-representation"],
its @nbrl[P-even? #:style #f]{parity},
its @nbrl[P-order #:style #f]{order},
its @nbrl[P-period #:style #f]{period} and
its @nbrl[P-inverse #:style #f]{inverse},
but only after they have been needed for the first time.
A P can be given a @nbrl[set-P-name!]{name}.
See parameter @nbr[P-print-by-name] for the way a P is written, printed or displayed.

@defproc[(P (p (or/c P? C?)) ...) P?]{
 Returns the P representing the @nber["R" "R"]
 formed by @nber["composition" "composition"] of the
 @nber["R" "Rs"] represented by the arguments.
 If no argument is given, the @nbr[P-identity] is returned.
 If only one argument is given, the returned P represents the same
 @nber["R" "R"] as the argument.

 Examples:}

@Interaction[
 (define p (P '(2 3) '(4 5 6)))
 (for ((k (in-range 10))) (printf "p(~s) = ~s~n" k (p k)))]

@example-table[
 (P)
 (P '())
 (P '(0 1) '(0 1))
 (P '(((0 2) (0 1))))
 (P '(0 1))
 (P '(1 0))
 (P '(0 1) '(2 3 4))
 (P '(3 0 1 2))]

@Interaction[
 (define-values ( a  b  c) (values '(0 1) '(1 2) '(2 3)))
 (define-values (pa pb pc) (values  (P a)  (P b)  (P c)))
 (define x (P  a  b  c))
 (define y (P pa pb pc))
 y
 (eq? x y)]

Let's do a check that two Ps representing the same @nber["R" "R"]
are the same in the sense of @nbr[eq?]
(provided no disturbing @nbsl["Cleanup" "cleanup"] is made)

@Interaction[
 (define a (P '(3 4) '(4 5)))
 (define b (P '(4 5 3)))
 (code:comment #,(list "a and b represent the same " (elemref "R" "R") ":"))
 (define m (max (P-restriction a) (P-restriction b)))
 (code:line (for/and ((k (in-range m))) (= (a k) (b k))) (code:comment #,(green "true")))
 (code:comment "Hence:")
 (code:line (eq? a b) (code:comment #,(green "true")))]

Another example:

@Interaction[
 (define p (P '((0 2) (3 4 5))))
 (define q (P-inverse p))
 q
 (code:comment "Because p and q are the inverses of each other, we have:")
 (and (code:comment #,(green "true"))
   (eq? (P-inverse p) q)
   (eq? (P-inverse q) p)
   (eq? (P p q) P-identity)
   (eq? (P q p) P-identity))]

@nbr[P] is associative, of course. For example:

@Interaction[
 (define in-S4 (in-G (G-symmetric 4)))
 (for*/and ((a in-S4) (b in-S4) (c in-S4)) (code:comment #,(green "true"))
   (define x (P a (P b c)))
   (define y (P (P a b) c))
   (define z (P a b c))
   (and (eq? x z) (eq? y z) (eq? x y)))]

Some checks on the properties of @nber["composition" "compositions"] of @nber["R" "Rs"]:

@Interaction[
 (for/and ((n (in-range 5))) (code:comment #,(green "true"))
   (define Sn (G-symmetric n))
   (define in-Sn (in-G Sn))
   (for*/and ((p in-Sn) (q in-Sn))
     (define pq (P p q))
     (define qp (P q p))
     (define max-restriction
       (max
         (P-restriction p)
         (P-restriction q)))
     (and
       (G-member? pq Sn)
       (G-member? qp Sn)
       (=   (P-order pq) (P-order qp))
       (eq? (P-even? pq) (P-even? qp))
       (<= 0 (P-restriction pq) max-restriction)
       (<= 0 (P-restriction qp) max-restriction))))]

@elemtag["P-example"]{
 The @nber["R" "restriction"] of pq not necessarily equals that of qp:}

@Interaction[
 (define p (P '((1 2) (3 4))))
 (define q (P '( 1 2   3 4)))
 (define pq (P p q))
 (define qp (P q p))
 (define-syntax-rule (print-restrictions x ...)
   (begin
     (printf "~s = ~s with restriction ~s~n" 'x x (P-restriction x))
     ...))
 (print-restrictions pq qp)]

When composing two or more Ps with Racket's procedure @nbr[compose],
the result is a procedure that yields the same answers as when made with procedure @nbr[P],
but the result is not a P. Example:

@Interaction*[
 (define a (P '(0 1 2)))
 (define b (P '(1 2 3)))
 (define c (P '(2 3 4)))
 (define  abc (compose a b c))
 (define Pabc (P       a b c))
 (for/and ((k (in-range 10))) (= (abc k) (Pabc k)))]
But
@Interaction*[
 (code:line (P? abc) (code:comment #,(red "alas:")))]
whereas:
@Interaction*[
 (code:line (P? Pabc) (code:comment #,(green "true:")))]
Racket's procedure @(nbr compose) does not return @(nbr equal?) results@(lb)
when called with two or more @(nbr eq?) arguments.
@Interaction*[
 (code:line (equal? (compose a b c) (compose a b c)) (code:comment #,(red "alas:")))]
Procedure @(nbr P) does, even @(nbr eq?),
when the result represents the same @(elemref "R" "R")@(lb)
(and no disturbing @(nbsl "Cleanup" "cleanup") interferes)
@Interaction*[
 (eq? (code:comment #,(green "true"))
   (P (P a b) c)
   (P a (P b c)))]
Also:
@Interaction*[
 (eq? (code:comment #,(green "true"))
   (P-inverse (P a b c))
   (P (P-inverse c) (P-inverse b) (P-inverse a)))]
@(reset-Interaction*)

@note{Notice that (abc)@(expt-1) = c@(expt-1)b@(expt-1)a@(expt-1),
 writing x@(expt-1) for the inverse of x.}

@defproc[#:kind "predicate" (P? (x any/c)) boolean?]

@deftogether[(@defproc[(P-name (p P?)) any/c]
               @defproc[(set-P-name! (p P?) (name any/c)) void?])]{
 @nbr[P-name] returning @nbr[#f] indicates that @nbr[p] has no name. A P can be given a name.
 @nbr[(set-P-name! p name)] assigns a name or mutates it without creating a new P.
 @nbr[(set-P-name! p #f)] removes the name from @nbr[p] if it had a name.
 @Interaction[
 (define a (P '(1 2 3)))
 (define b (P '(1 2 3)))
 (P-name b)
 (code:line (set-P-name! a 'a-name) (code:comment #,(black
      (list "Also affects " @nbr[b]" because "@nbr[(eq? a b)]" → "@nbr[#t]"."))))
 (P-name b)
 (eq? a b)]}

@defparam*[P-print-by-name yes/no any/c boolean? #:value #f]{
 If this parameter is true, a @italic{@tt{p}} that has a name
 is written, printed or displayed by its name @nbr[(P-name #,(italic (tt "p")))].
 If this parameter is @nbr[#f] or the @italic{@tt{p}} has no name,
 it is written, printed or displayed in @constr-style as:
 @nbr[(P '#,(italic (tt "c")))]
 where @italic{@tt{c}} is the normalized @nbsl["C" "C-representation"].@(lb)
 Some procedures ignore this parameter and act if it were false.

 @Interaction[
 (set-P-name! P-identity 'E)
 (code:line (P-print-by-name #f) P-identity)
 (code:line (P-print-by-name #t) P-identity)
 (set-P-name! P-identity #f)
 (code:line (P-print-by-name #t) P-identity)]}

@defidform[#:kind "constant" P-identity]{
 The P representing the @nber["id" "identity"] of @nber["R"]{@bold{R}.}
 A P representing the identity always is the same as @nbr[P-identity]
 in the sense of equivalence relation @nbr[eq?],
 even after @nbsl["Cleanup" "cleanup"].}

@defproc[#:kind "predicate" (P-identity? (x any/c)) boolean?]{
 Same as @nbr[(eq? x P-identity)].
 The predicate remains valid after @nbsl["Cleanup" "cleanup"].}

@defproc[(P-commute? (p (or/c P? C?)) (q (or/c P? C?))) boolean?]{
 Same as @nbr[(eq? (P p q) (P q p))].
 Not disturbed by @nbsl["Cleanup" "cleanup"].}

@defproc[(P->C (p P?)) C-normalized?]{
 Returns the normalized @nbsl["C" "C-representation"] of @nbr[p].}
Examples:

@example-table[
 (P->C P-identity)
 (P->C (P))
 (P->C (P '(0 1) '(0 1)))
 (P->C (P '(1 0)))
 (P->C (P '(2 3 4) '(0 1)))
 (P->C (P '(2 3 0 1)))
 (P->C (P '(0 1) '(1 2) '(2 3)))
 (P->C (P '(2 3) '(1 2) '(0 1)))]

Because a P memorizes its normalized C-repesentation,
we have (if no @nbsl["Cleanup" "cleanup"] interferes):

@Interaction[
 (eq?
   (P->C (P '(2 3 0 1)))
   (P->C (P '(0 1) '(1 2) '(2 3))))]

@defproc[(P-order (p (or/c P? C?))) N+?]{
 For every argument @nbr[p] there is a smallest
 @nbsl["N"]{positive natural number} @nbr[k]
 such that @nb{@nbr[(P-expt p k)] → @nbr[P-identity].}
 @nbr[k] is called the order of the @nber["R" "R"] represented by @nbr[p].@(lb)
 The @nber["id" "identity"] of @nber["R"]{@bold{R}}
 is the only @nber["R" "R"] of order 1.
 For every other @nber["R" "R"] the order is greater than 1.}

@note{
 The order of an element of a finite group always is a divisor of the order of the group.@(lb)
 Do not confuse the order of a group element with the order of a group.}

Examples:

@Interaction[
 (define a (P '(0 1)))
 (define b (P '(2 3 4)))
 (define c (P '(5 6 7 8 9)))
 (define e P-identity)
 (define (show p)
   ((fmt "R27W N' has order ' R2W/" 'cur) (P->C p) (P-order p)))
 (for-each show
   (list
     e
     a
     b
     c
     (P a b)
     (P a c)
     (P b c)
     (P a b c)))]

@defproc*[(((P-period (p P?)) (vector-immutableof P?))
           ((P-period (c C?)) (vector-immutableof P?)))]{
 If the argument is a @nbsl["C" "C"] it is first converted to a @nbsl["P" "P"].
 @nbr[(P-period c)] is treated as @nbr[(P-period (P c))].
 Procedure @nbr[P-period] returns an immutable vector of length @nbr[(P-order p)] containing the
 powers of @nbr[p].
 Element with index @nbr[i] contains @nbr[(P-expt p i)].
 The period and the order of @nbr[p] are memorized in @nbr[p].
 They are not computed again when already available.
 The first element @nb{(index 0)} of the vector always is @nbr[P-identity].
 If @nbr[p] is not the @nbr[P-identity],
 the second element @nb{(index 1)} is @nbr[p] itself.
 The last element always is the @nbrl[P-inverse "inverse"] of @nbr[p].
 In fact, when omitting the first element (index 0, id est, the @nbr[P-identity]),
 the elements taken from right to left are the @nbrl[P-inverse "inverses"] of the elements
 taken from left to right.}
Examples:

@example-table[
 (P-period P-identity)
 (P-period (P '(0 1)))
 (P-period (P '(3 5 7)))]

@Interaction[
 (for/and ((p (in-G (G-symmetric 4)))) (code:comment #,(green "true"))
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
 Then @nb{∀k∈@bold{Z}: x@↑{k} = x@↑{k @bold{modulo} m}},@(lb)
 defining k @bold{modulo} m = k@tt{-}m⌊k/m⌋ for k,m∈@bold{Z} and m≠0.@(lb)
 This does the same as procedure @nbr[modulo] of Racket.}

Large exponents do no harm.
The power is computed almost as fast as for small exponents.
The computation of the modulus of an exponent with great absolute value may be somewhat slower,
though.

@(collect-garbage)

@Interaction[
 (code:line (define big (* 6 (expt 10 1000000))) (code:comment "= #e6e1000000"))
 (define exponents (range -10 11))
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
 ∀x∈@bold{X}: ∀k,m∈@bold{Z}: (x@↑{k})@↑{m} = x@↑{km}@(hspace 3)and@(lb)
 ∀x∈@bold{X}: ∀k,m∈@bold{Z}: x@↑{k}x@↑{m} = x@↑{k+m}}

This applies to @nber["R" (bold "R")] too, of course. For example:

@Interaction[
 (define p (P '(0 1) '(3 4 5)))
 (P-order p)
 (define in-exponents (in-range -10 10))
 (for*/and ((k in-exponents) (m in-exponents))
   (and
     (eq? (P-expt (P-expt p k) m)       (P-expt p (* k m)))
     (eq? (P (P-expt p k) (P-expt p m)) (P-expt p (+ k m)))))]

@defproc*[(((P-inverse (p P?)) P?) ((P-inverse (c C?)) P?))]{
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

@Interaction[
 (define S4 (G-symmetric 4))
 (G-order S4)
 (for/and ((p (in-G S4))) (code:comment #,(green "true"))
   (define q (P-inverse p))
   (and
     (P-identity? (P q p))
     (P-identity? (P p q))
     (equal? (P-non-fixed-points p) (P-non-fixed-points q))
     (=      (P-order            p) (P-order            q))
     (=      (P-restriction      p) (P-restriction      q))
     (eq?    (P-even?            p) (P-even?            q))))]

For every group @bold{X} we have:

@inset{@nb{∀a,b∈@bold{X}: (ab)@(expt-1) = b@(expt-1)a@(expt-1)}}

This applies to @nber["R" @bold{R}] too:

@Interaction[
 (define in-S4 (in-G (G-symmetric 4)))
 (for*/and ((a in-S4) (b in-S4)) (code:comment #,(green "true"))
   (eq?
     (P-inverse (P a b))
     (P (P-inverse b) (P-inverse a))))]

@defproc[(P-even? (p (or/c P? C?))) boolean?]{
 Returns @nbr[#t] if the @nber["R" "R"] represented by the argument is even.@(lb)
 Returns @nbr[#f] if the @nber["R" "R"] represented by the argument is odd.@(lb)
 See procedure @nbr[C-even?].}
Examples:

@Interaction[
 (and
   (P-even? P-identity)
   (not (P-even? (P '(0 1))))
   (P-even? (P '(0 1) '(2 3)))
   (P-even? (P '(0 1) '(1 2)))
   (not (P-even? (P '(0 1) '(1 2) '(1 0))))
   (P-even? (P '(0 1 2)))
   (eq? (P '(0 1 2)) (P '(0 2) '(0 1)))
   (not (P-even? (P '(0 2 4 6))))
   (eq? (P '(0 2 4 6)) (P '(0 6) '(0 4) '(0 2))))]

@Interaction[
 (define S3-list (G->list (G-symmetric 3)))
 (filter P-even? S3-list)
 (filter (compose not P-even?) S3-list)]

Let's check that a @nbsl["G" "G"] with at least one odd element
has as many odd elements as even ones.

@Interaction[
 (define (check g)
   (define in-g (in-G g))
   (define  odd-set (for/seteq ((p in-g) #:unless (P-even? p)) p))
   (define even-set (for/seteq ((p in-g) #:when   (P-even? p)) p))
   (cond
     ((and (zero? (set-count odd-set)) (equal? (expected) "all even")))
     ((and
        (=
          (set-count  odd-set)
          (set-count even-set)
          (/ (G-order g) 2))
        (for/and ((odd-p (in-set odd-set)))
          (equal?
            (for/seteq ((even-p (in-set even-set))) (P odd-p even-p))
            odd-set))
        (equal? (expected) "as many odd elements as even ones")))
     (else (error 'check "this should never happen: ~s" g))))
 (code:comment " ")
 (define expected (make-parameter #f))
 (code:comment " ")
 (and
   (code:comment " ")
   (code:comment "Tests on symmetric groups of order greater than 1")
   (code:comment " ")
   (parameterize ((expected "as many odd elements as even ones"))
     (for/and ((n (in-range 2 6)))
       (check (G-symmetric n))))
   (code:comment " ")
   (code:comment "Two checks on non-symmetric groups:")
   (code:comment " ")
   (parameterize ((expected "as many odd elements as even ones"))
     (and
       (check (G '((0 1) (2 3)) '((4 5) (6 7)) '(8 9)))
       (check (G '((0 1) (2 3)) '((4 5) (6 7)) '(0 1)))))
   (code:comment "")
   (code:comment "Checks on groups without odd elements.")
   (code:comment " ")
   (parameterize ((expected "all even"))
     (and
       (check G-identity)
       (check (G '(0 1 2)))
       (check (G '((0 1 2 3) (2 3 4 5))))
       (check (G '(0 1 2) '(1 2 3))))))]

@defproc[(P<? (p0 (or/c P? C?)) (p1 (or/c P? C?))) boolean?]{
 Defines a sorting order among @nber["R" "Rs"]. The sorting keys are:@(lb)
 @inset{
  1: the @nbrl[P-even? #:style #f "parity"],
  even @nber["R" "Rs"] preceding odd @nber["R" "Rs"].@(lb)
  2: the order of the @nber["R" "Rs"].@(lb)
  3: the number of non-fixed points.@(lb)
  4: the least non-fixed point.@(lb)
  5: @nbr[(p k)] for the smallest @nbr[k]
  for which the two @nber["R" "Rs"] yield different values.}
 @nbr[P<?] remains comparing correctly after @nbsl["Cleanup" "cleanup"].
 @Interaction[
 (define S4 (G-symmetric '(3 5 7 9)))
 (define S4-list (G->list S4))
 (define shuffled-S4-list S4-list)
 (define sorted-S4-list (sort shuffled-S4-list P<?))
 (equal? S4-list sorted-S4-list)
 sorted-S4-list]}

@defproc[(P-sort (ps (listof (or/c P? C?)))) (listof P?)]{
 Like @nbr[(sort (map P ps) P<?)], id est,
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

@(random-seed 1)

@(define permutations-note (list "See " (elemref "note" "note below")"."))

@Interaction[
 (random-seed 1)
 (code:line (define S3-list0 (G->list (G-symmetric 3))) (code:comment "S3-list0 is sorted."))
 (code:line (R-clear-hashes) (code:comment #,(list "Does not disturb procedure " (nbr P-sort))))
 (code:line (define S3-list1 (G->list (G-symmetric 3))) (code:comment "S3-list1 is sorted."))
 (code:comment "")
 (map P->C S3-list0)
 (code:comment "")
 (code:line (define in-rearrangements in-permutations) (code:comment #,permutations-note))
 (code:comment "")
 (for/and ((rearranged-S3-list1 (in-rearrangements S3-list1))) (code:comment #,(green "true"))
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
@note{According to the @nber["rearrangement" "terminology"] used in this document,
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

@Interaction[
 (define in-S4 (in-G (G-symmetric 4)))
 (for/and ((p in-S4)) (code:comment #,(green "true"))
   (define nfps (P-non-fixed-points p))
   (and
     (equal? nfps (sort (map p nfps) <))
     (equal? nfps (P-non-fixed-points (P-inverse p)))))]

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

@Interaction[
 (define (fixed-points p n)
   (for/list ((k (in-range n)) #:when (P-fixed-point? p k)) k))
 (fixed-points (P '(0 1) '(5 6 7)) 10)
 (for ((n (in-range 1 4)))
   (printf "~n ~nS~s~n" n)
   (for ((p (in-G (G-symmetric n))))
     ((fmt "L12W N' has fixed points ' L7W N' and every k≥' W/" 'cur)
      p (fixed-points p n) n)))]

@defproc[(P->H (p P?)) H?]{
 You probably never need this procedure. @red{Advice: avoid it}.}

@defproc[(H->P (h pseudo-H?)) P?]{
 You probably never need this procedure. @red{Advice: avoid it.}
 Nevertheless, procedure @nbr[H->P] can sometimes be useful.
 See the @elemref["H->P-example" "example"] in section @nbsl["C3v"]{Group C@↓{3v}}.}

@(define sequenceref
   (nbhl "https://docs.racket-lang.org/reference/sequences.html" "sequence"))

@section[#:tag "G"]{Finite subgroups of @nber["R" (bold "R")]}

All objects described in this section are defined in
module @nbhll["G.rkt" "G.rkt"].
A G represents a finite subgroup of @nber["R" (bold "R")] and is
written, displayed or printed in @constr-style as:

@inset{@nbr[(G (P '()) (P '#,(italic (tt "c"))) ...)]}

showing in @nbrl[P-sort]{sorted} order all @nbsl["P" "Ps"]
representing the elements of the G (ignoring parameter @nbr[P-print-by-name]).
@nb{Gs produced} by the procedures of this section and representing the same subgroup of
@nber["R" (bold "R")] are the same in the sense of @nbr[eq?].
@red{Warning}: this may not remain true after a @nbsl["Cleanup" "cleanup"].
@nb{For every} finite group there is an isomorphic G (ignoring memory limits).

@defproc[(G (p (or/c P? C?)) ...) G?]{
 Returns the G representing the smallest (least @nbrl[G-order]{order})
 group containing all @nber["R" "Rs"]
 represented by the arguments.
 Duplicate arguments representing the same @nber["R" "R"] do no harm.
 If no argument is given, the @nbr[G-identity] is returned.}

@note{By definition a group, say @bold{X}, recursively includes
 the composition of every pair of its elements,@(lb)
 the composition of every element with itself included, id est,
 @nb{∀x,y∈@bold{X}: xy∈@bold{X}}.}

Examples:

@(example/n (G))

@(example/n (G '()))

@(example/n (G P-identity))

@(example/n (G '(0 1)))

@(example/n (G '(0 1 2) '(1 2 0) '(2 0 1)))

@(example/n (G '(0 1) '(2 3)))

@(example/n (G '(0 1) '(1 2)))

@(example/n (G '(0 1) '(0 1 2)))

@Interaction[(define X (G '(0 3) '(0 1 2)))
             (G-order X)
             (define in-X (in-G X))
             (for*/and ((p in-X) (q in-X)) (G-member? (P p q) X))]

@nbr[(G '(0 1) '(1 2))] yields the same as @nbr[(G '(0 1) '(0 1 2))].@(lb)
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

@defproc[(G-order (g G?)) N+?]{
 Returns the order of @nbr[g], id est, its number of elements.

 @note{Do not confuse the order of a G with the order of a
  @nbsl["P" "P"] (See @nbr[P-order]).
  The order of every @nbsl["P" "P"] of a G is a divisor of the order of that G.
  This is a consequence of the more general theorem of group theory that
  the order of an element of a finite group always is a divisor of the order of that group.
  This theorem holds for all finite groups, Gs included.}}

@defproc[(in-G (g G?)) (Sequenceof P?)]{
 Returns an eagerly @nbrl[P-sort "sorted"] @sequenceref of the elements of @nbr[g].}

@defproc[(G-member? (p (or/c P? C?)) (g G?)) boolean?]{
 Returns @nbr[#t] if the @nber["R" "R"] represented by @nbr[p]
 is an element of the @nbsl["G" "G"] represented by @nbr[g],@(lb)
 else returns @nbr[#f].}
Examples:

@Interaction[(define g (G '(0 1) '(0 2)))
             (define in-g (in-G g))
             (code:comment "By definition, ∀p,q∈g: pq∈g")
             (for*/and ((p in-g) (q in-g)) (G-member? (P p q) g))]

@color-example[green (G-member? P-identity G-identity)]
@color-example[red   (G-member? '(2 3) G-identity)]

@red{Warning}: procedure @nbr[G-member?] can be confused by a @nbsl["Cleanup" "cleanup"]:

@Interaction[
 (define c '(0 1))
 (define g (G c))
 (code:line (G-member? c g)  (code:comment #,(green "true")))
 (code:line (R-clear-hashes) (code:comment #,(red "caution")))
 (code:line (G-member? c g)  (code:comment #,(red "alas")))]

@defproc[(G-print-table (g G?) (output-port output-port? (current-output-port))) void?]{
 The @nber["composition" "composition"] table of @nbr[g] is printed in normalized
 @nbsl["C" "cycle-notation"] on the @nbr[output-port].
 Every element is the @nber["composition" "composition"] pq
 of element p in the left column and element q in the top row.
 The left column and top row are @nbrl[P-sort "sorted"] and start with the
 @nbrl[P-identity "identity"].
 The columns are aligned (assuming a fixed width font).}

@note{For every group @bold{X} with identity e we have: @nb{∀x∈@bold{X}: ex = x = xe}.
 Hence, with the identity as the first label for both columns and rows,
 the first row and first column of the table proper are the same as the labels.
 Therefore we can omit the labels.} Example:

@Interaction[
 (define C3v (G '(0 1) '(0 1 2)))
 (G-print-table C3v)]

See section @nbsl["C3v"]{Group C@↓{3v}}
for a more elaborated discussion of this group.

@defproc[(G-table (g G?)) (vector-immutableof (vector-immutableof P?))]{
 Returns the @nber["composition" "composition"]
 table of @nbr[g] as an immutable vector of immutable vectors of @nbsl["P" "Ps"].
 The first row, id est, @nbr[(vector-ref (G-table g) 0)]
 and the first column, id est,
 @nbr[(for/vector ((row (in-vector (G-table g))) (vector-ref row 0)))]
 are @nbrl[P-sort "sorted"].}

@Interaction[
 (define C3v (G '(0 1) '(0 1 2)))
 (define table (G-table C3v))
 table
 (code:comment "Check that every element pq of the table is the composition of")
 (code:comment "element p in the left column and element q in the top row.")
 (define indices (in-range (G-order C3v)))
 (code:comment "(table-ref i j) = element in row i and column j.")
 (define (table-ref i j) (vector-ref (vector-ref table i) j))
 (for*/and ((i indices) (j indices))
   (define p  (table-ref i 0))
   (define q  (table-ref 0 j))
   (define pq (table-ref i j))
   (eq? pq (P p q)))]

@defproc*[(((G-symmetric (n N?) (offset N? 0)) G?)
           ((G-symmetric (lst (listof N?))) G?))]{
 The first form returns the @nbhl["https://en.wikipedia.org/wiki/Symmetric_group"]{symmetric group}
 of all @nbr[n]! @nbsl["P" "Ps"] corresponding to the rearrangements
 of the @nbsl["N"]{natural numbers}
 from @nbr[offset] up to but not including @nbr[(+ offset n)].
 All @nbsl["N"]{natural numbers} outside this range are
 @nbrl[P-fixed-point?]{fixed points} of all elements of the group.
 @nbr[(G-symmetric 0 offset)] and @nbr[(G-symmetric 1 offset)]
 both evaluate to the @nbr[G-identity].
 Obviously @nbr[G-symmetric] yields isomorphic groups when
 called with the same value for @nbr[n].
 The order of the returned G is @nbr[n]!.

 The second form returns the @nbhl["https://en.wikipedia.org/wiki/Symmetric_group"]{symmetric group}
 corresponding to all rearrangements of @nbr[lst].
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

@Interaction[
 (define g0 (G-symmetric 3))
 (define g1 (G-symmetric 3 1))
 (define g2 (G-symmetric 3 2))
 (define g3 (G-symmetric '(0 3 6)))
 g0
 g1
 g2
 g3
 (and
   (G-isomorphism g0 g1)
   (G-isomorphism g0 g2)
   (G-isomorphism g0 g3)
   #t)
 (code:comment "")
 (and
   (eq? (G-symmetric '()) G-identity)
   (eq? (G-symmetric '(0 1 2)) (G-symmetric 3))
   (eq? (G-symmetric '(4 5 6)) (G-symmetric 3 4)))]

@deftogether[(@defproc[#:kind "predicate" (G-abelean? (g G?)) boolean?]
               @defproc[#:kind "predicate" (G-commutative? (g G?)) boolean?])]{
 @nbr[G-commutative?] is a synonym of @nbr[G-abelean?] in the sense of @nbr[free-identifier=?].

 @note{By definition, a group is abelean if and only if all its elements commute with each other.
  @(lb)Sufficient is that all elements of a @nbrl[G-base]{base} commute with each other.}

 Examples:}

@color-example[green (G-abelean? (G '(0 1 2) '(3 4)))]
because: @color-example[ green (P-commute? (P '(0 1 2)) (P '(3 4)))]

But: 
@color-example[red (G-abelean? (G '(0 1 2) '(0 1)))]
because: @color-example[red (P-commute? (P '(0 1 2)) '(0 1))]
In particular:@(lb)
@example[(P '(0 1 2) '(0 1))]
@example[(P '(0 1) '(0 1 2))]

@defproc[(G-base (g G?)) (Setof P?)]{
 Returns a @nbr[seteq] with a minimal base for @nbr[g].
 @(nbsl "G" "G")s of order greater than 2 have more than one minimal base.
 @nbr[G-base] returns one of them only. See @nbr[G-bases].} Example:

@(random-seed 1)

@Interaction[
 (random-seed 1)
 (define g (G '(4 5) '(0 1) '(2 3)))
 (define g-base (G-base g))
 (code:comment #,(list
                   "The returned base not necessarily is the "
                   (elemref "simplest base" "simplest one") ":"))
 g-base
 (code:comment "Nevertheless it is a correct base:")
 (eq? (apply G (set->list g-base)) g)]

The @nbrl[G-symmetric "symmetric groups"] S@↓{1} and S@↓{2}
both have one minimal base of one element.
Every symmetric group S@↓{n} with n≥3
has at least one minimal base of two elements, @nb{for example:}

@Interaction[
 (G-base (G-symmetric 0))
 (G-base (G-symmetric 1))
 (G-base (G-symmetric 2))
 (for/and ((n (in-range 3 8)))
   (define n-1 (sub1 n))
   (define Sn (G-symmetric n))
   (and (= (set-count (G-base Sn)) 2)
     (code:comment "As an example take base {(0 n-1), (0 .. n-2)},")
     (code:comment "where (0 n-1) is a transposition and")
     (code:comment "where (0 .. n-2) is the cycle of the natural")
     (code:comment "numbers from 0 up to and including n-2.")
     (eq? Sn (G (list 0 n-1) (range 0 n-1)))))]

The following example is not a proof,
but shows how to prove that every symmetric group S@↓{n} with n≥3
has at least one minimal base of two elements.

@Interaction[
 (if
   (for/and ((n (in-range 2 8)))
     (define n-1 (sub1 n))
     (code:comment "transposition and cycle form a minimal base.")
     (define transposition (P (list 0 n-1)))
     (define cycle (P (range 0 n-1)))
     (code:comment "base-of-transposition is not minimal for n>3.")
     (define base-of-transpositions
       (for/list ((k (in-range n-1)))
         (P (P-expt cycle k) transposition (P-expt cycle (- k)))))
     ((fmt 'cur "x/'n = 'W/x/ U#(W/)")
      n base-of-transpositions)
     (eq? (apply G base-of-transpositions) (G-symmetric n)))
   (printf "~n ~netc.~n")
   (error 'example "failed! (This should never happen)"))]

For n>2 the set of @nbrl[C-transpositions]{transpositions}
@nb{{(k n@(minus)1): 0 ≤ k < n@(minus)1}}
forms a (non-minimal) base @nb{for S@↓{n}},
because every element of S@↓{n} can be written as a composition of transpositions and
every relevant transposition @nb{(i j)} not in the list of transpositions can be
obtained by composing three transpositions of the list as follows:
@nb{((i n@(minus)1) (j n@(minus)1) (i n@(minus)1)) = (i j)},
where i, j and @nb{n@(minus)1} are three distinct natural numbers.

@defproc[(G-bases (g G?)) (listof (Setof P?))]{
 Returns a list of all minimal bases of @nbr[g].} Examples:

@Interaction[
 (define (G-order+bases g)
   (define bases (G-bases g))
   ((fmt 'cur
      "'order: 'W/"
      "'nr of minimal bases 'W/"
      "U#(W/)")
    (G-order g)
    (length bases)
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
 (for/and ((base (in-list (G-bases g))))
   (eq? (apply G (set->list base)) g))]

@elemtag["simplest base"]{To find one of the simplest bases:}

@Interaction[
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
 (find-simple-base (G-symmetric 3))
 (find-simple-base (G-symmetric 4))
 (find-simple-base (G-symmetric 5))]

@defproc[(G-subg? (g0 G?) (g1 G?)) boolean?]{
 @nbr[#t] if @nbr[g0] is a subgroup of @nbr[g1].@(lb)
 @red{Warning}: procedure @nbr[G-subg?] can be confused by a @nbsl["Cleanup" "cleanup"]:}

@Interaction[
 (define g0a (G '(0 1)))
 (define g1  (G '(0 1) '(0 2)))
 (code:line (G-subg?  g0a g1)  (code:comment #,(green "true")))
 (code:line (R-clear-hashes)   (code:comment #,(red "caution")))
 (code:line (G-subg?  g0a g1)  (code:comment #,(green "true")))
 (define g0b (G '(0 1)))
 (code:line (G-equal? g0a g0b) (code:comment #,(green "true")))
 (code:line (  equal? g0a g0b) (code:comment #,(red "alas")))
 (code:line ( G-subg? g0b g1)  (code:comment #,(red "alas")))]

@defproc[(G-proper-subg? (g0 G?) (g1 G?)) boolean?]{
 @nbr[g0] is a proper subgroup of @nbr[g1]
 if and only if it is a @nbr[G-subg?] of @nbr[g1]
 but not the @nbr[G-identity] and not the same as @nbr[g1].
 @red{Warning}: procedure @nbr[G-proper-subg?]
 can be confused by a @nbsl["Cleanup" "cleanup"].}

@defproc[(G-even-subg (g G?)) G?]{
 Returns the G representing the invariant subgroup of all even Ps of @nbr[g].
 Same, but faster, as:
 @inset{@nbr[(list->G (filter P-even? (G->list g)))]}
 Example:}

@Interaction[
 (define g (G '(0 1) '(0 1 2)))
 (define h (G-even-subg g))
 g
 h
 (code:line (for/and ((p (in-G g))) (P-even? p)) (code:comment #,(red "False.")))
 (code:line (for/and ((p (in-G h))) (P-even? p)) (code:comment #,(green "True.")))]

@defproc[(G-subgroups (g G?)) (listof G?)]{
 Returns a list of all subgroups of @nbr[g]. Example:

 @Interaction[
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
     ((fmt "L8W L11W L5W NU#(XW)/" 'cur)
      (proper?    subg)
      (invariant? subg)
      (G-order    subg)
      (map P->C (G->list subg))))
   (printf line))]

 @note{The order of a subgroup of a finite group always is a divisor
  of the order of the latter.}}

@defproc[#:kind "predicate" (G-simple? (g G?)) boolean?]{
 A group is simple if none of its non-trivial subgroups is invariant.} Examples:

@example-table[
 (G-simple? G-identity)
 (G-simple? (G '(0 1)))
 (G-simple? (G '(0 1 2)))
 (G-simple? (G '(0 1 2 3)))
 (G-simple? (G '(0 1) '(1 2)))
 (G-simple? (G '((0 1) (1 2))))
 (G-simple? (G '(0 1) '(2 3)))]

@defproc[(G-class (p P?) (g G?)) (Setof P?)]{
 Returns the conjugation class of @nbr[g] containing element @nbr[p].@(lb)
 If @nbr[p]∉@nbr[g], @nbr[G-class] returns an empty set.

 @note{
  Two elements a and b of a group @bold{X} are conjugates of each other if and only if:
  @nb{∃c∈@bold{X}: ac = cb}.
  @nb{This is} an equivalence relation, which defines conjugation classes in @bold{X}.
  Two elements belong to the same class if and only if they are conjugates of each other.
  All elements of a conjugation class of a finite group
  have the same order and the same normalized cycle structure.
  The number of elements in a conjugation class of a finite group
  always is a divisor of the order of the group.
  @nb{A conjugation} class of element @nb{x∈@bold{X}} consists of x only if and only if
  it commutes with all elements of @bold{X}.
  This implies that the identity always is lonesome in its class;
  it is a conjugate of itself only.
  @nb{It also} implies that the class of every element of an abelean group
  consists of this element only.}}

Examples:

@Interaction*[
 (define g (G '(0 1) '(0 2)))
 (G-class P-identity g)
 (G-class (P '(0 1)) g)
 (G-class (P '(0 1 2)) g)
 (code:comment "Empty set if p∉g:")
 (G-class (P '(0 3)) g)]

@defproc[(G-classes (g G?)) (listof (Setof P?))]{
 Returns a list of all conjugation classes of @nbr[g].
 All elements of a conjugation class
 have the same normalized cycle structure:
 
 @Interaction*[
 (define (print-G-classes g)
   (for ((CLASS (in-list (G-classes g))) (n (in-naturals 1)))
     (printf "Class ~s: " n)
     (for ((p (in-set CLASS))) (printf "~s " (P->C p)))
     (newline)))
 (print-G-classes (G '(0 1) '(0 2)))]
 
 There may be more than one class with
 the same normalized cycle structure.
 For example:

 @Interaction*[
 (code:comment "Classes 3 and 4 have elements of the same cycle structure:")
 (print-G-classes (G '(1 3) '(0 1 2 3)))]

 and
 
 @Interaction*[
 (code:comment "Classes 1, 2 and 3 have the same structure:")
 (print-G-classes (G '((0 1 2 3) (4 5 6 7)) '((0 4 2 6) (1 7 3 5))))]
 
 In a symmetric group two elements belong to the same conjugation
 class if and only if they have the same normalized cycle structure:

 @Interaction*[
 (print-G-classes (G-symmetric 4))]}
@(reset-Interaction*)

@defproc[(G-invariant-subg? (g0 G?) (g1 G?)) boolean?]{
 @nbr[g0] is an invariant subgroup of @nbr[g1] if it is a subgroup of @nbr[g1] and@(lb)
 @nb{∀p∈@nbr[g1]: {pq: q∈@nbr[g0]} = {qp: q∈@nbr[g0]}}.@(lb)
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

@Interaction[
 (define S4 (G-symmetric 4))
 (define S4-even (G-even-subg S4))
 (G-order S4)
 (G-order S4-even)
 (G-invariant-subg? S4-even S4)]

@defproc[(G-isomorphism (g0 G?) (g1 G?) (name0 symbol? 'no-name) (name1 symbol? 'no-name))
         (or/c #f (list/c (-> P? P?) (-> P? P?)))]{
 If @nbr[g0] and @nbr[g1] are isomorphic,
 a list of two isomorphisms is returned,
 the car mapping the @nbsl["P" "P"]s of @nbr[g0] onto those of @nbr[g1]
 the cadr being the inverse of the car.
 The two isomorphisms are functions and @nbr[name0] and @nbr[name1] their names.
 If @nbr[g0] and @nbr[g1] are not isomorphic, @nbr[#f] is returned.
 Two isomorphic Gs may have more than one isomorphism.
 Procedure @nbr[G-isomorphism] returns one only plus its inverse.

 @note{@elemtag["iso"]{Two groups @bold{X} and @bold{Y} are isomorphic to each other
   if and only if there is a bijection @nb{ξ: @bold{X} ↔ @bold{Y}} such that:
   @nb{∀p,q∈@bold{X}: ξ(pq) = ξ(p)ξ(q).}
   Because ξ is a bijection, we also have:@(↑ (hspace 1))
   @nb{∀a,b∈@bold{Y}: ξ@(expt-1)(ab) = ξ@(expt-1)(a)ξ@(expt-1)(b).}
   Isomorphism is an
   @nbhl["https://en.wikipedia.org/wiki/Equivalence_relation" "equivalence relation."]}}} Examples:

Abelean group of 4 elements, called the `four group' or `V'.@(lb)
Every element of V is its own inverse.

@Interaction*[
 (define V (G '(0 1) '(2 3)))
 (G-order V)
 (G-abelean? V)
 (for/and ((p (in-G V))) (eq? (P-inverse p) p))]

There are two isomorphically distinct groups of order 4.@(lb)
An example of the other one is:

@Interaction*[
 (define C4 (G '(0 1 2 3)))
 (G-order C4)
 (G-abelean? C4)]

C4 is not isomorphic to V.

@Interaction*[
 (code:line (G-isomorphism V C4) (code:comment #,(red "false")))]

In particular @nbr[(P '(0 1 2 3))] not equals its own inverse:

@Interaction*[
 (code:line (let ((p (P '(0 1 2 3)))) (eq? (P-inverse p) p)) (code:comment #,(red "false")))]

@(reset-Interaction*)

Check that two isomorphisms returned by @nbr[G-isomorphism] are inverses of each other:

@Interaction*[
 (define g0 (G '(0 1) '(2 3)))
 (define g1 (G '((1 2) (7 8)) '((5 6) (3 4))))
 (define-values (g0->g1 g1->g0)
   (apply values (G-isomorphism g0 g1 'g0->g1 'g1->g0)))
 (eq? (list->G (map g0->g1 (G->list g0))) g1)
 (eq? (list->G (map g1->g0 (G->list g1))) g0)]

If the two Gs are not isomorphic, G-isomorphism returns @nbr[#f].

@Interaction[
 (code:line (G-isomorphism (G '(0 1) '(2 3)) (G '(0 1 2 3))) (code:comment #,(red "false")))]

An error is reported if the argument
is not in the domain of the isomorphism.

@Interaction*[
 (code:line (g1->g0 (P '(0 1))) (code:comment #,(red "error")))]
@(reset-Interaction*)

@red{Warning}: after @nbsl["Cleanup" "cleaning up"]
isomorphisms made before do not recognize newly constructed @nbsl["P" "P"]s:

@Interaction[
 (define iso
   (G-isomorphism
     (G '(0 1 2))
     (G '(1 2 3))
     '012->123
     '123->012))
 (define p (P '(0 1 2)))
 (code:line ((car iso) p) (code:comment #,(green "true")))
 (code:line ((cadr iso) p) (code:comment #,(red "error")))
 (code:line (R-clear-hashes) (code:comment #,(red "Caution")))
 (code:comment "Because of the cleanup the following raises an exception:")
 (code:line ((car iso) (P '(0 1 2))) (code:comment #,(red "error")))
 (code:comment "because after cleanup:")
 (define q (P '(0 1 2)))
 (code:line (equal? p q) (code:comment #,(red "alas")))
 (code:comment "although:")
 (code:line (P-equal? p q) (code:comment #,(green "true")))]

@defproc[(G->list (g G?)) (listof P?)]{
 Returns a sorted list of all elements of @nbr[g] using @nbr[P-sort].}

@defproc[(list->G (p-list (listof P?))) G?]{
 If the @nbsl["P" "Ps"] of the argument form a group
 the corresponding G is returned, else an exception is raised.
 Duplicate arguments representing the same @nber["R" "R"] do no harm.
 Examples:}

@Interaction[
 (list->G (list P-identity (P '(0 1 2)) (P '(0 2 1))))
 (code:comment "duplicates do no harm:")
 (list->G (list P-identity P-identity (P '(0 1)) (P '(0 1))))
 (code:comment "Error when the list does not form a group:")
 (code:comment #,(list "In the following example " @nbr[(P '((0 1) (2 3)))] " is missing."))
 (code:line (list->G (list P-identity (P '(0 1)) (P '(2 3)))) (code:comment #,(red "alas")))]

@section[#:tag "Cleanup"]{Cleanup}

@defproc*[
 (((R-hashes-count) N+?)
  ((R-clear-hashes) void?))]{
 Modules @nbhll["P.rkt" "P.rkt"] and @nbhll["G.rkt" "G.rkt"]
 use hashes in order to avoid repeated identical computations
 and to guarantee that
 @nbsl["P" "P"]s and @nbsl["G" "G"]s that represent the same @nber["R" "R"]s and
 groups of @nber["R" "R"]s are the same in the sense of @nbr[eq?].
 The two procedures shown above allow inspection of the total number of keys in the hashes
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
   @defproc[#:kind "equivalence relation" (G-equal? (g0 G?) (g1 G?)) boolean?])]{
 Not disturbed by @nbsl["Cleanup"]{cleanup}. Examples:}

@Interaction[
 (define p (P '(0 1 2)))
 (define g (G '(0 1 2) '(0 1)))
 (eq? p (P '(1 2 0)))
 (eq? g (G '(0 1) '(0 2)))
 (R-clear-hashes)
 (code:line (equal? p (P '(0 1 2))) (code:comment #,(red "alas:")))
 (code:line (equal? g (G '(0 1 2) '(0 1))) (code:comment #,(red "alas:")))
 (code:line (P-equal? p (P '(2 0 1))) (code:comment #,(green "true")))
 (code:line (G-equal? g (G '(0 1) '(1 2))) (code:comment #,(green "true")))]

@section[#:tag "Distinct-instances"]{Distinct instances of @nbhll["R.rkt" "R.rkt"]}
Two distinct instances of module @nbhll["R.rkt" "R.rkt"]
do not recognize each others @nbsl["P" "Ps"] or @nbsl["G" "Gs"],
not even their @nbrl[P-identity "P-identities"] and @nbrl[G-identity "G-identities"]:

@Interaction[
 (define other-eval
   (let ((namespace (make-base-namespace)))
     (parameterize ((current-namespace namespace))
       (namespace-require 'racket)
       (namespace-require 'restricted-permutations/R))
     (lambda (expr) (eval expr namespace))))
 (define other-P-identity  (other-eval 'P-identity))
 (define other-G-identity  (other-eval 'G-identity))
 (define other-P-identity? (other-eval 'P-identity?))
 (define other-G-identity? (other-eval 'G-identity?))
 (code:line (other-P-identity? other-P-identity) (code:comment #,(green "true")))
 (code:line (other-G-identity? other-G-identity) (code:comment #,(green "true")))
 (code:line (equal? P-identity other-P-identity) (code:comment #,(red "alas:")))
 (code:line (equal? G-identity other-G-identity) (code:comment #,(red "alas:")))
 (code:line (P-identity? other-P-identity) (code:comment #,(red "alas:")))
 (code:line (G-identity? other-G-identity) (code:comment #,(red "alas:")))
 (code:line (other-P-identity? P-identity) (code:comment #,(red "alas:")))
 (code:line (other-G-identity? G-identity) (code:comment #,(red "alas:")))
 (code:comment "")
 (code:comment #,(list "Even " (nbr P-equal?) " and " (nbr G-equal?) " can go wrong:"))
 (code:comment "(with an error message that may be obscure, although it does")
 (code:comment " indicate the mixing of different structures of the same name)")
 (P-equal? P-identity other-P-identity)
 (G-equal? G-identity other-G-identity)]

@section[#:tag "H"]{Hash representation}

All objects described in this section are defined in module @nbhll["H.rkt" "H.rkt"].
The H-representation is used internally for operations like application,
@nber["composition" "composition"] and @nbrl[P-inverse "inversion"].
@red{Advice}: avoid explicit use of the H-representation.
Use the @nbsl["P" "P-representation"].
It represents @nber["R" "Rs"] by functions
and avoids multiple copies in memory of Hs, @nbsl["C" "Cs"] and
@nbsl["P" "Ps"] representing the same @nber["R" "R"]:
@nbsl["P" "Ps"] representing the same @nber["R" "R"]
are the same in the sense of @nbr[eq?].
@red{Warning}: this may not remain true after @nbsl["Cleanup" "cleanup"].
 
@note{@elemtag["inversion"]{
  In this document the word `@italic{inversion}' applies to bijections.
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
 When called with one argument, the normalized form of the argument is returned.}

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
@subsection{Symmetries of a square}

Number the vertices of a square anticlockwise starting left below with 0, 1, 2 and 3.
@nested[#:style 'inset (image "square.gif")]
Name the symmetries as follows:
@inset[
 @Tabular[(("name" "description")
           ("E" "identity")
           ("R" "anti clockwise rotation about 90°")
           ("R2" "anti clockwise rotation about 180°")
           ("R3" "anti clockwise rotation about 270°")
           ("Sv" "reflection in vertical center line")
           ("Sh" "reflection in horizontal center line")
           ("Sd0" "reflection in diagional 0-2")
           ("Sd1" "reflection in diagional 1-3"))
          #:sep (hspace 2)
          #:row-properties '((top-border bottom-border) ()()()()()()() bottom-border)]]

The whole group can be generated from a base of two elements, for example R and Sv.
The group is called ‘C4v’ because it has a fourfold axis of rotation (R)
with a vertical plane of reflection (Sv) assuming the square to be in a horizontal plane.
@Interaction*[
 (define R   (P '(0 1 2 3)))
 (define Sv  (P '((0 1) (2 3))))
 (define E   (P Sv Sv))
 (define R2  (P R R))
 (define R3  (P R R2))
 (define Sh  (P R2 Sv))
 (define Sd0 (P R Sh))
 (define Sd1 (P R2 Sd0))
 (define C4v-list (list E R R2 R3 Sv Sd0 Sh Sd1))
 (define names        '(E R R2 R3 Sv Sd0 Sh Sd1))
 (for-each set-P-name! C4v-list names)
 (P-print-by-name #t)]

The symmetries in  @nbsl["C" "C-representation"]:

@Interaction*[
 (for ((p (in-list C4v-list)))
   ((fmt "L3D N' : ' W/" 'cur) p (P->C p)))]

@tt{E} is the @nbr[P-identity]:

@Interaction*[(eq? E P-identity)]

Check that @tt{C4v-list} contains all symmetries as generated from base (R Sv) and those only:

@Interaction*[
 (define C4v (G R Sv))
 (equal? (P-sort C4v-list) (G->list C4v))]

Table of compositions:

@Interaction*[
 (apply (fmt "L5_##W/" 'cur)
   (sqr (length C4v-list))
   (length C4v-list)
   (for*/list
     ((p (in-list C4v-list))
      (q (in-list C4v-list)))
     (P p q)))]

Conjugation classes:

@Interaction*[
 (for-each writeln
   (sort 
     (for/list
       ((c (in-list (G-classes C4v))))
       (map P-name (sort (set->list c) symbol<? #:key P-name)))
     (λ (x y)
       (or (< (length x) (length y))
         (and (= (length x) (length y))
           (symbol<? (car x) (car y)))))))]

Subgroups:

@Interaction*[
 (define subgs
   (sort (G-subgroups C4v)
     (λ (x y) (< (G-order x) (G-order y)))))
 (code:comment "")
 (define-values (invariant variant)
   (partition (λ (x) (G-invariant-subg? x C4v)) subgs))
 (code:comment "")
 (define-syntax-rule (print-subgroups subgs)
   ((fmt "u#(xd/)" 'cur)
    (for/list ((sg (in-list subgs)))
      (sort (G->list sg) symbol<? #:key P-name))))
 (code:comment "")
 (print-subgroups invariant)
 (code:comment "")
 (print-subgroups variant)]

For example, {@tt{E Sv}}, {@tt{E Sh}}, {@tt{E Sd0}} and {@tt{E Sd1}}@(lb)
are not invariant under transformation @tt{R}:

@Interaction*[
 (for ((s (in-list (list Sv Sd0))))
   (printf "~s ≠ ~s~n" s (P R s (P-inverse R))))]

{@tt{E R2}} is an invariant subgroup. This implies@(lb)
that @tt{R2} commutes with all symmetries of the square:

@Interaction*[
 (for/and ((p (in-list C4v-list))) (P-commute? p R2))]
None of the symmetries other than @tt{E} and @tt{R2}@(lb)
commute with all symmetries of the square:

@Interaction*[
 (for/or ((p (in-list (remove* (list E R2) C4v-list))))
   (for/and ((q (in-list C4v-list)))
     (P-commute? p q)))]
@(reset-Interaction*)

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

@Interaction*[
 (define rotation (P '((0 1 2 3) (4 5 6 7))))
 (define reflection (P '((0 7) (1 6))))
 (define cube-symmetries (G rotation reflection))]

The following table maps each conjugation class to a description.

@Interaction*[
 (define conj-descr-table
   (make-hash
     (map
       (λ (entry) (cons (G-class (car entry) cube-symmetries) (cdr entry)))
       (list
         (cons (P '((0 1 2 3) (4 5 6 7)))
           "Rotation 90° or 270°, axis // to an edge.")
         (cons (P '((0 2) (1 3) (4 6) (5 7)))
           "Rotation 180°, axis // to an edge.")
         (cons (P '((0 1) (2 3) (4 5) (6 7)))
           "Reflection, plane // to a side.")
         (cons (P '((0 7) (1 6)))
           "Reflection in diagonal plane.")
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
           "Inversion-symmetry.")))))
 (code:comment "")
 (define (get-class-descr conj-class)
   (hash-ref conj-descr-table conj-class))]

Check that all conjugation classes are present in @tt{conj-descr-table}.

@Interaction*[
 (set=? (hash-keys conj-descr-table) (G-classes cube-symmetries))]

Procedure @tt{print-group-info} prints some information about group @tt{cube-symmetries}
or @tt{cube-rotations}. It does some tests too.

@Interaction*[
 (define (print-group-info g name print-classes?)
   (define conj-classes (sort (G-classes g) conj-class<?))
   (define g-order (G-order g))
   (printf " ~nInfo about group: ~a~n ~n" name)
   (printf "Order of the group: ~s~n" g-order)
   (printf "Number of conjugation classes: ~s~n" (length conj-classes))
   (code:comment "")
   (printf
     "Check: order of each element divisor of the order of the group? ~s~n"
     (for/and ((p (in-G g))) (divisor? (P-order p) g-order)))
   (code:comment "")
   (printf
     "Check: size of each conjugation class divisor of order of the group? ~s~n"
     (for/and ((conj-class (in-list conj-classes)))
       (divisor? (set-count conj-class) g-order)))
   (code:comment "")
   (printf " ~nThe conjugation classes are:~n")
   (code:comment "")
   (for ((conj-class (in-list conj-classes)))
     (printf " ~n~a~n" (get-class-descr conj-class))
     (printf "Order: ~s, class-size: ~s~n"
       (P-order (set-first conj-class))
       (set-count conj-class))
     (when print-classes?
       (for ((p (in-list (P-sort (set->list conj-class)))))
         (printf "~s~n" (P->C p))))))
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
   (zero? (modulo multiple divisor)))]
@Interaction*[
 (print-group-info cube-symmetries "cube-symmetries" #t)]
 
Subgroup consisting of rotations only.
Rotation and other-rotation are rotations about 90°
with intersecting axes perpendicular to each other.

@Interaction*[
 (define other-rotation '((0 1 5 4) (2 6 7 3)))
 (define cube-rotations (G rotation other-rotation))
 (print-group-info cube-rotations "cube-rotations" #f)]

@tt{cube-rotations} is an invariant subgroup of @tt{cube-symmetries}.

@Interaction*[
 (G-invariant-subg? cube-rotations cube-symmetries)]

Each conjugation class of the group of @tt{cube-rotations}@(lb)
also is a conjugation class of the group of all @tt{cube-symmetries}:

@Interaction*[
 (proper-subset?
   (G-classes cube-rotations)
   (G-classes cube-symmetries))]

The group of all @tt{cube-symmetries} has ten conjugation classes,
of which five coincide with the conjugation classes of subgroup @tt{cube-rotations}.
Elements of the same class have the same normalized cycle structure,
but distinct classes can have the same normalized cycle structure.
@note{In a @nbrl[G-symmetric]{symmetric} group
 every class has distinct normalized cycle structure.
 In other words, in a symmetric group
 two elements are conjugates of each other
 if and only if they have the same normalized cycle structure.}
In group @tt{cube-symmetries} the inversion-symmetry,
rotations about 180° and reflections in the planes
containing the center of the cube and parallel to a side of the cube
have the same normalized cycle structure, but form distinct conjugation classes.
The @nbr[P-identity] always is the only member of its class.

The inversion-symmetry @nbr[(P '((0 6) (1 7) (2 4) (3 5)))],
which does not occur in subgroup @element['tt "cube-rotations"], is lonesome too.
This implies that it commutes with all elements.
It maps each vertex to the one in opposit position with respect to the center of the cube.

Possibly you did not expect three-fold rotation axes as symmetries of a cube, but they are there.
In particular, @nber["composition" "composition"] of two rotations about 90° with intersecting
axes orthogonal to each other produces a rotation about 120°, for example:

@example/n[(P '((0 1 2 3) (4 5 6 7)) '((0 3 7 4) (1 2 6 5)))]

This is a rotation about 120° around axis 0-6.
Composition of this rotation with the inversion-symmetry,
which is not part of subgroup @element['tt "cube-rotations"], produces:

@example/n[(P (P '((1 3 4) (2 7 5))) (P '((0 6) (1 7) (2 4) (3 5))))]

This is a symmetry of order 6.
Let's check that the inversion-symmetry commutes with all symmetries of the cube:

@Interaction*[
 (define inversion-symmetry (P '((0 6) (1 7) (2 4) (3 5))))
 (for/and ((p (in-G cube-symmetries)))
   (P-commute? inversion-symmetry p))]

There are @nb{9×24 = 216} distinct minimal bases for the symmetries of the cube.
They can be grouped in 9 collections of symmetrically equivalent minimal bases,
each collection containing 24 bases.
Two minimal bases @nb{{a ...}} and @nb{{b ...}} are symmetrically equivalent
if the group contains @nb{a symmetry} x such that @nb{{ax ...} = {xb ...}}.
This is an equality of two sets:
@nb{the consecution} of @nb{the elements} between the curly brackets is irrelevant.
Symmetrically equivalent minimal bases have the same normalized cycle structure,
but not all bases with the same cycle structure are symmetrically equivalent.
For group @tt{cube-symmetries}
the number of collections of symmetrically equivalent minimal bases is one less
than the number of conjugation classes.
This is no coincidence,
because both the identity and the inversion symmetry form a conjugation class by itself.
They commute with all symmetries and are the only ones with this property.
In group @tt{cube-rotations} the number of collections of symmetrically equivalent minimal bases
is the same as the number of conjugation classes. It does not contain the inversion symmetry.
The following example shows the details:

@Interaction*[
 (define (print-G-info g)
   (define bases (G-bases g))
   (code:comment "")
   (define (base-eqv? a b)
     (for/or ((p (in-G g)))
       (equal? a
         (for/seteq ((c (in-set b))) (P (P-inverse p) c p)))))
   (code:comment "")
   (define base-collections (group-by values bases base-eqv?))
   (code:comment "")
   (printf " ~n")
   (printf "nr of minimal bases ~a~n" (length bases))
   (printf "nr of collections of symmetrically equivalent bases: ~a~n"
     (length base-collections))
   (code:comment "")
   (code:comment #,(list "Print one base of each collection in " (nbsl "C" "C-notation") "."))
   (code:comment "")
   (for
     ((base-collection (in-list (sort base-collections < #:key length)))
      (i (in-naturals 1)))
     (define base (set->list (car base-collection)))
     (define-values (x y)
       (apply values (map P->C base)))
     (printf " ~n~s: size: ~s: example: ~s and ~s~n"
       i (length base-collection) x y)
     (define a (get-class-descr (G-class (car base) g)))
     (define b (get-class-descr (G-class (cadr base) g)))
     (displayln a)
     (displayln b)
     (when (equal? a b) (displayln "Axes orthogonal to each other."))))
 (code:comment "")
 (print-G-info cube-symmetries)
 (code:comment "")
 (print-G-info cube-rotations)]

In the group of all @tt{cube-symmetries}, all collections of
symmetrically equivalent minimal bases have the same size.
This is not true for group @tt{cube-rotations}.
It has 108 distinct minimal bases
in five collections of symmetrically equivalent bases,
one collection of 12 bases and four collections of 24 bases.

The group of symmetries of the cube has 91 subgroups
of which 30 contain rotations only.

@Interaction*[
 (define all-subgs (G-subgroups cube-symmetries))
 (define rotation-subgs (apply set (G-subgroups cube-rotations)))
 (code:comment "")
 (define order-hash
   (for/fold ((h (hash))) ((subg (in-list all-subgs)))
     (define rotations? (set-member? rotation-subgs subg))
     (define order (G-order subg))
     (define invariant? (G-invariant-subg? subg cube-symmetries))
     (define key (list order rotations? invariant?))
     (hash-set h key (add1 (hash-ref h key 0)))))
 (code:comment "")
 (define (sort-entries entries) (sort entries entry<?))
 (code:comment "")
 (define (entry<? x y)
   (define-values (x-order x-rotations? x-invariant?)
     (apply values (car x)))
   (define-values (y-order y-rotations? y-invariant?)
     (apply values (car y)))
   (or (< x-order y-order)
     (and (= x-order y-order)
       (or (and x-rotations? (not y-rotations?))
         (and (eq? x-rotations? y-rotations?)
           x-invariant? (not y-invariant?))))))
 (code:comment "")
 (define header "order rotations-only? invariant? nr-of-subgroups~n")
 (define line   "────────────────────────────────────────────────~n")
 (define (~b x) (if x "yes" "no"))
 (code:comment "")
 (begin
   (printf line) 
   (printf "~s subgroups~n"
     (length all-subgs))
   (printf "of which ~s invariant~n"
     (apply +
       (map (curry hash-ref order-hash)
         (filter caddr (hash-keys order-hash)))))
   (printf "and ~s with rotations only~n"
     (set-count rotation-subgs))
   (printf line)
   (printf header)
   (printf line)
   (code:comment "")
   (for ((entry (in-list (sort-entries (hash->list order-hash)))))
     (define-values (n order rotations-only? invariant?)
       (apply values (cdr entry) (car entry)))
     ((fmt "R2W4X L16D L11D R2D/" 'cur)
      order
      (~b rotations-only?)
      (~b invariant?)
      n))
   (printf line))]

@(reset-Interaction*)

@subsection{The quaternion group}

@(define Q-comment
   (list
     "Q is (a group isomorphic to) the "
     (nbhl "https://en.wikipedia.org/wiki/Quaternion_group" "quaternion group") "."))

@Interaction*[
 (define i (P '((0 1 2 3) (4 5 6 7))))
 (define j (P '((0 4 2 6) (1 7 3 5))))
 (code:comment #,Q-comment)
 (define Q (G i j))
 (G-order Q)
 (define Q-classes (G-classes Q))
 (for ((p (in-G Q))) (printf "order = ~s, p = ~s~n" (P-order p) p))
 ((fmt 'cur "u#(w/)") Q-classes)]

In the quaternion group, make the following identifications:

@Interaction*[
 (define | i| i)
 (define | j| j)
 (define | k| (P | i| | j|))
 (define |-1| (P | i| | i|))
 (define | 1| (P |-1| |-1|))
 (define |-i| (P |-1| | i|))
 (define  -j  (P |-1| | j|))
 (define  -k  (P |-1| | k|))
 (define Ps    (list | 1| |-1| | i| |-i| | j|  -j  | k|  -k ))
 (define names (list " 1" "-1" " i" "-i" " j" "-j" " k" "-k"))
 (for ((p (in-list Ps)) (name (in-list names))) (set-P-name! p name))]

We have
@tt["ii=jj=kk=-1"],
@tt["ij=k"],
@tt["jk=i"]
and @tt["ki=j"].
With these @nber["composition" "compositions"]
all others are defined as shown in the following table:

@Interaction*[
 (P-print-by-name #t)
 ((fmt 'cur "U#(U#(WX)/)")
  (for/list ((p (in-list Ps)))
    (for/list ((q (in-list Ps)))
      (P p q))))]
         
Because @element['tt "1"] is the identity, it commutes with all elements.
@element['tt "-1"] commutes with all elements too,
which is verified by the fact that the second row of the table
equals the second column.
Notice that
@nb[@element['tt "ji=(-ii)ji=-i(ij)i=-iki=-ij=-k"]].@(lb)
Likewise @nb[@element['tt "kj=-i"]] and @nb[@element['tt "ik=-j"]].
The @nbrl[G-classes "conjugation classes"] are:

@nested[#:style 'inset]{@verbatim|{
 {1    }
 {   -1}
 {i, -i}
 {j, -j}
 {k, -k}}|}

We can verify this as follows:

@Interaction*[
 (for/and ((CLASS (in-list Q-classes)))
   (case (set-count CLASS)
     ((1)
      (define x (set-first CLASS))
      (or (P-identity? x) (eq? x |-1|)))
     ((2)
      (define-values (p q) (apply values (set->list CLASS)))
      (eq? (P |-1| p) q))
     (else #f)))]

Group @tt{Q} is not @nbrl[G-abelean?]{abelean},
but nevertheless all its subgroup are @nbrl[G-invariant-subg? "invariant"]:

@Interaction*[
 (define Q-subgs (G-subgroups Q))
 (begin
   (displayln "The subgroups are:")
   (for
     ((subg
        (in-list
          (sort Q-subgs < #:key G-order))))
     ((fmt "u#(dx)/" 'cur)
      (sort (G->list subg) string<? #:key P-name))))
 (not (G-abelean? Q))
 (for/and ((subg (in-list Q-subgs)))
   (G-invariant-subg? subg Q))]
@(reset-Interaction*)

@subsection[#:tag "C3v"]{Group C@↓{3v}}

C@↓{3v} is the group of symmetries of an equilateral triangle,
with subscript `3' indicating that it has a three-fold axis of rotation and
subscript `v' indicating it has a vertical plane of reflection containing
the axis of rotation and one of the vertices, in fact three such reflections
and assuming the triangle to be located in a horizontal plane.
Naming the vertices 0, 1 and 2 we can map the symmetries isomorphically onto @nber["R" "Rs"]:

@Interaction*[
 (define C3v (G '(0 1) '(0 1 2)))
 (G-print-table C3v)]
C@↓{3v} is isomorphic to S@↓{3}. In this case we even have:
@Interaction*[
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
Every row of the table of @nber["composition" "composition"]s of a group
is a distinct @nber["rearrangement" "rearrangement"] of the elements.
Likewise every column is a distinct @nber["rearrangement" "rearrangement"].
There@(-?)fore every element of a group @bold{X}
can be associated with one or two permutations of set @bold{X}:

@inset{
 ∀p∈@bold{X}: (q∈@bold{X}: → pq) is a permutation of set @bold{X} (column of p)@(lb)
 ∀p∈@bold{X}: (q∈@bold{X}: → qp) is a permutation of set @bold{X} (row of p)}

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

Procedure correspondence computes the
@nber["rearrangement" "rearrangements"]
of C@↓{3v} in the rows/columns of its composition table.
Use of @nbr[H->P] is @(red "discouraged"), @(green "but here it is useful").
@elemtag{H->P-example}

@Interaction*[
 (define in-C3v (in-G C3v))
 (code:comment "(correspondence g) -> (hasheq P? N? ... ...) (listof P?) (listof P?)")
 (code:comment "g : G?")
 (define (correspondence g)
   (define in-g (in-G g))
   (code:comment #,(list "h maps the Ps of g onto the " @nbsl["N"]{natural numbers}))
   (code:comment "0 up to but not including the order of g.")
   (define h (for/hasheq ((p in-g) (k (in-naturals))) (values p k)))
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
 (define-values (h rows columns) (correspondence C3v))]

Let's print map h:

@Interaction*[
 (for ((p in-C3v))
   ((fmt 'cur "L7W NX'is mapped onto'X W'.'/") (P->C p) (hash-ref h p)))]

Using this map, the composition table can be simplified by representing
the elements of C@↓{3v} by the natural numbers they are mapped onto.

@Interaction*[
 (for ((p in-C3v))
   (for ((q in-C3v)) (printf " ~s" (hash-ref h (P p q))))
   (newline))]

Let's show the correspondence of the elements of C@↓{3v}
to permutations of the set of C@↓{3v}
representing them by the @nber["C3v-table" "labels shown above"].

@Interaction*[
 (for ((p in-C3v) (row (in-list rows)))
   ((fmt 'cur "'   row of 'L7WN' corresponds to 'W/")
    (P->C p) (P->C row)))
 (code:comment "")
 (for ((p in-C3v) (column (in-list columns)))
   ((fmt 'cur "'column of 'L7WN' corresponds to 'W/")
    (P->C p) (P->C column)))]

Let's check that we have isomorphic groups here.

@Interaction*[
 (define row-group    (list->G rows))
 (define column-group (list->G columns))
 (and
   (G-isomorphism C3v    row-group)
   (G-isomorphism C3v column-group)
   #t)]
@(reset-Interaction*)

@subsection[#:tag "C3h"]{Group C@↓{3h}}

Group C@↓{3h} has a three-fold axis of rotation and a plane of reflection
perpendicular to the axis of rotation. The subscript `h' indicates that
with vertical axis of rotation, the plane of reflection is horizontal.
A minimal base of C@↓{3h} consists of one element only.
This implies that C@↓{3h} is circular and abelean.
There are two minimal bases (consisting of inverses of each other)
C@↓{3h} is isomorphic to the group of the natural numbers from 0 up to 6 (excluded),
0 as identity and addition modulo 6 as @nber["composition" "composition"].

@Interaction[
 (define rotation (P '(0 1 2) '(3 4 5)))
 (define reflection (P '(0 3) '(1 4) '(2 5)))
 (eq? (P rotation reflection) (P reflection rotation))
 (define C3h-base (P rotation reflection))
 (define C3h (G C3h-base))
 (G-order C3h)
 (G-abelean? C3h)
 (G-bases C3h)
 (define period (P-period C3h-base))
 (code:comment "")
 (define h
   (make-immutable-hasheq
     (for/list ((p (in-vector period)) (k (in-naturals)))
       (printf "~s : ~s~n" k p)
       (cons p k))))
 (code:comment "")
 (for ((p (in-vector period)))
   (for ((q (in-vector period)))
     (printf "~s " (hash-ref h (P p q))))
   (newline)) 
 (code:comment "")
 (define C6 (G (range 6)))
 (and (G-isomorphism C3h C6) #t)
 (define other-C3h (G '(0 1 2) '(3 4)))
 (and (G-isomorphism C3h other-C3h) #t)]

@bold{@larger{@larger{@larger{The end}}}}
@(collect-garbage)
