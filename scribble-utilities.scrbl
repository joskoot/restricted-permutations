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
  "R.rkt"
  (for-label
   "R.rkt"
   racket
   (only-in typed/racket Setof Natural Sequenceof Index))
  (for-syntax racket))

@(provide lb ↑lb nb ignore nbsl nbsr nbhl nber nbrl nbr red green black
  eval-example example color-example example/n example-table
  Tabular minus -? note inset expt-1 ↑ ↓ ⇒ constr-style)

@(define lb linebreak)
@(define (↑lb) (list (↑ (hspace 1)) (lb)))
@(define nb nonbreaking)
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
@(define yellow (make-color-style "yellow"))

@(define example-ns (make-base-namespace))

@(parameterize ((current-namespace example-ns))
  (namespace-require 'racket)
  (namespace-require '"R.rkt"))

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
@(define ⇒ @larger{⇒})

@(define constr-style
 (nbhl "https://docs.racket-lang.org/drracket/output-syntax.html" "constructor style"))
        
aap noot mies