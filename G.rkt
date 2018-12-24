#lang racket

; Part of R.rkt. Documentation in R.scrbl cq R.html.
; By Jacob J. A. Koot

;===================================================================================================

(require "P.rkt" (only-in "C.rkt" H->C))
(require (only-in math/number-theory factorial))

(provide G-identity G-identity? G? G G-symmetric G-abelean? G-bases G-base G-order G-equal?
 G-subg? G-proper-subg? G-invariant-subg? G-even-subg G-class G-classes G->list list->G in-G
 G-member? G-clear-hashes G-hashes-count G-isomorphism G-table G-print-table G-subgroups
 (rename-out (G-abelean? G-commutative?)))

(define (G-print g port mode)
 (fprintf port "~s"
  (if (= (set-count (G-set g)) 1) 'G-identity
   (cons 'G (G->list g)))))

(struct G (set)
 #:constructor-name make-G
 #:omit-define-syntaxes
 #:property prop:custom-write G-print)

(define (G-constr s) (hash-ref! G-hash s (λ () (make-G s))))
(define G-hash (make-hash))
(define G-identity (G-constr (seteq P-identity)))
(define (G-identity? x) (eq? x G-identity))

(define (G-clear-hashes)
 (hash-clear! G-hash)
 (hash-set! G-hash G-identity G-identity))

(define (G-hashes-count) (hash-count G-hash))

(define (G . base)
 (define ps (remove-duplicates (map P base) P-equal?))
 (define max-order (factorial (length (remove-duplicates (flatten (map P->C ps)) =))))
 (define (*set-union . x) (if (null? x) (seteq) (apply set-union x)))
 (define new
  (apply *set-union
   (for/list ((p (in-list ps))) (apply seteq (cdr (vector->list (P-period p)))))))
 (let loop ((old (seteq)) (new new))
  (if (set-empty? new) (G-constr (set-add old P-identity))
   (let ((old+new (set-union new old)))
    (if (= (set-count old+new) (sub1 max-order))
     (G-constr (set-add old+new P-identity))
     (loop old+new
      (let loop1 ((p old+new) (r (seteq)))
       (cond
        ((set-empty? p) r)
        ((= (+ (set-count old+new) (set-count r)) (sub1 max-order)) r)
        (else
         (let loop2 ((q new) (r r))
          (cond
           ((set-empty? q) (loop1 (set-rest p) r))
           ((= (+ (set-count old+new) (set-count r)) (sub1 max-order)) r)
           (else
            (let loop3
             ((pq (cdr (vector->list (P-period (P (set-first p) (set-first q)))))) (r r))
             (cond
              ((null? pq) (loop2 (set-rest q) r))
              ((= (+ (set-count old+new) (set-count r)) (sub1 max-order)) r)
              ((or (set-member? old+new (car pq)) (set-member? r (car pq))) (loop3 (cdr pq) r))
              (else (loop3 (cdr pq) (set-add r (car pq))))))))))))))))))

(define (G->list g) (P-sort (set->list (G-set g))))

(define (list->G lst)
 (let ((s (list->seteq lst)))
  (hash-ref! G-hash s
   (λ ()
    (if (G-set? s) (G-constr s)
     (error 'list->G "the argument does not correspond to a group:~n~s" lst))))))

(define (G-set? x)
 (or (hash-has-key? G-hash x)
  (and (set-eq? x) (not (set-mutable? x))
   (for/and ((p (in-set x))) (P? p))
   (for*/and ((p0 (in-set x)) (p1 (in-set x))) (set-member? x (P p0 p1))))))

(define no-offset (gensym 'no-offset))

(define (G-symmetric n (offset no-offset))
 (cond
  ((and
    (list? n)
    (eq? offset no-offset)
    (andmap exact-nonnegative-integer? n))
   (G-symmetric-help (remove-duplicates n =)))
  ((and
    (exact-nonnegative-integer? n)
    (eq? offset no-offset))
   (G-symmetric-help (range 0 n)))
  ((and
    (exact-nonnegative-integer? n)
    (exact-nonnegative-integer? offset))
   (G-symmetric-help (range offset (+ n offset))))
  (else
   (if (eq? offset no-offset)
    (error 'G-symmetric "incorrect argument ~s" n)
    (error 'G-symmetric "incorrect arguments ~s ~s" n offset)))))

(define (G-symmetric-help lst)
 (cond
  ((< (length lst) 2) G-identity)
  (else
   (G-constr
    (for/seteq ((x (in-permutations lst)))
     (H->P (make-immutable-hasheq (map cons lst x))))))))

(define (G-abelean? g)
 (for*/and ((a (in-set (G-set g))) (b (in-set (G-set g))))
  (eq? (P a b) (P b a))))

(define (G-bases g)
 (define Ps (set->list (set-remove (G-set g) G-identity)))
 (let loop ((k 1))
  (define bases
   (for/list ((base (in-combinations Ps k)) #:when (eq? (apply G base) g))
    (apply seteq base)))
  (if (null? bases) (loop (add1 k)) bases)))

(define (G-base g)
 (define Ps (set->list (set-remove (G-set g) G-identity)))
 (let/ec ec
  (let loop ((k 1))
   (for/list ((base (in-combinations Ps k)))
    (when (eq? (apply G base) g) (ec (apply seteq base))))
  (loop (add1 k)))))

(define (G-order g) (set-count (G-set g)))
(define (G-subg? g0 g1) (subset? (G-set g0) (G-set g1)))

(define (G-subgroups g)
 (define n (set-count (G-base g)))
 (cons G-identity
  (set->list
   (for*/seteq ((k (in-range 1 (add1 n))) (base (in-combinations (cdr (G->list g)) k)))
    (apply G base)))))

(define (G-proper-subg? g0 g1)
 (and (not (eq? g0 G-identity)) (proper-subset? (G-set g0) (G-set g1))))

(define (G-invariant-subg? g0 g1)
 (or (eq? g0 g1) (eq? g0 G-identity)
  (and (G-subg? g0 g1)
   (for*/and ((p1 (in-set (G-set g1))))
    (equal? (for/seteq ((p0 (in-set (G-set g0)))) (P p0 p1))
            (for/seteq ((p0 (in-set (G-set g0)))) (P (P-inverse p1) p0)))))))

(define (G-even-subg g) (G-constr (for/seteq ((p (in-G g)) #:when (P-even? p)) p)))

(define (G-class p g)
 (if (G-member? p g)
  (for/seteq ((q (in-set (G-set g)))) (P q p (P-inverse q)))
  (seteq)))

(define (G-classes g)
 (for/fold
  ((classes '()) (done (seteq)) #:result classes)
  ((p (in-G g)))
  (cond
   ((set-member? done p) (values classes done))
   (else (define class (G-class p g))
    (values (cons class classes) (set-union done class))))))

(define (G-equal? g0 g1)
 (or (eq? g0 g1)
  (let ((a (G->list g0)) (b (G->list g1)))
   (and (= (length a) (length b))
    (andmap P-equal? a b)))))

(define (G-isomorphism g0 g1 (name0 'no-name) (name1 'no-name))
 (cond
  ((not (= (G-order g0) (G-order g1))) #f)
  (else
   (define (make-prop-hash g)
    (define hash (make-hash))
    (define (properties p)
     (list (P-order p) (set-count (G-class p g))))
    (for ((p (in-set (G-set g))))
     (define props (properties p))
     (hash-set! hash props (cons p (hash-ref hash props '()))))
    (values hash (apply set (hash-keys hash))))
   (define-values (hash0 keys0) (make-prop-hash g0))
   (define-values (hash1 keys1) (make-prop-hash g1))
   (define (make-iso hash)
    (define hsah
     (make-immutable-hasheq (hash-map hash (λ (k v) (cons v k)))))
    (list
     (procedure-rename
      (λ (p)
       (hash-ref hash p
        (λ () (error name0 "arg ~s not in domain of this isomorphism" p)))) name0)
     (procedure-rename
      (λ (p)
       (hash-ref hsah p
        (λ () (error name1 "arg ~s not in domain of this isomorphism" p)))) name1)))
   (cond
    ((not (equal? keys0 keys1)) #f)
    (else
     (define keys (set->list keys0))
     (define h0 (apply append (for/list ((key (in-list keys))) (hash-ref hash0 key))))
     (define samples1-list
      (apply cartesian-product
       (for/list ((key (in-list keys))) (permutations (hash-ref hash1 key)))))
     (let loop ((samples1-list samples1-list))
      (and (pair? samples1-list)
       (let ((h1 (apply append (car samples1-list))))
        (define h0->1 (make-immutable-hasheq (map cons h0 h1)))
        (or
         (and
          (for*/and ((p (in-list h0)) (q (in-list h0)))
           (eq?
            (hash-ref h0->1 (P p q))
            (P (hash-ref h0->1 p) (P (hash-ref h0->1 q)))))
          (make-iso h0->1))
         (loop (cdr samples1-list)))))))))))

(define (in-G g) (in-list (G->list g)))
(define (G-member? p g) (set-member? (G-set g) (P p)))

(define (G-print-table g (port (current-output-port)))
 (define in-g (in-G g))
 (define cs (map (compose (curry format "~s") P->C) (G->list g)))
 (define column-width (add1 (apply max (map string-length cs))))
 (define (pad pq) (~s #:width column-width (P->C pq)))
 (for ((p in-g))
  (for ((q in-g)) (fprintf port "~a" (pad (P p q))))
  (newline port)))

(define-syntax-rule (for/immutable-vector x body ...)
 (vector->immutable-vector (for/vector x body ...)))

(define (G-table g)
 (define in-g (in-G g))
 (for/immutable-vector ((p (in-G g))) (for/immutable-vector ((q in-g)) (P p q))))

;===================================================================================================
