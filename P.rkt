#lang racket

; Part of R.rkt. Documentation in R.scrbl.
; By Jacob J. A. Koot

;===================================================================================================

(require "H.rkt" "C.rkt" "N.rkt" (only-in racket/generator generator yield))
(provide P-identity P? P-period P-order P-expt P-inverse P-even? P->C P<? P-sort P)
(provide (rename-out (P P-compose)))
(provide P-clear-hashes P-hashes-count P-equal? P-identity? P-restriction P-non-fixed-points)
(provide P-fixed-point? in-R P->H H->P)

(define (P->C p)                  ; This definition comes before that of P-write because
 (or (P-C-field p)                ; the debugger can be caught in an infinite sequence of
  (let ((c (H->C (P-H-field p)))) ; exceptions being raised when trying to print a P:
   (set-P-C-field! p c)           ; (P->C: undefined; cannot reference before def ...)
   c)))

(define (P-apply p k) (H-apply (P-H-field p) k))
(define P-hash (make-hash))
(define P-compose-hash (make-hash))
(define P<?-hash (make-hash))

(define (P-write p port mode)
 (let ((c (P->C p)))
  (if (null? c) (write 'P-identity port)
   (fprintf port "(P '~s)" c))))

(define (P-clear-hashes)
 (hash-clear! P-hash)
 (hash-clear! P-compose-hash)
 (hash-clear! P<?-hash)
 (hash-set! P-hash H-identity P-identity))

(define (P-hashes-count)
 (+
  (hash-count P-hash)
  (hash-count P-compose-hash)
  (hash-count P<?-hash)))

(struct P
 (H-field
  (C-field       #:auto #:mutable)
  (order-field   #:auto #:mutable)
  (period-field  #:auto #:mutable)  ; Vector of powers of Ps in order of the exponent.
  (inverse-field #:auto #:mutable)  ; Inverse of P
  (even-field    #:auto #:mutable)) ; 'even or 'odd (avoiding confusion with the auto-value)
 #:auto-value #f                    ; Nevertheless P-even? always returns a boolean.
 #:property prop:custom-write P-write
 #:property prop:procedure P-apply
 #:constructor-name P-constr
 #:omit-define-syntaxes)

(define P->H (procedure-rename P-H-field 'P->H))

(define (H->P h)
 (define hh (H-normalize h))
 (hash-ref! P-hash hh (λ ()(P-constr hh))))

(define P-identity
 (let ((P-identity (P-constr H-identity)))
  (hash-set! P-hash H-identity P-identity)
  P-identity))

(define (P-identity? x) (eq? x P-identity))

(define (C->P . cs)
 (for ((c (in-list cs)))
  (unless (C? c)
   (error 'C->P "all arguments must be Cs, but given: ~s" c)))
 (let ((h (C->H cs)))
  (hash-ref! P-hash h (λ () (P-constr h)))))

(define (P . p/cs)
 (let ((ps (map P/C->P p/cs)))
  (hash-ref! P-compose-hash ps
   (λ ()
    (let ((h (apply H-compose (map P-H-field ps))))
     (hash-ref! P-hash h (λ () (P-constr h))))))))

(define (P/C->P p/c) (if (P? p/c) (hash-ref! P-hash (P-H-field p/c) (λ () p/c)) (C->P p/c)))

(define (P-expt p/c k)
 (let ((p (P/C->P p/c)))
  (vector-ref (P-period p) (modulo k (P-order p)))))

(define (P-inverse p/c)
 (let ((p (P/C->P p/c)))
  (or (P-inverse-field p)
   (let ((order (P-order-field p)) (period (P-period-field p)))
    (or
     (and order period
      (let ((inverse (vector-ref period (sub1 order))))
       (set-P-inverse-field! p inverse)
       inverse))
     (let*
      ((h (P-H-field p))
       (order (hash-count h))
       (inverted-h (H-inverse h))
       (inverted-p (hash-ref! P-hash inverted-h (λ () (P-constr inverted-h)))))
      (set-P-inverse-field! p inverted-p)
      (set-P-inverse-field! inverted-p p)
      (set-P-order-field! p order)
      (set-P-order-field! inverted-p order)
      inverted-p))))))

(define (P-order p/c)
 (let ((p (P/C->P p/c)))
  (or (P-order-field p))
   (let*
    ((c (P->C p))
     (order
      (cond
       ((null? c) 1)
       ((N? (car c)) (length c))
       (else (apply lcm (map length c))))))
    (set-P-order-field! p order)
    order)))

(define (P-period p/c)
 (define (P-period p)
  (apply vector-immutable
   (cons P-identity
    (let loop ((current-p p))
     (if (eq? current-p P-identity) '()
      (cons current-p (loop (P p current-p))))))))
 (let ((p (P/C->P p/c)))
  (or (P-period-field p)
   (let* ((period (P-period p)) (order (vector-length period)))
    (set-P-order-field! p order)
    (set-P-period-field! p period)
    period))))

(define (P-even? p/c)
 (let* ((p (P/C->P p/c)) (parity (P-even-field p)))
  (case parity
   ((even) #t)
   ((odd) #f)
   (else         
    (let*
     ((c (H->C (P-H-field p)))
      (parity
       (cond
        ((null? c))
        ((N? (car c)) (odd? (length c)))
        (else (even? (apply + (length c) (map length c)))))))
     (set-P-even-field! p (if parity 'even 'odd))
     parity)))))

(define (P-sort p/cs) (sort (map P/C->P p/cs) P<?))

(define (P<? p/c0 p/c1)
 (let ((p0 (P/C->P p/c0)) (p1 (P/C->P p/c1)))
  (hash-ref! P<?-hash (cons p0 p1)
   (λ () ; use P-equal? in stead of eq?, because after cleanup
    (and (not (P-equal? p0 p1)) ; using eq? may cause an infite loop after cleanup.
     (let ((even0 (P-even? p0)) (even1 (P-even? p1)))
      (or (and even0 (not even1))
       (and (eqv? even0 even1)
        (let ((order0 (P-order p0)) (order1 (P-order p1)))
         (or (< order0 order1)
          (and (= order0 order1)
           (let loop ((k 0)) ; This loop always terminates because p0 and p1 are not P-equal.
            (let ((e0 (p0 k)) (e1 (p1 k)))
             (or (< e0 e1) (and (= e0 e1) (loop (add1 k)))))))))))))))))

(define (P-equal? p0 p1)
 (or (eq? p0 p1)
  (equal? (P-H-field p0) (P-H-field p1))))

(define (P-restriction p) (H-restriction (P-H-field p)))
(define (P-non-fixed-points p) (sort (hash-keys (P-H-field p)) <))
(define (P-fixed-point? p k) (= (p k) k))

(define (make-P-generator)
 (generator ()
  (yield P-identity)
  (yield (C->P '(0 1)))
  (let loop ((m 3) (lst1 '(0 1 2)) (lst2 '(0 1)))
   (for ((k (in-list lst2)))
    (define list-k (list k))
    (for ((lst (in-permutations (remove k lst1))))
     (yield (C->P (V->C (apply vector (append lst list-k)))))))
   (loop (add1 m) (cons m lst1) lst1))))

(define (in-R (max-restriction 256))
 (when (> max-restriction 256)
  (error 'in-R "~s too big max-restriction (max is 256)" max-restriction))
 (in-producer (make-P-generator) (λ (p) (> (P-restriction p) max-restriction))))

(define (V->C v)
 (let ((n (vector-length v)))
  (if (zero? n) '()
   (let cycle-loop ((k 0) (c '()) (done (set)))
     (cond
      ((= k n)
       (cond
        ((null? c) '())
        ((> (length c) 1) (sort c single-C<?))
        (else (car c))))
      ((set-member? done k) (cycle-loop (add1 k) c done))
      (else
       (define first (vector-ref v k))
       (if (= first k) (cycle-loop (add1 k) c done)
        (let single-cycle-loop ((next (vector-ref v first)) (reversed-single-C (list first k)))
         (if (= next k)
          (cycle-loop
           (add1 k)
           (cons (reverse reversed-single-C) c)
           (set-union (apply set reversed-single-C) done))
          (single-cycle-loop (vector-ref v next) (cons next reversed-single-C)))))))))))

(define  (single-C<? c0 c1)
 (let ((a (length c0)) (b (length c1)))
  (or (< a b)
   (and (= a b) (< (car c0) (car c1))))))

;===================================================================================================
