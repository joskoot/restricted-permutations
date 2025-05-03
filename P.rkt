#lang racket

; Part of R.rkt. Documentation in R.scrbl.
; By Jacob J. A. Koot

;===================================================================================================

(require "H.rkt" "C.rkt" "N.rkt")
(provide P-identity P? P-period P-order P-expt P-inverse P-even? P->C P<? P-sort P)
(provide P-clear-hashes P-hashes-count P-equal? P-identity? P-restriction P-non-fixed-points)
(provide P-fixed-point? P->H H->P P-commute? P-name set-P-name! P-print-by-name)

(define (P->C p)                  ; This definition comes before that of P-write because
  (or (P-C-field p)                ; the debugger can be caught in an infinite sequence of
    (let ((c (H->C (P-H-field p)))) ; exceptions being raised when trying to print a P:
      (set-P-C-field! p c)           ; (P->C: undefined; cannot reference before def ...)
      c)))

(define (P-apply p k) (H-apply (P-H-field p) k))
(define P-hash (make-hash))
(define P-compose-hash (make-hash))
(define P<?-hash (make-hash))
(define P-print-by-name (make-parameter #f (λ (x) (and x #t)) 'P-print-by-name))

(define (P-write p port mode)
  (define name (P-name p))
  (if (and name (P-print-by-name))
    (fprintf port "~a" name)
    (fprintf port "(P '~s)" (P->C p))))

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
    (name          #:auto #:mutable)
    (order-field   #:auto #:mutable)
    (period-field  #:auto #:mutable)  ; Vector of powers of Ps in order of the exponent.
    (inverse-field #:auto #:mutable)  ; Inverse of P
    (even-field    #:auto #:mutable)) ; 'even or 'odd (avoiding confusion with the auto-value)
  #:auto-value #f                     ; Nevertheless P-even? always returns a boolean.
  #:property prop:custom-write P-write
  #:property prop:procedure P-apply
  #:constructor-name P-constr
  #:omit-define-syntaxes)

(define P->H (procedure-rename P-H-field 'P->H))

(define (H->P h)
  (define hh (H-normalize h))
  (hash-ref! P-hash hh (λ () (P-constr hh))))

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

(define (P-commute? p q) (eq? (P p q) (P q p)))

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
               (order (or order (P-order p)))
               (inverted-h (H-inverse h))
               (inverted-p (hash-ref! P-hash inverted-h (λ () (P-constr inverted-h)))))
            (set-P-inverse-field! p inverted-p)
            (set-P-inverse-field! inverted-p p)
            (set-P-order-field! inverted-p order)
            inverted-p))))))

(define (P-order p/c)
  (let ((p (P/C->P p/c)))
    (or (P-order-field p)
      (let*
          ((c (P->C p))
           (order
             (cond
               ((null? c) 1)
               ((N? (car c)) (length c))
               (else (apply lcm (map length c))))))
        (set-P-order-field! p order)
        order))))

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
        (and (not (P-equal? p0 p1)) ; using eq? may cause an infite loop.
          (let ((order0 (P-order p0)) (order1 (P-order p1)))
            (or (< order0 order1)
              (and (= order0 order1)
                (let ((even0 (P-even? p0)) (even1 (P-even? p1)))
                  (or (and even0 (not even1))
                    (and (eqv? even0 even1)
                      (let loop ((k 0))
                        ; This loop always terminates because p0 and p1 are not P-equal.
                        (let ((e0 (p0 k)) (e1 (p1 k)))
                          (or (< e0 e1) (and (= e0 e1) (loop (add1 k)))))))))))))))))

(define (P-equal? p0 p1)
  (or (eq? p0 p1)
    (equal? (P-H-field p0) (P-H-field p1))))

(define (P-restriction p) (H-restriction (P-H-field p)))
(define (P-non-fixed-points p) (sort (hash-keys (P-H-field p)) <))
(define (P-fixed-point? p k) (= (p k) k))

(define  (single-C<? c0 c1)
  (let ((a (length c0)) (b (length c1)))
    (or (< a b)
      (and (= a b) (< (car c0) (car c1))))))

;===================================================================================================

