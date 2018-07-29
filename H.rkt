#lang racket

; By Jacob J. A. Koot
; Part of R.rkt. Documentation in R.scrbl.
; Advice: don't use this module explicitly.

;===================================================================================================
; A H is an immutable hasheqv representing a permutation.
;===================================================================================================

(require "N.rkt")

(provide H-identity H-identity? H-apply H-compose H-inverse H? H-restriction pseudo-H? H-normalize)

(define (H-normalize h)
 (for/hasheqv (((k v) (in-hash h)) #:when (not (= k v))) (values k v)))

(define (H-apply h k) (hash-ref h k k))

(define H-identity (make-immutable-hasheqv))

(define (H-identity? x) (equal? x H-identity))

(define (H? x)
 (and (pseudo-H? x)
  (for/and (((k v) (in-hash x))) (not (= k v)))))

(define (pseudo-H? x)
 (and (hash-eqv? x) (immutable? x)
  (let ((keys (hash-keys x)) (values (hash-values x)))
   (and
    (andmap N? keys)
    (andmap N? values)
    (equal? (sort (hash-keys x) <) (sort values <))))))

(define (H-compose . hs)
 (case (length hs)
  ((0) H-identity)
  ((1) (H-normalize (car hs)))
  (else
   (define reversed-hs (reverse hs))
   (for/fold ((h (make-immutable-hasheqv)))
             ((k (in-list (remove-duplicates (apply append (map hash-keys hs)) =))))
    (define v (for/fold ((k k)) ((h (in-list reversed-hs))) (H-apply h k)))
    (if (= v k) h (hash-set h k v))))))

(define (H-inverse h)
 (for/hasheqv (((k v) (in-hash (H-normalize h)))) (values v k)))

(define (H-restriction h)
 (define keys (hash-keys (H-normalize h)))
 (if (null? keys) 0 (add1 (apply max keys))))

;===================================================================================================
