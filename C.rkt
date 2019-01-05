#lang racket

; By Jacob J. A. Koot
; Part of R.rkt. Documentation in R.scrbl.

;===================================================================================================

(require "H.rkt" "N.rkt")

(provide H->C C->H C? C-normalized? C-normalize C-transpositions C-identity? C-even?)

(define (C? x)
 (and (list? x)
  (or (null? x)
   (and (andmap N? x) (not (check-duplicates x)))
   (andmap C? x))))

(define (C-normalized? x) (and (C? x) (equal? (C-normalize x) x)))

(define (C-identity? c) (and (C? c) (null? (C-normalize c))))

(define (H->C h)
 (define keys (sort (hash-keys h) <))
 (if (null? keys) '()
  (for/fold
   ((c '())
    (done (set))
    #:result
    (cond
     ((null? c) '())
     ((> (length c) 1) (sort c single-C<?))
     (else (car c))))
   ((key (in-list keys)))
   (cond
    ((set-member? done key) (values c done))
    ((= (hash-ref h key key) key)
     (values c (set-add done key)))
    (else
     (define first key)
     (define next (hash-ref h first))
     (let single-cycle-loop ((next next) (reversed-single-C (list first)))
      (if (= next first)
       (values
        (cons (reverse reversed-single-C) c)
        (set-union (apply set reversed-single-C) done))
       (single-cycle-loop (hash-ref h next) (cons next reversed-single-C)))))))))

(define  (single-C<? c0 c1)
 (let ((a (length c0)) (b (length c1)))
  (or (< a b)
   (and (= a b) (< (car c0) (car c1))))))

(define (C->H c)
 (define (C-single->H c-single)
  (cond
   ((< (length c-single) 2) H-identity)
   (else
    (define first (car c))
    (for/fold ((h H-identity) (k (car c)) #:result (hash-set h k first))
              ((current (in-list (cdr c))))
     (values (hash-set h k current) current)))))
 (unless (C? c) (raise-argument-error 'C->H "C?" c))
 (cond
  ((null? c) H-identity)
  ((N? (car c)) (C-single->H c))
  (else (apply H-compose (map C->H c)))))

(define (C-normalize c)
 (unless (C? c) (raise-argument-error 'C-normalize "C?" c))
 (H->C (C->H c)))

(define (C-transpositions c)
 (define (C-single-transpositions c)
  (for/list ((a (in-list c)) (b (in-list (cdr c)))) (list (min a b) (max a b))))
 (define (C-transpositions c)
  (cond
   ((null? c) '())
   ((N? (car c)) (C-single-transpositions c))
   (else (apply append (map C-single-transpositions c)))))
 (C-transpositions (C-normalize c)))

(define (C-even? c) (even? (length (C-transpositions c))))

;===================================================================================================
