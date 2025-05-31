#lang racket

; By Jacob J. A. Koot
; Documentation in R.scrbl.

(require "H.rkt" "C.rkt" "P.rkt" "G.rkt" "N.rkt")

(provide
  (all-from-out "N.rkt")
  (all-from-out "H.rkt")
  (all-from-out "C.rkt")
  (except-out (all-from-out "P.rkt") P-clear-hashes P-hashes-count)
  (except-out (all-from-out "G.rkt") G-clear-hashes G-hashes-count)
  R-clear-hashes R-hashes-count)

(print-as-expression #f)

(define (R-clear-hashes)
  (G-clear-hashes)
  (P-clear-hashes))

(define (R-hashes-count)
  (+
    (G-hashes-count)
    (P-hashes-count)))

