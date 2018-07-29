#lang racket

; By Jacob J. A. Koot
; Part of R.rkt. Documentation in R.scrbl.

(require (only-in typed/racket index?))

(provide
 (rename-out
  (exact-nonnegative-integer? N?)
  (exact-positive-integer? N+?)
  (exact-integer? Z?)))
