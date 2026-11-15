#lang racket

(require "R.rkt" format/fmt test/test)

(test 1 ((C-normalize '(1 0))) '((0 1)))
(test 2 ((C-normalize '(1 2 0))) '((0 1 2)))
(test 3 ((C-normalize '((1 2) (0 3)))) '(((0 3) (1 2))))
(test 4 ((C-normalize '((0 2) (0 1)))) '((0 1 2)))
(test 5 ((C-normalize '((0 1) (0 2)))) '((0 2 1)))
(test 6 ((C-normalize '((0 1 2) (0 1))))'((0 2)))
(test 7 ((C-normalize '((0 1 2) (0 2)))) '((1 2)))
(test 8 ((C-normalize '((0 1 2) (1 2)))) '((0 1)))
(test 9 ((C-normalize '((0 1) (0 1 2) (0 1)))) '((0 2 1)))
(test 10 ((C-normalize '((0 1) (1 2) (2 3)))) '((0 1 2 3)))
(test 11 ((C-normalize '(((0 1) (1 2)) (2 3)))) '((0 1 2 3)))
(test 12 ((C-normalize '((0 1) ((1 2) (2 3))))) '((0 1 2 3)))
(test 13 ((C-normalize '((() () ())))) '(()))
(test 14 ((C-normalize '(((99999999))))) '(()))
(test 15 ((C-normalize '((1) (2) (3)))) '(()))
(test 16 ((C-normalize '((0 1) (0 1)))) '(()))
(test 17 ((C-normalize '((4 5 6) (1 2 3) (7 8)))) '(((7 8) (1 2 3) (4 5 6))))
(test 18 ((C-transpositions '())) '(()))
(test 19 ((C-transpositions '(0 1))) '(((0 1))))
(test 20 ((C-transpositions '(0 1 2))) '(((0 1) (1 2))))
(test 21 ((C-transpositions '(2 1 0))) '(((0 2) (1 2))))
(test 22 ((C-transpositions '(0 1 2 3))) '(((0 1) (1 2) (2 3))))
(test 23 ((C-transpositions '(2 3 4 0 1))) '(((0 1) (1 2) (2 3) (3 4))))
(test 24 ((C-transpositions '((0 1) (2 3)))) '(((0 1) (2 3))))
(test 25 ((C-transpositions '((0 1) (0 1)))) '(()))
(test 26 ((C-transpositions '((0 1 2) (3 4 5)))) '(((0 1) (1 2) (3 4) (4 5))))
(test 27 ((C-transpositions '((3 4 5) (0 1 2)))) '(((0 1) (1 2) (3 4) (4 5))))

(test 28
  ((for/and ((n (in-range 5)))
     (define Sn (G-symmetric n))
     (G-invariant-subg? (G-even-subg Sn) Sn)))
  '(#t))

(test 29
  ((for/and ((p (in-G (G-symmetric 4))))
     (define c (P->C p))
     (define c-inverse (P->C (P-inverse p)))
     (eq? (C-even? c) (C-even? c-inverse))))
  '(#t))

(test 30
  ((define in-g (in-list (map P->C (G->list (G-symmetric 4)))))
   (define (conjugates? x y) (for/or ((z in-g)) (eq? (P x z) (P z y))))
   (for*/and ((x in-g) (y in-g) #:when (conjugates? x y))
     (eq? (C-even? x) (C-even? y))))
  '(#t))

(test 31
  ((define p (P '((0 2) (3 4 5))))
   (define q (P-inverse p))
   (and ; true
     (eq? (P-inverse p) q)
     (eq? (P-inverse q) p)
     (eq? (P p q) P-identity)
     (eq? (P q p) P-identity)))
  '(#t))

(test 32
  ((define in-S4 (in-G (G-symmetric 4)))
   (for*/and ((a in-S4) (b in-S4) (c in-S4)) ; true
     (define x (P a (P b c)))
     (define y (P (P a b) c))
     (define z (P a b c))
     (and (eq? x z) (eq? y z) (eq? x y))))
  '(#t))

(test 33
  ((for/and ((n (in-range 5))) ; true
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
         (<= 0 (P-restriction qp) max-restriction)))))
  '(#t))

(test 34
  ((define p (P '((1 2) (3 4))))
   (define q (P '( 1 2   3 4)))
   (P-set-name! p 'p)
   (P-set-name! q 'q)
   (P-print-by-name #t)  
   (define (restriction-of-compositions-of p q)
     (define (restriction-of-composition p q)
       (define pq (P p q))
       (printf "~s~s = ~s with restriction ~s~n"
         p q pq (P-restriction pq)))
     (restriction-of-composition p q)
     (restriction-of-composition q p))
   (restriction-of-compositions-of p q))
  #f
  #:output
  "pq = (P '(2 4)) with restriction 5
   qp = (P '(1 3)) with restriction 4")

(test  35
  ((define a (P '(0 1 2)))
   (define b (P '(1 2 3)))
   (define c (P '(2 3 4)))
   (eq? ; true
     (P (P a b) c)
     (P a (P b c))))
  '(#t))

(test 36
  ((define a (P '(0 1 2)))
   (define b (P '(1 2 3)))
   (define c (P '(2 3 4)))
   (eq? ; true
     (P-inverse (P a b c))
     (P (P-inverse c) (P-inverse b) (P-inverse a))))
  '(#t))

(test 37
  ((P-set-name! P-identity 'E)
   (P-print-by-name #f) (writeln P-identity)
   (P '())
   (P-print-by-name #t) (writeln P-identity)
   (P-remove-name! P-identity)
   (P-print-by-name #t) (writeln P-identity))
  #f
  #:output "(P '()) E (P '())")

(test 38
  ((define a (P '(0 1)))
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
       (P a b c))))
  #f
  #:output "
                         () has order  1
                      (0 1) has order  2
                    (2 3 4) has order  3
                (5 6 7 8 9) has order  5
            ((0 1) (2 3 4)) has order  6
        ((0 1) (5 6 7 8 9)) has order 10
      ((2 3 4) (5 6 7 8 9)) has order 15
((0 1) (2 3 4) (5 6 7 8 9)) has order 30")

(test 39
  ((for/and ((p (in-G (G-symmetric 4)))) ; true
     (define period (P-period p))
     (define order (P-order p))
     (and
       (P-identity? (vector-ref period 0))
       (for/and ((k (in-range 1 order)))
         (eq?
           (vector-ref period (- order k))
           (P-inverse (vector-ref period k)))))))
  '(#t))

(test 40
  ((define p (P '(0 1) '(3 4 5)))
   (writeln (P-order p))
   (define in-exponents (in-range -10 10))
   (for*/and ((k in-exponents) (m in-exponents))
     (and
       (eq? (P-expt (P-expt p k) m)       (P-expt p (* k m)))
       (eq? (P (P-expt p k) (P-expt p m)) (P-expt p (+ k m))))))
  '(#t)
  #:output "6")

(test 41
  ((define S4 (G-symmetric 4))
   (G-order S4)
   24
   (for/and ((p (in-G S4))) ; true
     (define q (P-inverse p))
     (and
       (P-identity? (P q p))
       (P-identity? (P p q))
       (equal? (P-non-fixed-points p) (P-non-fixed-points q))
       (=      (P-order            p) (P-order            q))
       (=      (P-restriction      p) (P-restriction      q))
       (eq?    (P-even?            p) (P-even?            q)))))
  '(#t))

(test 42
  ((define in-S4 (in-G (G-symmetric 4)))
   (for*/and ((a in-S4) (b in-S4)) ; true
     (eq?
       (P-inverse (P a b))
       (P (P-inverse b) (P-inverse a)))))
  '(#t))

(test 43
  ((and
     (P-even? P-identity)
     (not (P-even? (P '(0 1))))
     (P-even? (P '(0 1) '(2 3)))
     (P-even? (P '(0 1) '(1 2)))
     (not (P-even? (P '(0 1) '(1 2) '(1 0))))
     (P-even? (P '(0 1 2)))
     (eq? (P '(0 1 2)) (P '(0 2) '(0 1)))
     (not (P-even? (P '(0 2 4 6))))
     (eq? (P '(0 2 4 6)) (P '(0 6) '(0 4) '(0 2)))))
  '(#t))

(test 44
  ((random-seed 1)
   (define S3-list0 (G->list (G-symmetric 3))) ; S3-list0 is sorted.
   (R-clear-hashes) ; Does not disturb procedure P-sort
   (define S3-list1 (G->list (G-symmetric 3))) ; S3-list1 is sorted.
   (define in-rearrangements in-permutations) ; See note below.
   (for/and ((rearranged-S3-list1 (in-rearrangements S3-list1))) ; true
     (define sorted-rearranged-S3-list1 (P-sort rearranged-S3-list1))
     (and
       (andmap P-equal? S3-list0 sorted-rearranged-S3-list1)
       (eq? (car S3-list0) (car sorted-rearranged-S3-list1))
       (not
         (ormap equal?
           (cdr S3-list0)
           (cdr sorted-rearranged-S3-list1))))))
  '(#t))

(test 45 ((P-non-fixed-points P-identity)) '(()))
(test 46 ((P-non-fixed-points (P '(5 6) '(0 1 2)))) '((0 1 2 5 6)))

(test 47
  ((define in-S4 (in-G (G-symmetric 4)))
   (for/and ((p in-S4)) ; true
     (define nfps (P-non-fixed-points p))
     (and
       (equal? nfps (sort (map p nfps) <))
       (equal? nfps (P-non-fixed-points (P-inverse p))))))
  '(#t))

(test 48 ((write (G))) #f #:output "(G (P '()))")
(test 49 ((write (G P-identity))) #f #:output "(G (P '()))")
(test 50 ((write (G '(0 1)))) #f #:output "(G (P '()) (P '(0 1)))")

(test 51 ((write (G '(0 1 2) '(1 2 0) '(2 0 1)))) #f
  #:output "(G (P '()) (P '(0 1 2)) (P '(0 2 1)))")

(test 52
  ((write (G '(0 1) '(2 3)))) #f
  #:output "(G (P '()) (P '((0 1) (2 3))) (P '(0 1)) (P '(2 3)))")

(test 53
  ((write (G '(0 1) '(1 2)))) #f
  #:output "(G (P '()) (P '(0 1 2)) (P '(0 2 1)) (P '(0 1)) (P '(0 2)) (P '(1 2)))")

(test 54
  ((write (G '(0 1) '(0 1 2)))) #f
  #:output "(G (P '()) (P '(0 1 2)) (P '(0 2 1)) (P '(0 1)) (P '(0 2)) (P '(1 2)))")

(test 55
  ((define X (G '(0 3) '(0 1 2)))
   (define in-X (in-G X))
   (for*/and ((p in-X) (q in-X)) (G-member? (P p q) X)))
  '(#t))

(test 56
  ((define C3v (G '(0 1) '(0 1 2)))
   (G-print-table C3v)) #f
  #:output "
()      (0 1 2) (0 2 1) (0 1)   (0 2)   (1 2)   
(0 1 2) (0 2 1) ()      (0 2)   (1 2)   (0 1)   
(0 2 1) ()      (0 1 2) (1 2)   (0 1)   (0 2)   
(0 1)   (1 2)   (0 2)   ()      (0 2 1) (0 1 2) 
(0 2)   (0 1)   (1 2)   (0 1 2) ()      (0 2 1) 
(1 2)   (0 2)   (0 1)   (0 2 1) (0 1 2) ()  ")

(test 57
  ((define C3v (G '(0 1) '(0 1 2)))
   (define table (G-table C3v))
   (write table)
   #(#((P '()) (P '(0 1 2)) (P '(0 2 1)) (P '(0 1)) (P '(0 2)) (P '(1 2)))
     #((P '(0 1 2)) (P '(0 2 1)) (P '()) (P '(0 2)) (P '(1 2)) (P '(0 1)))
     #((P '(0 2 1)) (P '()) (P '(0 1 2)) (P '(1 2)) (P '(0 1)) (P '(0 2)))
     #((P '(0 1)) (P '(1 2)) (P '(0 2)) (P '()) (P '(0 2 1)) (P '(0 1 2)))
     #((P '(0 2)) (P '(0 1)) (P '(1 2)) (P '(0 1 2)) (P '()) (P '(0 2 1)))
     #((P '(1 2)) (P '(0 2)) (P '(0 1)) (P '(0 2 1)) (P '(0 1 2)) (P '())))
   (define indices (in-range (G-order C3v)))
   (define (table-ref i j) (vector-ref (vector-ref table i) j))
   (for*/and ((i indices) (j indices))
     (define p  (table-ref i 0))
     (define q  (table-ref 0 j))
     (define pq (table-ref i j))
     (eq? pq (P p q))))
  '(#t)
  #:output "
#(#((P '())      (P '(0 1 2)) (P '(0 2 1)) (P '(0 1))   (P '(0 2))   (P '(1 2)))
  #((P '(0 1 2)) (P '(0 2 1)) (P '())      (P '(0 2))   (P '(1 2))   (P '(0 1)))
  #((P '(0 2 1)) (P '())      (P '(0 1 2)) (P '(1 2))   (P '(0 1))   (P '(0 2)))
  #((P '(0 1))   (P '(1 2))   (P '(0 2))   (P '())      (P '(0 2 1)) (P '(0 1 2)))
  #((P '(0 2))   (P '(0 1))   (P '(1 2))   (P '(0 1 2)) (P '())      (P '(0 2 1)))
  #((P '(1 2))   (P '(0 2))   (P '(0 1))   (P '(0 2 1)) (P '(0 1 2)) (P '())))")

(test 58
  ((define g0 (G-symmetric 3))
   (define g1 (G-symmetric 3 1))
   (define g2 (G-symmetric 3 2))
   (define g3 (G-symmetric '(0 3 6)))
   g0
   (G (P '()) (P '(0 1 2)) (P '(0 2 1)) (P '(0 1)) (P '(0 2)) (P '(1 2)))
   g1
   (G (P '()) (P '(1 2 3)) (P '(1 3 2)) (P '(1 2)) (P '(1 3)) (P '(2 3)))
   g2
   (G (P '()) (P '(2 3 4)) (P '(2 4 3)) (P '(2 3)) (P '(2 4)) (P '(3 4)))
   g3
   (G (P '()) (P '(0 3 6)) (P '(0 6 3)) (P '(0 3)) (P '(0 6)) (P '(3 6)))
   (and
     (G-isomorphism g0 g1)
     (G-isomorphism g0 g2)
     (G-isomorphism g0 g3)
     #t))
  '(#t))

(test 59
  ((and
     (eq? (G-symmetric '()) G-identity)
     (eq? (G-symmetric '(0 1 2)) (G-symmetric 3))
     (eq? (G-symmetric '(4 5 6)) (G-symmetric 3 4))))
  '(#t))

(test 60
  ((for/and ((n (in-range 3 6)))
     (define n-1 (sub1 n))
     (define Sn (G-symmetric n))
     (and (= (set-count (G-base Sn)) 2)
       (eq? Sn (G (list 0 n-1) (range 0 n-1))))))
  '(#t))

(test 61
  ((define g (G '(0 1) '(0 1 2)))
   (for/and ((base (in-list (G-bases g))))
     (eq? (apply G (set->list base)) g)))
  '(#t))

(test 62
  ((values
     (G-invariant-subg? (G '(0 1)) (G '(0 1) '(0 2)))
     (G-invariant-subg? (G '(0 1 2)) (G '(0 1) '(0 2)))))
  '(#f #t))

(test 63
  ((define g0 (G '(0 1) '(2 3)))
   (define g1 (G '((1 2) (7 8)) '((5 6) (3 4))))
   (define-values (g0->g1 g1->g0)
     (apply values (G-isomorphism g0 g1 'g0->g1 'g1->g0)))
   (and
     (eq? (list->G (map g0->g1 (G->list g0))) g1)
     (eq? (list->G (map g1->g0 (G->list g1))) g0)))
  '(#t))

(test-report)
