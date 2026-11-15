;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_b2:
;; the primes occurring in at least seven prime-coefficient quadratics with
;; a rational root are exactly 2 and 5. This file contains no proof.

(in-package "ACL2")

;; For a natural number, testing every candidate divisor below it is exactly
;; the usual definition of primality.
(defun putnam-2011-b2-no-divisor-through-p (number divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (or (not (natp divisor))
          (<= divisor 1))
      t
    (and
     (not (equal (mod number divisor) 0))
     (putnam-2011-b2-no-divisor-through-p
      number (- divisor 1)))))

(defun putnam-2011-b2-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2011-b2-no-divisor-through-p
    number (- number 1))))

;; This is membership in the source set S. The rational root remains an
;; internal existential witness, as in the ground-truth statements.
(defun-sk putnam-2011-b2-triple-p (p q r)
  (exists (x)
    (and
     (putnam-2011-b2-prime-p p)
     (putnam-2011-b2-prime-p q)
     (putnam-2011-b2-prime-p r)
     (rationalp x)
     (equal
      (+ (* p x x) (* q x) r)
      0))))

(defun putnam-2011-b2-occurrence-p (p q r target)
  (and
   (putnam-2011-b2-triple-p p q r)
   (or
    (equal p target)
    (equal q target)
    (equal r target))))

;; A set has cardinality at least seven exactly when it has seven pairwise
;; distinct members. These witnesses are ordered prime triples, not a finite
;; replacement for the unbounded source set.
(defun-sk putnam-2011-b2-seven-occurrences-p (target)
  (exists
      (p1 q1 r1
       p2 q2 r2
       p3 q3 r3
       p4 q4 r4
       p5 q5 r5
       p6 q6 r6
       p7 q7 r7)
    (and
     (putnam-2011-b2-occurrence-p p1 q1 r1 target)
     (putnam-2011-b2-occurrence-p p2 q2 r2 target)
     (putnam-2011-b2-occurrence-p p3 q3 r3 target)
     (putnam-2011-b2-occurrence-p p4 q4 r4 target)
     (putnam-2011-b2-occurrence-p p5 q5 r5 target)
     (putnam-2011-b2-occurrence-p p6 q6 r6 target)
     (putnam-2011-b2-occurrence-p p7 q7 r7 target)
     (no-duplicatesp-equal
      (list
       (list p1 q1 r1)
       (list p2 q2 r2)
       (list p3 q3 r3)
       (list p4 q4 r4)
       (list p5 q5 r5)
       (list p6 q6 r6)
       (list p7 q7 r7))))))

(defun putnambench-putnam-2011-b2-statement (target)
  (implies
   (natp target)
   (iff
    (and
     (putnam-2011-b2-prime-p target)
     (putnam-2011-b2-seven-occurrences-p target))
    (or
     (equal target 2)
     (equal target 5)))))

(value-triple :itpeval-statement-checked)
:q
