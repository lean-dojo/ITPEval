;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_a1:
;; the cardinality of the primes whose base-10 digits alternate 1 and 0,
;; beginning and ending with 1, equals the supplied solution 1. This file
;; contains no proof.

(in-package "ACL2")

(defun putnam-1989-a1-solution ()
  1)

;; A(k) has 2*k+1 decimal digits and satisfies A(0)=1 and
;; A(k+1)=100*A(k)+1. Hence its values are exactly the positive integers
;; whose usual base-10 digits alternate 1 and 0, beginning and ending with 1.
(defun putnam-1989-a1-alternating-number (k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (+ 1
       (* 100
          (putnam-1989-a1-alternating-number (- k 1))))))

(defun-sk putnam-1989-a1-alternating-positive-integer-p (p)
  (exists (k)
    (and
     (natp k)
     (equal
      p
      (putnam-1989-a1-alternating-number k)))))

;; For a natural number, testing every candidate divisor below it is exactly
;; the usual definition of primality.
(defun putnam-1989-a1-no-divisor-through-p (n divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (or (not (natp divisor))
          (<= divisor 1))
      t
    (and
     (not (equal (mod n divisor) 0))
     (putnam-1989-a1-no-divisor-through-p
      n (- divisor 1)))))

(defun putnam-1989-a1-prime-p (n)
  (and
   (natp n)
   (< 1 n)
   (putnam-1989-a1-no-divisor-through-p
    n (- n 1))))

(defun putnam-1989-a1-counted-prime-p (p)
  (and
   (putnam-1989-a1-prime-p p)
   (putnam-1989-a1-alternating-positive-integer-p p)))

(defun putnam-1989-a1-listed-primes-p (members)
  (if (consp members)
      (and
       (putnam-1989-a1-counted-prime-p (car members))
       (putnam-1989-a1-listed-primes-p (cdr members)))
    (equal members nil)))

(defun-sk putnam-1989-a1-all-counted-primes-listed-p (members)
  (forall (p)
    (implies
     (putnam-1989-a1-counted-prime-p p)
     (member-equal p members))))

;; A duplicate-free list of length COUNT that contains exactly all members of
;; the unbounded source set is a bijective encoding of cardinality COUNT.
(defun putnam-1989-a1-cardinality-witness-p (count members)
  (and
   (natp count)
   (true-listp members)
   (equal (len members) count)
   (no-duplicatesp-equal members)
   (putnam-1989-a1-listed-primes-p members)
   (putnam-1989-a1-all-counted-primes-listed-p members)))

(defun-sk putnam-1989-a1-cardinality-p (count)
  (exists (members)
    (putnam-1989-a1-cardinality-witness-p
     count members)))

(defun putnambench-putnam-1989-a1-statement ()
  (putnam-1989-a1-cardinality-p
   (putnam-1989-a1-solution)))

(value-triple :itpeval-statement-checked)
:q
