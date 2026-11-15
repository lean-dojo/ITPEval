;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_b3:
;; a positive-dimensional rational matrix with at least m+n distinct prime
;; absolute entry values has rank at least two. This file contains no proof.

(in-package "ACL2")

;; A list of rows is an exact representation of the source finite matrix.

(defun putnam-2014-b3-rational-row-p (row n)
  (and
   (true-listp row)
   (equal (len row) n)
   (if (endp row)
       t
     (and
      (rationalp (car row))
      (putnam-2014-b3-rational-row-p (cdr row) (- n 1))))))

(defun putnam-2014-b3-rational-matrix-p (matrix m n)
  (and
   (true-listp matrix)
   (equal (len matrix) m)
   (if (endp matrix)
       t
     (and
      (putnam-2014-b3-rational-row-p (car matrix) n)
      (putnam-2014-b3-rational-matrix-p
       (cdr matrix) (- m 1) n)))))

(defun putnam-2014-b3-no-proper-divisor-from-p
    (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and
       (natp number)
       (natp divisor)
       (<= 2 divisor)
       (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (putnam-2014-b3-no-proper-divisor-from-p
        number (+ divisor 1)))
    t))

(defun putnam-2014-b3-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2014-b3-no-proper-divisor-from-p number 2)))

(defun putnam-2014-b3-adjoin-prime-value (value primes)
  (let ((absolute-value (abs value)))
    (if (and
         (integerp value)
         (putnam-2014-b3-prime-p absolute-value)
         (not (member-equal absolute-value primes)))
        (cons absolute-value primes)
      primes)))

(defun putnam-2014-b3-collect-row-primes (row primes)
  (if (endp row)
      primes
    (putnam-2014-b3-collect-row-primes
     (cdr row)
     (putnam-2014-b3-adjoin-prime-value
      (car row) primes))))

(defun putnam-2014-b3-collect-matrix-primes (matrix primes)
  (if (endp matrix)
      primes
    (putnam-2014-b3-collect-matrix-primes
     (cdr matrix)
     (putnam-2014-b3-collect-row-primes
      (car matrix) primes))))

;; Over the rationals, rank is at least two exactly when some two rows and
;; two columns form a nonzero 2 by 2 minor.

(defun putnam-2014-b3-minor-with-first-column-p
    (first-row-tail second-row-tail first-a first-b)
  (if (or (endp first-row-tail)
          (endp second-row-tail))
      nil
    (or
     (not
      (equal
       (- (* first-a (car second-row-tail))
          (* (car first-row-tail) first-b))
       0))
     (putnam-2014-b3-minor-with-first-column-p
      (cdr first-row-tail)
      (cdr second-row-tail)
      first-a
      first-b))))

(defun putnam-2014-b3-two-rows-have-nonzero-minor-p
    (first-row second-row)
  (if (or (endp first-row)
          (endp second-row))
      nil
    (or
     (putnam-2014-b3-minor-with-first-column-p
      (cdr first-row)
      (cdr second-row)
      (car first-row)
      (car second-row))
     (putnam-2014-b3-two-rows-have-nonzero-minor-p
      (cdr first-row)
      (cdr second-row)))))

(defun putnam-2014-b3-row-has-nonzero-minor-p
    (row remaining-rows)
  (if (endp remaining-rows)
      nil
    (or
     (putnam-2014-b3-two-rows-have-nonzero-minor-p
      row (car remaining-rows))
     (putnam-2014-b3-row-has-nonzero-minor-p
      row (cdr remaining-rows)))))

(defun putnam-2014-b3-rank-at-least-two-p (matrix)
  (if (endp matrix)
      nil
    (or
     (putnam-2014-b3-row-has-nonzero-minor-p
      (car matrix) (cdr matrix))
     (putnam-2014-b3-rank-at-least-two-p
      (cdr matrix)))))

(defun putnambench-putnam-2014-b3-statement (m n matrix)
  (implies
   (and
    (natp m)
    (natp n)
    (< 0 m)
    (< 0 n)
    (putnam-2014-b3-rational-matrix-p matrix m n)
    (<=
     (+ m n)
     (len
      (putnam-2014-b3-collect-matrix-primes matrix nil))))
   (putnam-2014-b3-rank-at-least-two-p matrix)))

(value-triple :itpeval-statement-checked)
:q
