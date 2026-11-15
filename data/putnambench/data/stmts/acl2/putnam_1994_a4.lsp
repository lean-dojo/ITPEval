;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_a4:
;; arbitrary 2 by 2 integer matrices A and B for which A+kB is invertible
;; over the integers for k=0,1,2,3,4 have A+5B invertible over the integers.
;; This file contains no proof.

(in-package "ACL2")

;; A 2 by 2 integer matrix is invertible with an integer-entry inverse exactly
;; when its determinant is a unit of the integers, namely 1 or -1. Thus the
;; entrywise determinant predicates below are bidirectionally equivalent to
;; the source matrix invertibility assertions.

(defun putnam-1994-a4-determinant-at
    (a00 a01 a10 a11 b00 b01 b10 b11 k)
  (- (* (+ a00 (* k b00))
        (+ a11 (* k b11)))
     (* (+ a01 (* k b01))
        (+ a10 (* k b10)))))

(defun putnam-1994-a4-invertible-at-p
    (a00 a01 a10 a11 b00 b01 b10 b11 k)
  (let ((determinant
         (putnam-1994-a4-determinant-at
          a00 a01 a10 a11 b00 b01 b10 b11 k)))
    (or (equal determinant 1)
        (equal determinant -1))))

(defun putnambench-putnam-1994-a4-statement
    (a00 a01 a10 a11 b00 b01 b10 b11)
  (implies
   (and
    (integerp a00)
    (integerp a01)
    (integerp a10)
    (integerp a11)
    (integerp b00)
    (integerp b01)
    (integerp b10)
    (integerp b11)
    (putnam-1994-a4-invertible-at-p
     a00 a01 a10 a11 b00 b01 b10 b11 0)
    (putnam-1994-a4-invertible-at-p
     a00 a01 a10 a11 b00 b01 b10 b11 1)
    (putnam-1994-a4-invertible-at-p
     a00 a01 a10 a11 b00 b01 b10 b11 2)
    (putnam-1994-a4-invertible-at-p
     a00 a01 a10 a11 b00 b01 b10 b11 3)
    (putnam-1994-a4-invertible-at-p
     a00 a01 a10 a11 b00 b01 b10 b11 4))
   (putnam-1994-a4-invertible-at-p
    a00 a01 a10 a11 b00 b01 b10 b11 5)))

(value-triple :itpeval-statement-checked)
:q
