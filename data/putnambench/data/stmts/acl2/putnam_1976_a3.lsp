;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_a3:
;; the complete natural-number classification of prime powers that differ by
;; one in absolute value. This file contains no proof.

(in-package "ACL2")

(defun putnam-1976-a3-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1976-a3-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1976-a3-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1976-a3-no-divisor-through-p
    p (- p 1))))

(defun putnam-1976-a3-equation-p (p r q s)
  (and
   (putnam-1976-a3-prime-p p)
   (putnam-1976-a3-prime-p q)
   (< 1 r)
   (< 1 s)
   (equal
    (abs (- (expt p r) (expt q s)))
    1)))

(defun putnam-1976-a3-solution-p (p r q s)
  (or
   (and (equal p 3)
        (equal r 2)
        (equal q 2)
        (equal s 3))
   (and (equal p 2)
        (equal r 3)
        (equal q 3)
        (equal s 2))))

(defun putnambench-putnam-1976-a3-statement (p r q s)
  (implies
   (and (natp p)
        (natp r)
        (natp q)
        (natp s))
   (equal
    (putnam-1976-a3-equation-p p r q s)
    (putnam-1976-a3-solution-p p r q s))))

(value-triple :itpeval-statement-checked)
:q
