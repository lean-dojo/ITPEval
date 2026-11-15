;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_a6:
;; the binary zero-block coefficient series over the field with two elements
;; satisfies its stated cubic formal-power-series identity. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Every field with two elements is uniquely isomorphic to GF(2), and this
;; isomorphism fixes 0 and 1. Thus bits with arithmetic modulo 2 preserve the
;; source coefficient definition and all formal-power-series operations.
;;
;; The source binary digit list is least-significant-bit first and has a 1
;; adjoined at each end. Scanning the digits from low to high therefore checks
;; exactly that each intervening block of zeroes has even length. The final
;; EVENP check accounts for the adjoined high-end 1.

(defun putnam-1989-a6-even-zero-blocks-aux (n zero-count fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp n) (zp fuel))
      (evenp zero-count)
    (if (equal (mod n 2) 0)
        (putnam-1989-a6-even-zero-blocks-aux
         (floor n 2) (+ zero-count 1) (- fuel 1))
      (and
       (evenp zero-count)
       (putnam-1989-a6-even-zero-blocks-aux
        (floor n 2) 0 (- fuel 1))))))

(defun putnam-1989-a6-alpha-coefficient (n)
  (if (and (natp n)
           (putnam-1989-a6-even-zero-blocks-aux n 0 n))
      1
    0))

;; For fixed I and TOTAL, sum alpha_i alpha_j alpha_(TOTAL-j) over
;; 0 <= j <= TOTAL. All these sums are finite coefficient convolutions.

(defun putnam-1989-a6-cube-row (i total j)
  (declare (xargs :measure (nfix j)))
  (let ((term
         (* (putnam-1989-a6-alpha-coefficient i)
            (putnam-1989-a6-alpha-coefficient j)
            (putnam-1989-a6-alpha-coefficient (- total j)))))
    (if (zp j)
        term
      (+ term
         (putnam-1989-a6-cube-row
          i total (- j 1))))))

;; Sum the rows for 0 <= i <= n. This is the coefficient of x^n in alpha^3.

(defun putnam-1989-a6-cube-coefficient-aux (n i)
  (declare (xargs :measure (nfix i)))
  (let* ((remaining (- n i))
         (row
          (putnam-1989-a6-cube-row
           i remaining remaining)))
    (if (zp i)
        row
      (+ row
         (putnam-1989-a6-cube-coefficient-aux
          n (- i 1))))))

(defun putnam-1989-a6-cube-coefficient (n)
  (if (natp n)
      (putnam-1989-a6-cube-coefficient-aux n n)
    0))

;; Equality of formal power series is coefficientwise equality. The universal
;; closure in N of this predicate is therefore exactly
;;
;;   alpha^3 + X*alpha + 1 = 0
;;
;; over GF(2). Alpha has been eliminated only because the source hypotheses
;; determine every one of its coefficients uniquely.

(defun putnambench-putnam-1989-a6-statement (n)
  (implies
   (natp n)
   (equal
    (mod
     (+ (putnam-1989-a6-cube-coefficient n)
        (if (zp n)
            0
          (putnam-1989-a6-alpha-coefficient (- n 1)))
        (if (equal n 0) 1 0))
     2)
    0)))

(value-triple :itpeval-statement-checked)
:q
