;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_a4:
;; every positive-degree product of real variables is a rational linear
;; combination of powers of ternary linear forms. This file contains no proof.

(in-package "ACL2")

;; A witness is a finite true list of rows (c a_1 ... a_n), where c is
;; rational and every a_j is -1, 0, or 1. Its length is the source N. Finite
;; lists are equivalent to the source Fin-indexed families, and each list
;; extends arbitrarily to the source's total natural-indexed coefficient
;; functions outside the ranges i<N and j<n.
;;
;; The coefficient test below states equality of homogeneous polynomials over
;; Q. For an exponent vector e of total degree n, the coefficient contributed
;; by c*(sum_j a_j*x_j)^n is
;;
;;   c * n!/(product_j e_j!) * product_j a_j^e_j.
;;
;; The target product has coefficient 1 exactly at e=(1,...,1), and 0 at
;; every other degree-n exponent vector. Base-(n+1) digit vectors enumerate
;; all such vectors without bounding n.
;;
;; This identity formulation is bidirectionally equivalent to the formal
;; sources' quantifier order. An identity witness evaluates to a source
;; witness at every real vector. Conversely, for fixed n the possible finite
;; rational/ternary witnesses form a countable set. If their polynomial zero
;; sets cover R^n, as the source says, Baire category implies that one of
;; those polynomials is identically zero. Thus no real domain or existential
;; witness is lost by the exact coefficient formulation.

(defun putnam-2004-a4-ternary-list-p (values)
  (if (consp values)
      (and (or (equal (car values) -1)
               (equal (car values) 0)
               (equal (car values) 1))
           (putnam-2004-a4-ternary-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2004-a4-row-p (row n)
  (and (true-listp row)
       (consp row)
       (rationalp (car row))
       (equal (len (cdr row)) (nfix n))
       (putnam-2004-a4-ternary-list-p (cdr row))))

(defun putnam-2004-a4-witness-p (rows n)
  (if (consp rows)
      (and (putnam-2004-a4-row-p (car rows) n)
           (putnam-2004-a4-witness-p (cdr rows) n))
    (equal rows nil)))

(defun putnam-2004-a4-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (nfix n)
       (putnam-2004-a4-factorial (- (nfix n) 1)))))

(defun putnam-2004-a4-factorial-product (exponents)
  (if (consp exponents)
      (* (putnam-2004-a4-factorial (car exponents))
         (putnam-2004-a4-factorial-product (cdr exponents)))
    1))

(defun putnam-2004-a4-power-product (values exponents)
  (if (and (consp values) (consp exponents))
      (* (expt (car values) (nfix (car exponents)))
         (putnam-2004-a4-power-product
          (cdr values) (cdr exponents)))
    1))

(defun putnam-2004-a4-row-coefficient (row n exponents)
  (* (car row)
     (/ (putnam-2004-a4-factorial n)
        (putnam-2004-a4-factorial-product exponents))
     (putnam-2004-a4-power-product
      (cdr row) exponents)))

(defun putnam-2004-a4-witness-coefficient
    (rows n exponents)
  (if (consp rows)
      (+ (putnam-2004-a4-row-coefficient
          (car rows) n exponents)
         (putnam-2004-a4-witness-coefficient
          (cdr rows) n exponents))
    0))

(defun putnam-2004-a4-natural-sum (values)
  (if (consp values)
      (+ (nfix (car values))
         (putnam-2004-a4-natural-sum (cdr values)))
    0))

(defun putnam-2004-a4-all-ones-p (values)
  (if (consp values)
      (and (equal (car values) 1)
           (putnam-2004-a4-all-ones-p (cdr values)))
    (equal values nil)))

(defun putnam-2004-a4-base-digits (code base count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (mod (nfix code) (nfix base))
     (putnam-2004-a4-base-digits
      (floor (nfix code) (nfix base))
      base
      (- (nfix count) 1)))))

(defun putnam-2004-a4-coefficient-correct-p
    (rows n exponents)
  (if (equal (putnam-2004-a4-natural-sum exponents)
             (nfix n))
      (equal
       (putnam-2004-a4-witness-coefficient
        rows n exponents)
       (if (putnam-2004-a4-all-ones-p exponents)
           1
         0))
    t))

(defun putnam-2004-a4-codes-correct-p (rows n code)
  (declare (xargs :measure (nfix code)))
  (and
   (putnam-2004-a4-coefficient-correct-p
    rows
    n
    (putnam-2004-a4-base-digits
     code (+ 1 (nfix n)) n))
   (if (zp code)
       t
     (putnam-2004-a4-codes-correct-p
      rows n (- (nfix code) 1)))))

(defun putnam-2004-a4-identity-witness-p (n rows)
  (and
   (natp n)
   (< 0 n)
   (putnam-2004-a4-witness-p rows n)
   (putnam-2004-a4-codes-correct-p
    rows
    n
    (- (expt (+ 1 n) n) 1))))

(defun putnam-2004-a4-quoted (object)
  (list 'quote object))

(defun putnam-2004-a4-true-function ()
  (list
   'lambda
   '(witness)
   (putnam-2004-a4-quoted t)))

(defun putnam-2004-a4-witness-failure-function (n)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'putnam-2004-a4-identity-witness-p
     (putnam-2004-a4-quoted n)
     'witness)
    (putnam-2004-a4-quoted nil)
    (putnam-2004-a4-quoted t))))

;; Negated functional equality is an internal, unbounded existential over
;; witness objects; no N, coefficient family, or matrix is a root parameter.
(defun putnam-2004-a4-decomposition-exists-p (n)
  (let ((failure
         (putnam-2004-a4-witness-failure-function n))
        (always-true
         (putnam-2004-a4-true-function)))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnambench-putnam-2004-a4-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (putnam-2004-a4-decomposition-exists-p n)))

(value-triple :itpeval-statement-checked)
:q
