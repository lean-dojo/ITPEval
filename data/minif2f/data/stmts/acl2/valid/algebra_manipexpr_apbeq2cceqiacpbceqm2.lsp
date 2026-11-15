;; Statement-only formalization of miniF2F corpus artifact
;; algebra_manipexpr_apbeq2cceqiacpbceqm2: complex numbers a, b, and c
;; satisfying a + b = 2*c and c = i satisfy a*c + b*c = -2.
;; Every satisfying tuple is uniquely parameterized by arbitrary complex a,
;; with c = i and b = 2*i - a. The resulting universal polynomial identity
;; is encoded as equality of complete coefficient lists through degree one.
;; Polynomial extensionality makes this encoding bidirectionally equivalent
;; to the source implication over the full complex domain. This file contains
;; no proof.

(in-package "ACL2")

(defun algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons
     (+ (car left) (car right))
     (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-add
      (cdr left) (cdr right))))))

(defun algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-scale
    (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons
     (* scalar (car polynomial))
     (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-scale
      scalar (cdr polynomial)))))

(defun algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-mul (left right)
  (if (endp left)
      nil
    (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-add
     (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-scale
      (car left) right)
     (cons
      0
      (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-mul
       (cdr left) right)))))

(defun algebra-manipexpr-apbeq2cceqiacpbceqm2-statement ()
  (let* ((a-polynomial (list 0 1))
         (i-polynomial (list #c(0 1)))
         (c-polynomial i-polynomial)
         (b-polynomial
          (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-add
           (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-scale
            2 c-polynomial)
           (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-scale
            -1 a-polynomial))))
    (equal
     (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-add
      (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-mul
       a-polynomial c-polynomial)
      (algebra-manipexpr-apbeq2cceqiacpbceqm2-polynomial-mul
       b-polynomial c-polynomial))
     (list -2 0))))

(value-triple :itpeval-statement-checked)
:q
