;; Statement-only formalization of miniF2F corpus artifact
;; algebra_2complexrootspoly_xsqp49eqxp7itxpn7i: for every complex x,
;; x^2 + 49 factors as (x + 7i)(x - 7i). The universal complex-polynomial
;; identity is encoded as equality of complete coefficient lists in ascending
;; degree order. Two complex polynomials agree at every complex input if and
;; only if their coefficients agree, so this encoding is bidirectionally
;; equivalent to the source statement. This file contains no proof.

(in-package "ACL2")

(defun algebra-2complexrootspoly-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (algebra-2complexrootspoly-polynomial-add
           (cdr left) (cdr right))))))

(defun algebra-2complexrootspoly-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (algebra-2complexrootspoly-polynomial-scale
           scalar (cdr polynomial)))))

(defun algebra-2complexrootspoly-polynomial-mul (left right)
  (if (endp left)
      nil
    (algebra-2complexrootspoly-polynomial-add
     (algebra-2complexrootspoly-polynomial-scale
      (car left) right)
     (cons
      0
      (algebra-2complexrootspoly-polynomial-mul
       (cdr left) right)))))

(defun algebra-2complexrootspoly-xsqp49eqxp7itxpn7i-statement ()
  (let ((x-polynomial (list 0 1)))
    (equal
     (algebra-2complexrootspoly-polynomial-add
      (algebra-2complexrootspoly-polynomial-mul
       x-polynomial x-polynomial)
      (list 49))
     (algebra-2complexrootspoly-polynomial-mul
      (algebra-2complexrootspoly-polynomial-add
       x-polynomial
       (list #c(0 7)))
      (algebra-2complexrootspoly-polynomial-add
       x-polynomial
       (list #c(0 -7)))))))

(value-triple :itpeval-statement-checked)
:q
