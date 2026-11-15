;; Statement-only formalization of miniF2F corpus artifact
;; algebra_2rootsintpoly_am10tap11eqasqpam110: for every complex a,
;; (a - 10)(a + 11) equals a^2 + a - 110. The universal complex-polynomial
;; identity is encoded as equality of complete coefficient lists in ascending
;; degree order. Two complex polynomials agree at every complex input if and
;; only if their coefficients agree, so this encoding is bidirectionally
;; equivalent to the source statement. This file contains no proof.

(in-package "ACL2")

(defun algebra-2rootsintpoly-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (algebra-2rootsintpoly-polynomial-add
           (cdr left) (cdr right))))))

(defun algebra-2rootsintpoly-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (algebra-2rootsintpoly-polynomial-scale
           scalar (cdr polynomial)))))

(defun algebra-2rootsintpoly-polynomial-mul (left right)
  (if (endp left)
      nil
    (algebra-2rootsintpoly-polynomial-add
     (algebra-2rootsintpoly-polynomial-scale
      (car left) right)
     (cons
      0
      (algebra-2rootsintpoly-polynomial-mul
       (cdr left) right)))))

(defun algebra-2rootsintpoly-am10tap11eqasqpam110-statement ()
  (let ((a-polynomial (list 0 1)))
    (equal
     (algebra-2rootsintpoly-polynomial-mul
      (algebra-2rootsintpoly-polynomial-add
       a-polynomial
       (list -10))
      (algebra-2rootsintpoly-polynomial-add
       a-polynomial
       (list 11)))
     (algebra-2rootsintpoly-polynomial-add
      (algebra-2rootsintpoly-polynomial-add
       (algebra-2rootsintpoly-polynomial-mul
        a-polynomial a-polynomial)
       a-polynomial)
      (list -110)))))

(value-triple :itpeval-statement-checked)
:q
