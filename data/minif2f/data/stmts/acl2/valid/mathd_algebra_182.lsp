;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_182:
;; for every complex y, 7 * (3 * y + 2) = 21 * y + 14. The universal
;; complex-polynomial identity is encoded as equality of complete coefficient
;; lists in ascending degree order. Two complex polynomials agree at every
;; complex input if and only if their coefficients agree, so this encoding is
;; bidirectionally equivalent to the source statement. This file contains no
;; proof.

(in-package "ACL2")

(defun mathd-algebra-182-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (mathd-algebra-182-polynomial-add
           (cdr left) (cdr right))))))

(defun mathd-algebra-182-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (mathd-algebra-182-polynomial-scale
           scalar (cdr polynomial)))))

(defun mathd-algebra-182-statement ()
  (let ((y-polynomial (list 0 1)))
    (equal
     (mathd-algebra-182-polynomial-scale
      7
      (mathd-algebra-182-polynomial-add
       (mathd-algebra-182-polynomial-scale 3 y-polynomial)
       (list 2)))
     (mathd-algebra-182-polynomial-add
      (mathd-algebra-182-polynomial-scale 21 y-polynomial)
      (list 14)))))

(value-triple :itpeval-statement-checked)
:q
