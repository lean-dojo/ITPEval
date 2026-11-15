;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_568:
;; for every real a, the stated cubic expression equals a^3 + a^2. The
;; universal real-polynomial identity is encoded as equality of complete
;; coefficient lists in ascending degree order. Two real polynomials agree at
;; every real input if and only if their coefficients agree, so this encoding
;; is bidirectionally equivalent to the source statement. This file contains
;; no proof.

(in-package "ACL2")

(defun mathd-algebra-568-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (mathd-algebra-568-polynomial-add
           (cdr left) (cdr right))))))

(defun mathd-algebra-568-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (mathd-algebra-568-polynomial-scale
           scalar (cdr polynomial)))))

(defun mathd-algebra-568-polynomial-multiply (left right)
  (if (endp left)
      nil
    (mathd-algebra-568-polynomial-add
     (mathd-algebra-568-polynomial-scale (car left) right)
     (cons 0
           (mathd-algebra-568-polynomial-multiply
            (cdr left) right)))))

(defun mathd-algebra-568-statement ()
  (let ((a (list 0 1)))
    (equal
     (mathd-algebra-568-polynomial-add
      (mathd-algebra-568-polynomial-multiply
       (mathd-algebra-568-polynomial-multiply
        (mathd-algebra-568-polynomial-add a (list -1))
        (mathd-algebra-568-polynomial-add a (list 1)))
       (mathd-algebra-568-polynomial-add a (list 2)))
      (mathd-algebra-568-polynomial-scale
       -1
       (mathd-algebra-568-polynomial-multiply
        (mathd-algebra-568-polynomial-add a (list -2))
        (mathd-algebra-568-polynomial-add a (list 1)))))
     (mathd-algebra-568-polynomial-add
      (mathd-algebra-568-polynomial-multiply
       (mathd-algebra-568-polynomial-multiply a a)
       a)
      (mathd-algebra-568-polynomial-multiply a a)))))

(value-triple :itpeval-statement-checked)
:q
