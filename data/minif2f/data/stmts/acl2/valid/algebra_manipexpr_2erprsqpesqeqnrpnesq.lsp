;; Statement-only formalization of miniF2F corpus artifact
;; algebra_manipexpr_2erprsqpesqeqnrpnesq: for all complex e and r,
;; 2(er) + (e^2 + r^2) equals (-r + -e)^2. The universal bivariate
;; complex-polynomial identity is encoded as equality of complete dense
;; coefficient lists, with the coefficient of e^i r^j at index i + 3j.
;; Every variable degree is at most two, so this indexing is injective;
;; polynomial extensionality makes the encoding bidirectionally equivalent
;; to the source statement. This file contains no proof.

(in-package "ACL2")

(defun algebra-manipexpr-polynomial-add (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (algebra-manipexpr-polynomial-add
           (cdr left) (cdr right))))))

(defun algebra-manipexpr-polynomial-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (algebra-manipexpr-polynomial-scale
           scalar (cdr polynomial)))))

(defun algebra-manipexpr-polynomial-mul (left right)
  (if (endp left)
      nil
    (algebra-manipexpr-polynomial-add
     (algebra-manipexpr-polynomial-scale
      (car left) right)
     (cons
      0
      (algebra-manipexpr-polynomial-mul
       (cdr left) right)))))

(defun algebra-manipexpr-monomial (degree)
  (if (zp degree)
      (list 1)
    (cons 0
          (algebra-manipexpr-monomial (1- degree)))))

(defun algebra-manipexpr-2erprsqpesqeqnrpnesq-statement ()
  (let ((e-polynomial (algebra-manipexpr-monomial 1))
        (r-polynomial (algebra-manipexpr-monomial 3)))
    (equal
     (algebra-manipexpr-polynomial-add
      (algebra-manipexpr-polynomial-scale
       2
       (algebra-manipexpr-polynomial-mul
        e-polynomial r-polynomial))
      (algebra-manipexpr-polynomial-add
       (algebra-manipexpr-polynomial-mul
        e-polynomial e-polynomial)
       (algebra-manipexpr-polynomial-mul
        r-polynomial r-polynomial)))
     (algebra-manipexpr-polynomial-mul
      (algebra-manipexpr-polynomial-add
       (algebra-manipexpr-polynomial-scale -1 r-polynomial)
       (algebra-manipexpr-polynomial-scale -1 e-polynomial))
      (algebra-manipexpr-polynomial-add
       (algebra-manipexpr-polynomial-scale -1 r-polynomial)
       (algebra-manipexpr-polynomial-scale -1 e-polynomial))))))

(value-triple :itpeval-statement-checked)
:q
