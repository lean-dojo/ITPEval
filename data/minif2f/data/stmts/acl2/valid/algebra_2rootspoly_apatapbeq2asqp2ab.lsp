;; Statement-only formalization of miniF2F corpus artifact
;; algebra_2rootspoly_apatapbeq2asqp2ab: for all complex a and b,
;; (a + a)(a + b) equals 2a^2 + 2ab. The universal bivariate
;; complex-polynomial identity is encoded as equality of canonical dense
;; coefficient tables, with powers of a indexing the outer list and powers
;; of b indexing each inner list. Two complex polynomials agree at every
;; complex pair if and only if their coefficients agree, so this encoding is
;; bidirectionally equivalent to the source statement. This file contains no
;; proof.

(in-package "ACL2")

(defun algebra-2rootspoly-bpoly-trim (polynomial)
  (if (endp polynomial)
      nil
    (let ((rest (algebra-2rootspoly-bpoly-trim (cdr polynomial))))
      (if (and (endp rest)
               (equal (car polynomial) 0))
          nil
        (cons (car polynomial) rest)))))

(defun algebra-2rootspoly-bpoly-add-raw (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons (+ (car left) (car right))
          (algebra-2rootspoly-bpoly-add-raw
           (cdr left) (cdr right))))))

(defun algebra-2rootspoly-bpoly-add (left right)
  (algebra-2rootspoly-bpoly-trim
   (algebra-2rootspoly-bpoly-add-raw left right)))

(defun algebra-2rootspoly-bpoly-scale-raw (scalar polynomial)
  (if (endp polynomial)
      nil
    (cons (* scalar (car polynomial))
          (algebra-2rootspoly-bpoly-scale-raw
           scalar (cdr polynomial)))))

(defun algebra-2rootspoly-bpoly-scale (scalar polynomial)
  (algebra-2rootspoly-bpoly-trim
   (algebra-2rootspoly-bpoly-scale-raw scalar polynomial)))

(defun algebra-2rootspoly-bpoly-mul (left right)
  (if (endp left)
      nil
    (algebra-2rootspoly-bpoly-add
     (algebra-2rootspoly-bpoly-scale (car left) right)
     (cons
      0
      (algebra-2rootspoly-bpoly-mul (cdr left) right)))))

(defun algebra-2rootspoly-bivariate-trim (polynomial)
  (if (endp polynomial)
      nil
    (let ((coefficient
           (algebra-2rootspoly-bpoly-trim (car polynomial)))
          (rest
           (algebra-2rootspoly-bivariate-trim (cdr polynomial))))
      (if (and (endp rest)
               (endp coefficient))
          nil
        (cons coefficient rest)))))

(defun algebra-2rootspoly-bivariate-add-raw (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons
     (algebra-2rootspoly-bpoly-add (car left) (car right))
     (algebra-2rootspoly-bivariate-add-raw
      (cdr left) (cdr right))))))

(defun algebra-2rootspoly-bivariate-add (left right)
  (algebra-2rootspoly-bivariate-trim
   (algebra-2rootspoly-bivariate-add-raw left right)))

(defun algebra-2rootspoly-bivariate-scale-raw (coefficient polynomial)
  (if (endp polynomial)
      nil
    (cons
     (algebra-2rootspoly-bpoly-mul coefficient (car polynomial))
     (algebra-2rootspoly-bivariate-scale-raw
      coefficient (cdr polynomial)))))

(defun algebra-2rootspoly-bivariate-scale (coefficient polynomial)
  (algebra-2rootspoly-bivariate-trim
   (algebra-2rootspoly-bivariate-scale-raw coefficient polynomial)))

(defun algebra-2rootspoly-bivariate-mul (left right)
  (if (endp left)
      nil
    (algebra-2rootspoly-bivariate-add
     (algebra-2rootspoly-bivariate-scale (car left) right)
     (cons
      nil
      (algebra-2rootspoly-bivariate-mul (cdr left) right)))))

(defun algebra-2rootspoly-apatapbeq2asqp2ab-statement ()
  (let ((a-polynomial (list nil (list 1)))
        (b-polynomial (list (list 0 1)))
        (two-polynomial (list (list 2))))
    (equal
     (algebra-2rootspoly-bivariate-mul
      (algebra-2rootspoly-bivariate-add
       a-polynomial a-polynomial)
      (algebra-2rootspoly-bivariate-add
       a-polynomial b-polynomial))
     (algebra-2rootspoly-bivariate-add
      (algebra-2rootspoly-bivariate-mul
       two-polynomial
       (algebra-2rootspoly-bivariate-mul
        a-polynomial a-polynomial))
      (algebra-2rootspoly-bivariate-mul
       two-polynomial
       (algebra-2rootspoly-bivariate-mul
        a-polynomial b-polynomial))))))

(value-triple :itpeval-statement-checked)
:q
