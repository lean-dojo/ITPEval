;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_a6:
;; the value at 1 of a real polynomial constrained by a sparse power identity
;; is the product of the distinct positive exponents divided by n factorial.
;; This file contains no proof.

(in-package "ACL2")

;; Lists A and B contain exactly a_1,...,a_n and b_1,...,b_n. Polynomials use
;; ascending coefficient order. This loses no function data because the source
;; statement refers only to these n entries, and every polynomial has a finite
;; coefficient list.
;;
;; Standard ACL2 has exact rationals rather than a primitive real sort. For
;; fixed N and B, coefficientwise expansion of the source identity is an
;; affine linear system with integer coefficients in A and the coefficients
;; of F; failure of the conclusion is one affine linear disequality with a
;; rational constant. Any real counterexample therefore has a rational
;; counterexample, by rational row reduction and a rational choice outside the
;; resulting hyperplane. Conversely, rational data embeds in the reals.
;; Hence universal closure of this rational coefficient formulation is
;; bidirectionally equivalent to the source theorem over real coefficients.

(defun putnam-1986-a6-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (putnam-1986-a6-rational-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1986-a6-positive-nat-list-p (values)
  (if (consp values)
      (and (posp (car values))
           (putnam-1986-a6-positive-nat-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1986-a6-poly-normalize (polynomial)
  (if (consp polynomial)
      (let ((rest
             (putnam-1986-a6-poly-normalize (cdr polynomial))))
        (if (and (endp rest)
                 (equal (car polynomial) 0))
            nil
          (cons (car polynomial) rest)))
    nil))

(defun putnam-1986-a6-poly-add (left right)
  (cond
   ((consp left)
    (cons (+ (car left)
             (if (consp right) (car right) 0))
          (putnam-1986-a6-poly-add
           (cdr left)
           (if (consp right) (cdr right) nil))))
   ((consp right) right)
   (t nil)))

(defun putnam-1986-a6-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1986-a6-poly-scale scalar (cdr polynomial)))
    nil))

(defun putnam-1986-a6-poly-mul (left right)
  (if (consp left)
      (putnam-1986-a6-poly-add
       (putnam-1986-a6-poly-scale (car left) right)
       (cons 0
             (putnam-1986-a6-poly-mul (cdr left) right)))
    nil))

(defun putnam-1986-a6-poly-pow (polynomial exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list 1)
    (putnam-1986-a6-poly-mul
     polynomial
     (putnam-1986-a6-poly-pow polynomial (- exponent 1)))))

(defun putnam-1986-a6-monomial (coefficient exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list coefficient)
    (cons 0
          (putnam-1986-a6-monomial coefficient (- exponent 1)))))

(defun putnam-1986-a6-sparse-polynomial (coefficients exponents)
  (if (and (consp coefficients)
           (consp exponents))
      (putnam-1986-a6-poly-add
       (putnam-1986-a6-monomial
        (car coefficients) (car exponents))
       (putnam-1986-a6-sparse-polynomial
        (cdr coefficients) (cdr exponents)))
    nil))

(defun putnam-1986-a6-poly-at-one (polynomial)
  (if (consp polynomial)
      (+ (car polynomial)
         (putnam-1986-a6-poly-at-one (cdr polynomial)))
    0))

(defun putnam-1986-a6-product (values)
  (if (consp values)
      (* (car values)
         (putnam-1986-a6-product (cdr values)))
    1))

(defun putnam-1986-a6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1986-a6-factorial (- n 1)))))

(defun putnambench-putnam-1986-a6-statement
    (n coefficients exponents polynomial)
  (implies
   (and
    (posp n)
    (putnam-1986-a6-rational-list-p coefficients)
    (equal (len coefficients) n)
    (putnam-1986-a6-positive-nat-list-p exponents)
    (equal (len exponents) n)
    (no-duplicatesp-equal exponents)
    (putnam-1986-a6-rational-list-p polynomial)
    (equal
     (putnam-1986-a6-poly-normalize
      (putnam-1986-a6-poly-mul
       (putnam-1986-a6-poly-pow (list 1 -1) n)
       polynomial))
     (putnam-1986-a6-poly-normalize
      (putnam-1986-a6-poly-add
       (list 1)
       (putnam-1986-a6-sparse-polynomial
        coefficients exponents)))))
   (equal
    (putnam-1986-a6-poly-at-one polynomial)
    (/ (putnam-1986-a6-product exponents)
       (putnam-1986-a6-factorial n)))))

(value-triple :itpeval-statement-checked)
:q
