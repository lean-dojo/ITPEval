;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_b3:
;; existence of integer-polynomial factors lifting a coprime factorization
;; from modulo p to modulo p^n. This file contains no proof.

(in-package "ACL2")

;; Integer polynomials are canonical finite lists of coefficients in ascending
;; degree order. The zero polynomial is NIL; every nonzero polynomial has a
;; nonzero final coefficient. This is a bijective representation of Z[x].
(defun putnam-1986-b3-integer-list-p (values)
  (if (consp values)
      (and (integerp (car values))
           (putnam-1986-b3-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1986-b3-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1986-b3-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (endp tail))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1986-b3-integer-polynomial-p (polynomial)
  (and
   (putnam-1986-b3-integer-list-p polynomial)
   (equal
    (putnam-1986-b3-poly-normalize polynomial)
    polynomial)))

(defun putnam-1986-b3-poly-add-raw (left right)
  (cond
   ((consp left)
    (cons
     (+ (car left)
        (if (consp right) (car right) 0))
     (putnam-1986-b3-poly-add-raw
      (cdr left)
      (if (consp right) (cdr right) nil))))
   ((consp right) right)
   (t nil)))

(defun putnam-1986-b3-poly-add (left right)
  (putnam-1986-b3-poly-normalize
   (putnam-1986-b3-poly-add-raw left right)))

(defun putnam-1986-b3-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (putnam-1986-b3-poly-normalize
       (cons
        (* scalar (car polynomial))
        (putnam-1986-b3-poly-scale
         scalar (cdr polynomial))))
    nil))

(defun putnam-1986-b3-poly-multiply (left right)
  (if (consp left)
      (putnam-1986-b3-poly-add
       (putnam-1986-b3-poly-scale (car left) right)
       (cons
        0
        (putnam-1986-b3-poly-multiply
         (cdr left) right)))
    nil))

;; This recursive check is exactly coefficientwise polynomial congruence.
;; Missing list entries denote the zero coefficients above the degree.
(defun putnam-1986-b3-poly-congruent-p (left right modulus)
  (declare
   (xargs
    :measure
    (+ (acl2-count left)
       (acl2-count right))))
  (if (or (consp left) (consp right))
      (and
       (equal
        (mod
         (-
          (if (consp left) (car left) 0)
          (if (consp right) (car right) 0))
         modulus)
        0)
       (putnam-1986-b3-poly-congruent-p
        (if (consp left) (cdr left) nil)
        (if (consp right) (cdr right) nil)
        modulus))
    t))

(defun putnam-1986-b3-no-divisor-from-p (number candidate)
  (declare
   (xargs
    :measure
    (nfix (- number candidate))))
  (if (and
       (natp number)
       (natp candidate)
       (<= 2 candidate)
       (< candidate number))
      (and
       (not (equal (mod number candidate) 0))
       (putnam-1986-b3-no-divisor-from-p
        number (+ candidate 1)))
    t))

(defun putnam-1986-b3-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-1986-b3-no-divisor-from-p number 2)))

(defun-sk putnam-1986-b3-lifts-exist-p
    (n p f g h)
  (exists (f-lifted g-lifted)
    (and
     (putnam-1986-b3-integer-polynomial-p f-lifted)
     (putnam-1986-b3-integer-polynomial-p g-lifted)
     (putnam-1986-b3-poly-congruent-p
      f-lifted f p)
     (putnam-1986-b3-poly-congruent-p
      g-lifted g p)
     (putnam-1986-b3-poly-congruent-p
      (putnam-1986-b3-poly-multiply
       f-lifted g-lifted)
      h
      (expt p n)))))

(defun putnambench-putnam-1986-b3-statement
    (n p f g h r s)
  (implies
   (and
    (natp n)
    (< 0 n)
    (natp p)
    (< 0 p)
    (putnam-1986-b3-prime-p p)
    (putnam-1986-b3-integer-polynomial-p f)
    (putnam-1986-b3-integer-polynomial-p g)
    (putnam-1986-b3-integer-polynomial-p h)
    (putnam-1986-b3-integer-polynomial-p r)
    (putnam-1986-b3-integer-polynomial-p s)
    (putnam-1986-b3-poly-congruent-p
     (putnam-1986-b3-poly-add
      (putnam-1986-b3-poly-multiply r f)
      (putnam-1986-b3-poly-multiply s g))
     (list 1)
     p)
    (putnam-1986-b3-poly-congruent-p
     (putnam-1986-b3-poly-multiply f g)
     h
     p))
   (putnam-1986-b3-lifts-exist-p
    n p f g h)))

(value-triple :itpeval-statement-checked)
:q
