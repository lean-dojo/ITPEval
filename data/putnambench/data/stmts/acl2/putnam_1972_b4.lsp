;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_b4:
;; for every natural n at least two, an integer-coefficient polynomial in
;; three variables recovers x from x^n, x^(n+1), and x+x^(n+2). This file
;; contains no proof.

(in-package "ACL2")

;; A term is (coefficient exponent-a exponent-b exponent-c), and a polynomial
;; is a finite list of terms. This is an exact sparse representation of an
;; integer polynomial, not a finite table of its values.

(defun putnam-1972-b4-integer-polynomial-p (polynomial)
  (if (consp polynomial)
      (let ((term (car polynomial)))
        (and (true-listp term)
             (equal (len term) 4)
             (integerp (nth 0 term))
             (natp (nth 1 term))
             (natp (nth 2 term))
             (natp (nth 3 term))
             (putnam-1972-b4-integer-polynomial-p
              (cdr polynomial))))
    (equal polynomial nil)))

(defun putnam-1972-b4-term-value (term a b c)
  (* (nth 0 term)
     (expt a (nth 1 term))
     (expt b (nth 2 term))
     (expt c (nth 3 term))))

(defun putnam-1972-b4-polynomial-value (polynomial a b c)
  (if (consp polynomial)
      (+ (putnam-1972-b4-term-value (car polynomial) a b c)
         (putnam-1972-b4-polynomial-value
          (cdr polynomial) a b c))
    0))

(defun-sk putnam-1972-b4-polynomial-identity-p (n polynomial)
  (forall (x)
    (implies
     (integerp x)
     (equal
      x
      (putnam-1972-b4-polynomial-value
       polynomial
       (expt x n)
       (expt x (+ n 1))
       (+ x (expt x (+ n 2))))))))

(defun-sk putnam-1972-b4-polynomial-exists-p (n)
  (exists (polynomial)
    (and
     (putnam-1972-b4-integer-polynomial-p polynomial)
     (putnam-1972-b4-polynomial-identity-p n polynomial))))

(defun putnambench-putnam-1972-b4-statement (n)
  (implies
   (and (natp n)
        (< 1 n))
   (putnam-1972-b4-polynomial-exists-p n)))

(value-triple :itpeval-statement-checked)
:q
