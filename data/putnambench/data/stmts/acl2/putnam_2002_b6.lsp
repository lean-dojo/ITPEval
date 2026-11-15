;; Statement-only formalization of PutnamBench corpus artifact putnam_2002_b6:
;; for every prime p, the determinant of the matrix with rows (x,y,z),
;; (x^p,y^p,z^p), and (x^(p^2),y^(p^2),z^(p^2)) is coefficientwise
;; congruent modulo p to a finite product of integer linear forms. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun putnam-2002-b6-no-divisor-through-p (p divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (and (natp p) (natp divisor))
      (if (< divisor 2)
          t
        (and
         (not (equal (mod p divisor) 0))
         (putnam-2002-b6-no-divisor-through-p
          p (- divisor 1))))
    nil))

(defun putnam-2002-b6-prime-p (p)
  (and
   (natp p)
   (<= 2 p)
   (putnam-2002-b6-no-divisor-through-p p (- p 1))))

;; A triple (a b c) denotes the integer polynomial ax+by+cz. A true list of
;; such triples denotes its finite product. Neither the list length nor any
;; coefficient is bounded.
(defun putnam-2002-b6-integer-triple-p (triple)
  (and
   (true-listp triple)
   (equal (len triple) 3)
   (integerp (nth 0 triple))
   (integerp (nth 1 triple))
   (integerp (nth 2 triple))))

(defun putnam-2002-b6-linear-form-list-p (linear-forms)
  (cond
   ((equal linear-forms nil) t)
   ((consp linear-forms)
    (and
     (putnam-2002-b6-integer-triple-p (car linear-forms))
     (putnam-2002-b6-linear-form-list-p (cdr linear-forms))))
   (t nil)))

;; This is the coefficient of x^i y^j z^k in the product represented by
;; LINEAR-FORMS. The empty product has constant coefficient one.
(defun putnam-2002-b6-product-coefficient
    (linear-forms i j k)
  (if (endp linear-forms)
      (if (and (equal i 0)
               (equal j 0)
               (equal k 0))
          1
        0)
    (let ((linear-form (car linear-forms))
          (remaining (cdr linear-forms)))
      (+
       (if (and (natp i) (< 0 i))
           (* (nth 0 linear-form)
              (putnam-2002-b6-product-coefficient
               remaining (- i 1) j k))
         0)
       (if (and (natp j) (< 0 j))
           (* (nth 1 linear-form)
              (putnam-2002-b6-product-coefficient
               remaining i (- j 1) k))
         0)
       (if (and (natp k) (< 0 k))
           (* (nth 2 linear-form)
              (putnam-2002-b6-product-coefficient
               remaining i j (- k 1)))
         0)))))

(defun putnam-2002-b6-monomial-indicator
    (i j k x-exponent y-exponent z-exponent)
  (if (and (equal i x-exponent)
           (equal j y-exponent)
           (equal k z-exponent))
      1
    0))

;; The six signed Leibniz terms give the coefficient of the source
;; determinant, including any coincident terms by integer addition.
(defun putnam-2002-b6-determinant-coefficient (p i j k)
  (let ((p2 (expt p 2)))
    (+
     (putnam-2002-b6-monomial-indicator i j k 1 p p2)
     (- (putnam-2002-b6-monomial-indicator i j k 1 p2 p))
     (- (putnam-2002-b6-monomial-indicator i j k p 1 p2))
     (putnam-2002-b6-monomial-indicator i j k p2 1 p)
     (putnam-2002-b6-monomial-indicator i j k p p2 1)
     (- (putnam-2002-b6-monomial-indicator i j k p2 p 1)))))

;; Universal quantification over all natural exponent triples is exactly
;; coefficientwise congruence of the two integer polynomials modulo p.
(defun-sk putnam-2002-b6-coefficientwise-congruent-p
    (p linear-forms)
  (forall (i j k)
    (implies
     (and (natp i) (natp j) (natp k))
     (equal
      (mod (putnam-2002-b6-determinant-coefficient p i j k) p)
      (mod (putnam-2002-b6-product-coefficient
            linear-forms i j k)
           p)))))

;; The source witness remains an internal, unbounded existential over all
;; finite lists of integer linear forms.
(defun-sk putnam-2002-b6-factorization-exists-p (p)
  (exists (linear-forms)
    (and
     (putnam-2002-b6-linear-form-list-p linear-forms)
     (putnam-2002-b6-coefficientwise-congruent-p
      p linear-forms))))

(defun-sk putnambench-putnam-2002-b6-statement ()
  (forall (p)
    (implies
     (putnam-2002-b6-prime-p p)
     (putnam-2002-b6-factorization-exists-p p))))

(value-triple :itpeval-statement-checked)
:q
