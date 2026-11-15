;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__056, "The Hermite-Lindemann Transcendence
;; Theorem": the complex exponential of every nonzero algebraic complex
;; number is transcendental. Complex numbers are represented by
;; rational-complex Cauchy names, and exponential is represented by its
;; defining power-series limit. This file contains no proof.

(in-package "ACL2")

(defun ht056-rational-complex-p (z)
  (and (consp z)
       (rationalp (car z))
       (rationalp (cdr z))))

(defun ht056-complex-zero ()
  (cons 0 0))

(defun ht056-complex-one ()
  (cons 1 0))

(defun ht056-complex-add (z w)
  (cons (+ (car z) (car w))
        (+ (cdr z) (cdr w))))

(defun ht056-complex-negate (z)
  (cons (- (car z))
        (- (cdr z))))

(defun ht056-complex-subtract (z w)
  (ht056-complex-add z (ht056-complex-negate w)))

(defun ht056-complex-multiply (z w)
  (cons (- (* (car z) (car w))
           (* (cdr z) (cdr w)))
        (+ (* (car z) (cdr w))
           (* (cdr z) (car w)))))

(defun ht056-complex-scale (q z)
  (cons (* q (car z))
        (* q (cdr z))))

(defun ht056-complex-squared-modulus (z)
  (+ (* (car z) (car z))
     (* (cdr z) (cdr z))))

(defun ht056-name-value (name index)
  (apply$ name (list index)))

(defun-sk ht056-name-values-rational-complex-p (name)
  (forall (index)
    (implies
     (natp index)
     (ht056-rational-complex-p
      (ht056-name-value name index)))))

(defun-sk ht056-cauchy-tail-p (name epsilon cutoff)
  (forall (left-index right-index)
    (implies
     (and (natp left-index)
          (natp right-index)
          (<= cutoff left-index)
          (<= cutoff right-index))
     (<
      (ht056-complex-squared-modulus
       (ht056-complex-subtract
        (ht056-name-value name left-index)
        (ht056-name-value name right-index)))
      epsilon))))

(defun-sk ht056-cauchy-cutoff-exists-p (name epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (ht056-cauchy-tail-p
          name epsilon cutoff))))

(defun-sk ht056-cauchy-p (name)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (ht056-cauchy-cutoff-exists-p
      name epsilon))))

(defun ht056-complex-cauchy-name-p (name)
  (and (tamep-functionp name)
       (ht056-name-values-rational-complex-p name)
       (ht056-cauchy-p name)))

(defun ht056-integer-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and (integerp (car coefficients))
           (ht056-integer-coefficient-list-p
            (cdr coefficients)))
    (equal coefficients nil)))

(defun ht056-nonzero-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (or (not (equal (car coefficients) 0))
          (ht056-nonzero-coefficient-list-p
           (cdr coefficients)))
    nil))

;; Coefficients are listed in ascending order of exponent.
(defun ht056-polynomial-value (coefficients z)
  (if (consp coefficients)
      (ht056-complex-add
       (cons (car coefficients) 0)
       (ht056-complex-multiply
        z
        (ht056-polynomial-value
         (cdr coefficients) z)))
    (ht056-complex-zero)))

(defun-sk ht056-polynomial-zero-tail-p
  (name coefficients epsilon cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (ht056-complex-squared-modulus
       (ht056-polynomial-value
        coefficients
        (ht056-name-value name index)))
      epsilon))))

(defun-sk ht056-polynomial-zero-cutoff-exists-p
  (name coefficients epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht056-polynomial-zero-tail-p
      name coefficients epsilon cutoff))))

(defun-sk ht056-polynomial-tends-to-zero-p
  (name coefficients)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (ht056-polynomial-zero-cutoff-exists-p
      name coefficients epsilon))))

(defun-sk ht056-algebraic-complex-name-p (name)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (ht056-integer-coefficient-list-p coefficients)
     (ht056-nonzero-coefficient-list-p coefficients)
     (ht056-polynomial-tends-to-zero-p
      name coefficients))))

(defun-sk ht056-nonzero-tail-p (name separation cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<= separation
         (ht056-complex-squared-modulus
          (ht056-name-value name index))))))

(defun-sk ht056-nonzero-complex-name-p (name)
  (exists (separation cutoff)
    (and
     (rationalp separation)
     (< 0 separation)
     (natp cutoff)
     (ht056-nonzero-tail-p
      name separation cutoff))))

(defun ht056-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (ht056-factorial (- n 1)))))

(defun ht056-complex-power (z exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ht056-complex-one)
    (ht056-complex-multiply
     z
     (ht056-complex-power z (- exponent 1)))))

(defun ht056-complex-exp-series-prefix (z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (ht056-complex-zero)
    (let ((index (- terms 1)))
      (ht056-complex-add
       (ht056-complex-exp-series-prefix
        z index)
       (ht056-complex-scale
        (/ 1 (ht056-factorial index))
        (ht056-complex-power z index))))))

;; The diagonal prefixes converge to exp(x) for every Cauchy name x:
;; at index n, use n+1 power-series terms at the nth rational approximation.
(defun ht056-exp-name-value (name index)
  (ht056-complex-exp-series-prefix
   (ht056-name-value name index)
   (+ 1 (nfix index))))

(defun-sk ht056-exp-polynomial-zero-tail-p
  (name coefficients epsilon cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (ht056-complex-squared-modulus
       (ht056-polynomial-value
        coefficients
        (ht056-exp-name-value name index)))
      epsilon))))

(defun-sk ht056-exp-polynomial-zero-cutoff-exists-p
  (name coefficients epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht056-exp-polynomial-zero-tail-p
      name coefficients epsilon cutoff))))

(defun-sk ht056-exp-polynomial-tends-to-zero-p
  (name coefficients)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (ht056-exp-polynomial-zero-cutoff-exists-p
      name coefficients epsilon))))

(defun-sk ht056-exp-is-algebraic-p (name)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (ht056-integer-coefficient-list-p coefficients)
     (ht056-nonzero-coefficient-list-p coefficients)
     (ht056-exp-polynomial-tends-to-zero-p
      name coefficients))))

(defun-sk hundred-theorems-056-hermite-lindemann-statement ()
  (forall (name)
    (implies
     (and
      (ht056-complex-cauchy-name-p name)
      (ht056-algebraic-complex-name-p name)
      (ht056-nonzero-complex-name-p name))
     (not (ht056-exp-is-algebraic-p name)))))

(value-triple :itpeval-statement-checked)
:q
