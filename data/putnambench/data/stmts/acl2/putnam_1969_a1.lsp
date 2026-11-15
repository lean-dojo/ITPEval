;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_a1:
;; the ranges of bivariate polynomials over the real numbers are exactly the
;; singletons, open or closed rays, and the full real line. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present a real-closed ordered field. By completeness
;; of the first-order theory of real-closed fields, the range classification
;; below is equivalent to its instance over the real numbers. A polynomial is
;; a finite list of (x-exponent y-exponent coefficient) terms; this is an exact
;; finite-support presentation, and range equality is stated extensionally.

(defun p69a1-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p69a1-unary-value (operation x)
  (apply$ operation (list x)))

(defun p69a1-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun p69a1-iff (left right)
  (if left
      (if right t nil)
    (if right nil t)))

(defun-sk p69a1-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p69a1-member-p carrier x)
      (p69a1-member-p carrier y)
      (p69a1-member-p carrier z))
     (and
      (p69a1-member-p
       carrier (p69a1-binary-value add x y))
      (p69a1-member-p
       carrier (p69a1-binary-value multiply x y))
      (p69a1-member-p
       carrier (p69a1-unary-value negate x))
      (p69a1-member-p
       carrier (p69a1-unary-value inverse x))
      (equal
       (p69a1-binary-value
        add (p69a1-binary-value add x y) z)
       (p69a1-binary-value
        add x (p69a1-binary-value add y z)))
      (equal
       (p69a1-binary-value add x y)
       (p69a1-binary-value add y x))
      (equal (p69a1-binary-value add x zero) x)
      (equal
       (p69a1-binary-value
        add x (p69a1-unary-value negate x))
       zero)
      (equal
       (p69a1-binary-value
        multiply
        (p69a1-binary-value multiply x y)
        z)
       (p69a1-binary-value
        multiply
        x
        (p69a1-binary-value multiply y z)))
      (equal
       (p69a1-binary-value multiply x y)
       (p69a1-binary-value multiply y x))
      (equal (p69a1-binary-value multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p69a1-binary-value
         multiply x (p69a1-unary-value inverse x))
        one))
      (equal
       (p69a1-binary-value
        multiply x (p69a1-binary-value add y z))
       (p69a1-binary-value
        add
        (p69a1-binary-value multiply x y)
        (p69a1-binary-value multiply x z)))))))

(defun-sk p69a1-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p69a1-member-p carrier x)
      (p69a1-member-p carrier y)
      (p69a1-member-p carrier z))
     (and
      (not (p69a1-binary-value less x x))
      (or
       (equal x y)
       (p69a1-binary-value less x y)
       (p69a1-binary-value less y x))
      (implies
       (and
        (p69a1-binary-value less x y)
        (p69a1-binary-value less y z))
       (p69a1-binary-value less x z))
      (implies
       (p69a1-binary-value less x y)
       (p69a1-binary-value
        less
        (p69a1-binary-value add x z)
        (p69a1-binary-value add y z)))
      (implies
       (and
        (p69a1-binary-value less zero x)
        (p69a1-binary-value less zero y))
       (p69a1-binary-value
        less
        zero
        (p69a1-binary-value multiply x y)))))))

(defun p69a1-univariate-polynomial-p
    (carrier coefficients)
  (if (consp coefficients)
      (and
       (p69a1-member-p carrier (car coefficients))
       (p69a1-univariate-polynomial-p
        carrier (cdr coefficients)))
    (equal coefficients nil)))

(defun p69a1-univariate-eval
    (zero add multiply coefficients x)
  (if (consp coefficients)
      (p69a1-binary-value
       add
       (car coefficients)
       (p69a1-binary-value
        multiply
        x
        (p69a1-univariate-eval
         zero add multiply (cdr coefficients) x)))
    zero))

(defun p69a1-odd-degree-polynomial-p
    (carrier zero coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (p69a1-univariate-polynomial-p carrier coefficients)
   (not (equal (car (last coefficients)) zero))
   (oddp (- (len coefficients) 1))))

(defun-sk p69a1-positive-square-root-exists-p
    (carrier multiply x)
  (exists (root)
    (and
     (p69a1-member-p carrier root)
     (equal
      (p69a1-binary-value multiply root root)
      x))))

(defun-sk p69a1-positive-elements-are-squares-p
    (carrier zero multiply less)
  (forall (x)
    (implies
     (and
      (p69a1-member-p carrier x)
      (p69a1-binary-value less zero x))
     (p69a1-positive-square-root-exists-p
      carrier multiply x))))

(defun-sk p69a1-odd-polynomial-root-exists-p
    (carrier zero add multiply coefficients)
  (exists (root)
    (and
     (p69a1-member-p carrier root)
     (equal
      (p69a1-univariate-eval
       zero add multiply coefficients root)
      zero))))

(defun-sk p69a1-odd-polynomials-have-roots-p
    (carrier zero add multiply)
  (forall (coefficients)
    (implies
     (p69a1-odd-degree-polynomial-p
      carrier zero coefficients)
     (p69a1-odd-polynomial-root-exists-p
      carrier zero add multiply coefficients))))

(defun p69a1-real-closed-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p69a1-member-p carrier zero)
   (p69a1-member-p carrier one)
   (not (equal zero one))
   (p69a1-field-laws-p
    carrier zero one add multiply negate inverse)
   (p69a1-order-laws-p
    carrier zero add multiply less)
   (p69a1-binary-value less zero one)
   (p69a1-positive-elements-are-squares-p
    carrier zero multiply less)
   (p69a1-odd-polynomials-have-roots-p
    carrier zero add multiply)))

(defun p69a1-term-p (carrier term)
  (and
   (true-listp term)
   (equal (len term) 3)
   (natp (nth 0 term))
   (natp (nth 1 term))
   (p69a1-member-p carrier (nth 2 term))))

(defun p69a1-polynomial-p (carrier polynomial)
  (if (consp polynomial)
      (and
       (p69a1-term-p carrier (car polynomial))
       (p69a1-polynomial-p carrier (cdr polynomial)))
    (equal polynomial nil)))

(defun p69a1-power (one multiply base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p69a1-binary-value
     multiply
     base
     (p69a1-power
      one multiply base (- exponent 1)))))

(defun p69a1-term-value
    (one multiply term x y)
  (p69a1-binary-value
   multiply
   (nth 2 term)
   (p69a1-binary-value
    multiply
    (p69a1-power
     one multiply x (nth 0 term))
    (p69a1-power
     one multiply y (nth 1 term)))))

(defun p69a1-polynomial-value
    (zero one add multiply polynomial x y)
  (if (consp polynomial)
      (p69a1-binary-value
       add
       (p69a1-term-value
        one multiply (car polynomial) x y)
       (p69a1-polynomial-value
        zero one add multiply (cdr polynomial) x y))
    zero))

(defun-sk p69a1-range-member-p
    (carrier zero one add multiply polynomial value)
  (exists (x y)
    (and
     (p69a1-member-p carrier x)
     (p69a1-member-p carrier y)
     (equal
      (p69a1-polynomial-value
       zero one add multiply polynomial x y)
      value))))

(defun-sk p69a1-range-equals-singleton-p
    (carrier zero one add multiply polynomial endpoint)
  (forall (value)
    (implies
     (p69a1-member-p carrier value)
     (p69a1-iff
      (p69a1-range-member-p
       carrier zero one add multiply polynomial value)
      (equal value endpoint)))))

(defun-sk p69a1-range-equals-closed-upper-ray-p
    (carrier zero one add multiply less polynomial endpoint)
  (forall (value)
    (implies
     (p69a1-member-p carrier value)
     (p69a1-iff
      (p69a1-range-member-p
       carrier zero one add multiply polynomial value)
      (not (p69a1-binary-value less value endpoint))))))

(defun-sk p69a1-range-equals-closed-lower-ray-p
    (carrier zero one add multiply less polynomial endpoint)
  (forall (value)
    (implies
     (p69a1-member-p carrier value)
     (p69a1-iff
      (p69a1-range-member-p
       carrier zero one add multiply polynomial value)
      (not (p69a1-binary-value less endpoint value))))))

(defun-sk p69a1-range-equals-open-lower-ray-p
    (carrier zero one add multiply less polynomial endpoint)
  (forall (value)
    (implies
     (p69a1-member-p carrier value)
     (p69a1-iff
      (p69a1-range-member-p
       carrier zero one add multiply polynomial value)
      (p69a1-binary-value less value endpoint)))))

(defun-sk p69a1-range-equals-open-upper-ray-p
    (carrier zero one add multiply less polynomial endpoint)
  (forall (value)
    (implies
     (p69a1-member-p carrier value)
     (p69a1-iff
      (p69a1-range-member-p
       carrier zero one add multiply polynomial value)
      (p69a1-binary-value less endpoint value)))))

(defun-sk p69a1-range-equals-universe-p
    (carrier zero one add multiply polynomial)
  (forall (value)
    (implies
     (p69a1-member-p carrier value)
     (p69a1-range-member-p
      carrier zero one add multiply polynomial value))))

(defun-sk p69a1-range-equals-nonuniversal-solution-p
    (carrier zero one add multiply less polynomial)
  (exists (endpoint)
    (and
     (p69a1-member-p carrier endpoint)
     (or
      (p69a1-range-equals-singleton-p
       carrier zero one add multiply polynomial endpoint)
      (p69a1-range-equals-closed-upper-ray-p
       carrier zero one add multiply less polynomial endpoint)
      (p69a1-range-equals-closed-lower-ray-p
       carrier zero one add multiply less polynomial endpoint)
      (p69a1-range-equals-open-lower-ray-p
       carrier zero one add multiply less polynomial endpoint)
      (p69a1-range-equals-open-upper-ray-p
       carrier zero one add multiply less polynomial endpoint)))))

(defun p69a1-range-classified-p
    (carrier zero one add multiply less polynomial)
  (or
   (p69a1-range-equals-nonuniversal-solution-p
    carrier zero one add multiply less polynomial)
   (p69a1-range-equals-universe-p
    carrier zero one add multiply polynomial)))

(defun-sk p69a1-all-polynomial-ranges-classified-p
    (carrier zero one add multiply less)
  (forall (polynomial)
    (implies
     (p69a1-polynomial-p carrier polynomial)
     (p69a1-range-classified-p
      carrier zero one add multiply less polynomial))))

(defun-sk p69a1-singleton-range-exists-p
    (carrier zero one add multiply endpoint)
  (exists (polynomial)
    (and
     (p69a1-polynomial-p carrier polynomial)
     (p69a1-range-equals-singleton-p
      carrier zero one add multiply polynomial endpoint))))

(defun-sk p69a1-closed-upper-ray-range-exists-p
    (carrier zero one add multiply less endpoint)
  (exists (polynomial)
    (and
     (p69a1-polynomial-p carrier polynomial)
     (p69a1-range-equals-closed-upper-ray-p
      carrier zero one add multiply less polynomial endpoint))))

(defun-sk p69a1-closed-lower-ray-range-exists-p
    (carrier zero one add multiply less endpoint)
  (exists (polynomial)
    (and
     (p69a1-polynomial-p carrier polynomial)
     (p69a1-range-equals-closed-lower-ray-p
      carrier zero one add multiply less polynomial endpoint))))

(defun-sk p69a1-open-lower-ray-range-exists-p
    (carrier zero one add multiply less endpoint)
  (exists (polynomial)
    (and
     (p69a1-polynomial-p carrier polynomial)
     (p69a1-range-equals-open-lower-ray-p
      carrier zero one add multiply less polynomial endpoint))))

(defun-sk p69a1-open-upper-ray-range-exists-p
    (carrier zero one add multiply less endpoint)
  (exists (polynomial)
    (and
     (p69a1-polynomial-p carrier polynomial)
     (p69a1-range-equals-open-upper-ray-p
      carrier zero one add multiply less polynomial endpoint))))

(defun-sk p69a1-all-singleton-ranges-occur-p
    (carrier zero one add multiply)
  (forall (endpoint)
    (implies
     (p69a1-member-p carrier endpoint)
     (p69a1-singleton-range-exists-p
      carrier zero one add multiply endpoint))))

(defun-sk p69a1-all-closed-upper-ray-ranges-occur-p
    (carrier zero one add multiply less)
  (forall (endpoint)
    (implies
     (p69a1-member-p carrier endpoint)
     (p69a1-closed-upper-ray-range-exists-p
      carrier zero one add multiply less endpoint))))

(defun-sk p69a1-all-closed-lower-ray-ranges-occur-p
    (carrier zero one add multiply less)
  (forall (endpoint)
    (implies
     (p69a1-member-p carrier endpoint)
     (p69a1-closed-lower-ray-range-exists-p
      carrier zero one add multiply less endpoint))))

(defun-sk p69a1-all-open-lower-ray-ranges-occur-p
    (carrier zero one add multiply less)
  (forall (endpoint)
    (implies
     (p69a1-member-p carrier endpoint)
     (p69a1-open-lower-ray-range-exists-p
      carrier zero one add multiply less endpoint))))

(defun-sk p69a1-all-open-upper-ray-ranges-occur-p
    (carrier zero one add multiply less)
  (forall (endpoint)
    (implies
     (p69a1-member-p carrier endpoint)
     (p69a1-open-upper-ray-range-exists-p
      carrier zero one add multiply less endpoint))))

(defun-sk p69a1-universal-range-exists-p
    (carrier zero one add multiply)
  (exists (polynomial)
    (and
     (p69a1-polynomial-p carrier polynomial)
     (p69a1-range-equals-universe-p
      carrier zero one add multiply polynomial))))

(defun putnambench-putnam-1969-a1-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
  (implies
   (p69a1-real-closed-field-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less)
   (and
    (p69a1-all-polynomial-ranges-classified-p
     real-carrier real-zero real-one real-add real-multiply
     real-less)
    (p69a1-all-singleton-ranges-occur-p
     real-carrier real-zero real-one real-add real-multiply)
    (p69a1-all-closed-upper-ray-ranges-occur-p
     real-carrier real-zero real-one real-add real-multiply
     real-less)
    (p69a1-all-closed-lower-ray-ranges-occur-p
     real-carrier real-zero real-one real-add real-multiply
     real-less)
    (p69a1-all-open-lower-ray-ranges-occur-p
     real-carrier real-zero real-one real-add real-multiply
     real-less)
    (p69a1-all-open-upper-ray-ranges-occur-p
     real-carrier real-zero real-one real-add real-multiply
     real-less)
    (p69a1-universal-range-exists-p
     real-carrier real-zero real-one real-add real-multiply))))

(value-triple :itpeval-statement-checked)
:q
