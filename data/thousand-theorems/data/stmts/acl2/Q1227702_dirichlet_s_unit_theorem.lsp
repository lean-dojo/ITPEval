;; Statement-only formalization of thousand-theorems corpus artifact Q1227702,
;; "Dirichlet's unit theorem": the units of the ring of integers of a number
;; field, modulo torsion, have a basis of rank equal to the number of infinite
;; places minus one, yielding a unique torsion-times-basis-power decomposition.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ objects present arbitrary carriers and operations. Conservative
;; DEFUN-SK predicates keep every unbounded universal or existential quantifier
;; internal to the statement. The real-value field is Archimedean and real
;; closed. Infinite places are exactly the normalized Archimedean absolute
;; values on the number field, listed extensionally without duplicates.
;;
;; A fundamental system has one unit for each place except one. Its unique
;; decomposition property is equivalent to being a Z-basis of the unit group
;; modulo torsion, and also states the indexed Lean theorem's unique
;; torsion-times-basis-power factorization.

(defun q1227702-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q1227702-unary-value (function object)
  (apply$ function (list object)))

(defun q1227702-binary-value (function left right)
  (apply$ function (list left right)))

;; Fields and ordered real-closed Archimedean fields.

(defun-sk q1227702-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (q1227702-member-p carrier x)
      (q1227702-member-p carrier y)
      (q1227702-member-p carrier z))
     (let* ((xy-add
             (q1227702-binary-value add x y))
            (yz-add
             (q1227702-binary-value add y z))
            (xy-mul
             (q1227702-binary-value multiply x y))
            (yz-mul
             (q1227702-binary-value multiply y z))
            (neg-x
             (q1227702-unary-value negate x))
            (inv-x
             (q1227702-unary-value inverse x)))
       (and
        (q1227702-member-p carrier xy-add)
        (q1227702-member-p carrier xy-mul)
        (q1227702-member-p carrier neg-x)
        (q1227702-member-p carrier inv-x)
        (equal
         (q1227702-binary-value add xy-add z)
         (q1227702-binary-value add x yz-add))
        (equal
         xy-add
         (q1227702-binary-value add y x))
        (equal
         (q1227702-binary-value add x zero)
         x)
        (equal
         (q1227702-binary-value add x neg-x)
         zero)
        (equal
         (q1227702-binary-value multiply xy-mul z)
         (q1227702-binary-value multiply x yz-mul))
        (equal
         xy-mul
         (q1227702-binary-value multiply y x))
        (equal
         (q1227702-binary-value multiply x one)
         x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (q1227702-binary-value multiply x inv-x)
          one))
        (equal
         (q1227702-binary-value multiply x yz-add)
         (q1227702-binary-value
          add
          (q1227702-binary-value multiply x y)
          (q1227702-binary-value multiply x z))))))))

(defun q1227702-field-p
    (carrier zero one add multiply negate inverse)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (q1227702-member-p carrier zero)
   (q1227702-member-p carrier one)
   (not (equal zero one))
   (q1227702-field-laws-p
    carrier zero one add multiply negate inverse)))

(defun-sk q1227702-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (q1227702-member-p carrier x)
      (q1227702-member-p carrier y)
      (q1227702-member-p carrier z))
     (let ((xy (q1227702-binary-value less x y))
           (yx (q1227702-binary-value less y x))
           (yz (q1227702-binary-value less y z)))
       (and
        (not (q1227702-binary-value less x x))
        (or xy yx (equal x y))
        (implies
         (and xy yz)
         (q1227702-binary-value less x z))
        (implies
         xy
         (q1227702-binary-value
          less
          (q1227702-binary-value add x z)
          (q1227702-binary-value add y z)))
        (implies
         (and
          (q1227702-binary-value less zero x)
          (q1227702-binary-value less zero y))
         (q1227702-binary-value
          less
          zero
          (q1227702-binary-value multiply x y))))))))

(defun q1227702-natural-cast (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (q1227702-binary-value
     add
     one
     (q1227702-natural-cast (- n 1) zero one add))))

(defun q1227702-integer-cast
    (n zero one add negate)
  (if (and (integerp n) (< n 0))
      (q1227702-unary-value
       negate
       (q1227702-natural-cast (- n) zero one add))
    (q1227702-natural-cast (nfix n) zero one add)))

(defun q1227702-rational-cast
    (q zero one add multiply negate inverse)
  (if (rationalp q)
      (q1227702-binary-value
       multiply
       (q1227702-integer-cast
        (numerator q) zero one add negate)
       (q1227702-unary-value
        inverse
        (q1227702-integer-cast
         (denominator q) zero one add negate)))
    zero))

(defun-sk q1227702-archimedean-laws-p
    (carrier zero one add less bound)
  (forall (x)
    (implies
     (q1227702-member-p carrier x)
     (let ((n (q1227702-unary-value bound x)))
       (and
        (natp n)
        (q1227702-binary-value
         less
         x
         (q1227702-natural-cast n zero one add)))))))

(defun q1227702-real-coefficient-list-p
    (coefficients carrier)
  (if (consp coefficients)
      (and
       (q1227702-member-p carrier (car coefficients))
       (q1227702-real-coefficient-list-p
        (cdr coefficients) carrier))
    (equal coefficients nil)))

(defun q1227702-real-polynomial-eval
    (coefficients x zero add multiply)
  (if (consp coefficients)
      (q1227702-binary-value
       add
       (car coefficients)
       (q1227702-binary-value
        multiply
        x
        (q1227702-real-polynomial-eval
         (cdr coefficients) x zero add multiply)))
    zero))

(defun-sk q1227702-square-root-laws-p
    (carrier zero multiply less square-root)
  (forall (x)
    (implies
     (and
      (q1227702-member-p carrier x)
      (not (q1227702-binary-value less x zero)))
     (let ((root
            (q1227702-unary-value square-root x)))
       (and
        (q1227702-member-p carrier root)
        (not (q1227702-binary-value less root zero))
        (equal
         (q1227702-binary-value multiply root root)
         x))))))

(defun-sk q1227702-odd-root-laws-p
    (carrier zero add multiply odd-root)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (<= 2 (len coefficients))
      (evenp (len coefficients))
      (q1227702-real-coefficient-list-p
       coefficients carrier)
      (not (equal (car (last coefficients)) zero)))
     (let ((root
            (q1227702-unary-value odd-root coefficients)))
       (and
        (q1227702-member-p carrier root)
        (equal
         (q1227702-real-polynomial-eval
          coefficients root zero add multiply)
         zero))))))

(defun q1227702-real-field-p
    (carrier zero one add multiply negate inverse less
     square-root odd-root archimedean-bound)
  (and
   (q1227702-field-p
    carrier zero one add multiply negate inverse)
   (tamep-functionp less)
   (tamep-functionp square-root)
   (tamep-functionp odd-root)
   (tamep-functionp archimedean-bound)
   (q1227702-order-laws-p
    carrier zero add multiply less)
   (q1227702-binary-value less zero one)
   (q1227702-archimedean-laws-p
    carrier zero one add less archimedean-bound)
   (q1227702-square-root-laws-p
    carrier zero multiply less square-root)
   (q1227702-odd-root-laws-p
    carrier zero add multiply odd-root)))

;; Finite extensions of Q, presented by an explicit finite basis and inverse
;; coordinate map. The carrier itself remains arbitrary and potentially
;; infinite.

(defun-sk q1227702-rational-cast-injective-p
    (zero one add multiply negate inverse)
  (forall (q r)
    (implies
     (and
      (rationalp q)
      (rationalp r)
      (equal
       (q1227702-rational-cast
        q zero one add multiply negate inverse)
       (q1227702-rational-cast
        r zero one add multiply negate inverse)))
     (equal q r))))

(defun q1227702-rational-list-p (values)
  (if (consp values)
      (and
       (rationalp (car values))
       (q1227702-rational-list-p (cdr values)))
    (equal values nil)))

(defun q1227702-linear-combination
    (basis coefficients
     zero one add multiply negate inverse)
  (declare (xargs :measure (len basis)))
  (if (and (consp basis) (consp coefficients))
      (q1227702-binary-value
       add
       (q1227702-binary-value
        multiply
        (q1227702-rational-cast
         (car coefficients)
         zero one add multiply negate inverse)
        (car basis))
       (q1227702-linear-combination
        (cdr basis)
        (cdr coefficients)
        zero one add multiply negate inverse))
    zero))

(defun q1227702-basis-elements-p (basis carrier)
  (if (consp basis)
      (and
       (q1227702-member-p carrier (car basis))
       (q1227702-basis-elements-p (cdr basis) carrier))
    (equal basis nil)))

(defun-sk q1227702-basis-laws-p
    (carrier basis coordinates
     zero one add multiply negate inverse)
  (forall (x coefficients)
    (and
     (implies
      (q1227702-member-p carrier x)
      (let ((coordinate-vector
             (q1227702-unary-value coordinates x)))
        (and
         (true-listp coordinate-vector)
         (q1227702-rational-list-p coordinate-vector)
         (equal (len coordinate-vector) (len basis))
         (equal
          (q1227702-linear-combination
           basis coordinate-vector
           zero one add multiply negate inverse)
          x))))
     (implies
      (and
       (true-listp coefficients)
       (q1227702-rational-list-p coefficients)
       (equal (len coefficients) (len basis)))
      (equal
       (q1227702-unary-value
        coordinates
        (q1227702-linear-combination
         basis coefficients
         zero one add multiply negate inverse))
       coefficients)))))

(defun q1227702-number-field-p
    (carrier zero one add multiply negate inverse
     basis coordinates)
  (and
   (q1227702-field-p
    carrier zero one add multiply negate inverse)
   (true-listp basis)
   (q1227702-basis-elements-p basis carrier)
   (tamep-functionp coordinates)
   (q1227702-rational-cast-injective-p
    zero one add multiply negate inverse)
   (q1227702-basis-laws-p
    carrier basis coordinates
    zero one add multiply negate inverse)))

;; Algebraic integers, units, torsion, and integer powers.

(defun q1227702-integer-list-p (values)
  (if (consp values)
      (and
       (integerp (car values))
       (q1227702-integer-list-p (cdr values)))
    (equal values nil)))

(defun q1227702-monic-polynomial-eval
    (coefficients x
     zero one add multiply negate)
  (if (consp coefficients)
      (q1227702-binary-value
       add
       (q1227702-integer-cast
        (car coefficients) zero one add negate)
       (q1227702-binary-value
        multiply
        x
        (q1227702-monic-polynomial-eval
         (cdr coefficients) x
         zero one add multiply negate)))
    one))

(defun-sk q1227702-integral-p
    (x zero one add multiply negate)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (consp coefficients)
     (q1227702-integer-list-p coefficients)
     (equal
      (q1227702-monic-polynomial-eval
       coefficients x
       zero one add multiply negate)
      zero))))

(defun q1227702-unit-p
    (x carrier zero one add multiply negate inverse)
  (and
   (q1227702-member-p carrier x)
   (not (equal x zero))
   (q1227702-integral-p
    x zero one add multiply negate)
   (q1227702-integral-p
    (q1227702-unary-value inverse x)
    zero one add multiply negate)))

(defun q1227702-natural-power
    (x n one multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (q1227702-binary-value
     multiply
     x
     (q1227702-natural-power
      x (- n 1) one multiply))))

(defun q1227702-integer-power
    (x n one multiply inverse)
  (if (and (integerp n) (< n 0))
      (q1227702-natural-power
       (q1227702-unary-value inverse x)
       (- n)
       one
       multiply)
    (q1227702-natural-power
     x (nfix n) one multiply)))

(defun-sk q1227702-torsion-p
    (x carrier zero one add multiply negate inverse)
  (exists (n)
    (and
     (q1227702-unit-p
      x carrier zero one add multiply negate inverse)
     (natp n)
     (< 0 n)
     (equal
      (q1227702-natural-power x n one multiply)
      one))))

;; Infinite places as normalized Archimedean absolute values.

(defun q1227702-real-nonnegative-p
    (less zero value)
  (not (q1227702-binary-value less value zero)))

(defun q1227702-real-le-p (less left right)
  (not (q1227702-binary-value less right left)))

(defun q1227702-real-abs
    (value zero negate less)
  (if (q1227702-binary-value less value zero)
      (q1227702-unary-value negate value)
    value))

(defun-sk q1227702-infinite-place-laws-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     carrier zero one add multiply negate inverse place)
  (forall (x y q)
    (and
     (implies
      (and
       (q1227702-member-p carrier x)
       (q1227702-member-p carrier y))
      (let ((place-x
             (q1227702-unary-value place x))
            (place-y
             (q1227702-unary-value place y)))
        (and
         (q1227702-member-p real-carrier place-x)
         (q1227702-real-nonnegative-p
          real-less real-zero place-x)
         (iff
          (equal place-x real-zero)
          (equal x zero))
         (equal
          (q1227702-unary-value
           place
           (q1227702-binary-value multiply x y))
          (q1227702-binary-value
           real-multiply place-x place-y))
         (q1227702-real-le-p
          real-less
          (q1227702-unary-value
           place
           (q1227702-binary-value add x y))
          (q1227702-binary-value
           real-add place-x place-y)))))
     (implies
      (rationalp q)
      (equal
       (q1227702-unary-value
        place
        (q1227702-rational-cast
         q zero one add multiply negate inverse))
       (q1227702-real-abs
        (q1227702-rational-cast
         q real-zero real-one real-add real-multiply
         real-negate real-inverse)
        real-zero real-negate real-less))))))

(defun q1227702-infinite-place-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     carrier zero one add multiply negate inverse place)
  (and
   (tamep-functionp place)
   (q1227702-infinite-place-laws-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less
    carrier zero one add multiply negate inverse place)))

(defun-sk q1227702-places-extensionally-equal-p
    (carrier left-place right-place)
  (forall (x)
    (implies
     (q1227702-member-p carrier x)
     (equal
      (q1227702-unary-value left-place x)
      (q1227702-unary-value right-place x)))))

(defun q1227702-same-infinite-place-p
    (carrier left-place right-place)
  (and
   (tamep-functionp left-place)
   (tamep-functionp right-place)
   (q1227702-places-extensionally-equal-p
    carrier left-place right-place)))

(defun q1227702-place-in-list-p (place places carrier)
  (if (consp places)
      (or
       (q1227702-same-infinite-place-p
        carrier place (car places))
       (q1227702-place-in-list-p
        place (cdr places) carrier))
    nil))

(defun q1227702-place-list-valid-p
    (places
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     carrier zero one add multiply negate inverse)
  (if (consp places)
      (and
       (q1227702-infinite-place-p
        real-carrier real-zero real-one real-add real-multiply
        real-negate real-inverse real-less
        carrier zero one add multiply negate inverse
        (car places))
       (not
        (q1227702-place-in-list-p
         (car places) (cdr places) carrier))
       (q1227702-place-list-valid-p
        (cdr places)
        real-carrier real-zero real-one real-add real-multiply
        real-negate real-inverse real-less
        carrier zero one add multiply negate inverse))
    (equal places nil)))

(defun-sk q1227702-place-coverage-p
    (places
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     carrier zero one add multiply negate inverse)
  (forall (place)
    (implies
     (q1227702-infinite-place-p
      real-carrier real-zero real-one real-add real-multiply
      real-negate real-inverse real-less
      carrier zero one add multiply negate inverse place)
     (q1227702-place-in-list-p
      place places carrier))))

(defun q1227702-infinite-place-list-p
    (places
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     carrier zero one add multiply negate inverse)
  (and
   (true-listp places)
   (consp places)
   (q1227702-place-list-valid-p
    places
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less
    carrier zero one add multiply negate inverse)
   (q1227702-place-coverage-p
    places
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less
    carrier zero one add multiply negate inverse)))

;; Basis modulo torsion and unique decomposition.

(defun q1227702-fund-product
    (fund-system exponents one multiply inverse)
  (if (and (consp fund-system) (consp exponents))
      (q1227702-binary-value
       multiply
       (q1227702-integer-power
        (car fund-system)
        (car exponents)
        one multiply inverse)
       (q1227702-fund-product
        (cdr fund-system)
        (cdr exponents)
        one multiply inverse))
    one))

(defun q1227702-unit-list-p
    (values carrier zero one add multiply negate inverse)
  (if (consp values)
      (and
       (q1227702-unit-p
        (car values)
        carrier zero one add multiply negate inverse)
       (q1227702-unit-list-p
        (cdr values)
        carrier zero one add multiply negate inverse))
    (equal values nil)))

(defun q1227702-decomposition-p
    (decomposition x fund-system
     carrier zero one add multiply negate inverse)
  (let ((zeta (nth 0 decomposition))
        (exponents (nth 1 decomposition)))
    (and
     (true-listp decomposition)
     (equal (len decomposition) 2)
     (q1227702-torsion-p
      zeta carrier zero one add multiply negate inverse)
     (true-listp exponents)
     (q1227702-integer-list-p exponents)
     (equal (len exponents) (len fund-system))
     (equal
      x
      (q1227702-binary-value
       multiply
       zeta
       (q1227702-fund-product
        fund-system exponents one multiply inverse))))))

(defun-sk q1227702-decomposition-exists-p
    (x fund-system
     carrier zero one add multiply negate inverse)
  (exists (decomposition)
    (q1227702-decomposition-p
     decomposition x fund-system
     carrier zero one add multiply negate inverse)))

(defun-sk q1227702-decomposition-unique-p
    (x fund-system
     carrier zero one add multiply negate inverse)
  (forall (left right)
    (implies
     (and
      (q1227702-decomposition-p
       left x fund-system
       carrier zero one add multiply negate inverse)
      (q1227702-decomposition-p
       right x fund-system
       carrier zero one add multiply negate inverse))
     (equal left right))))

(defun q1227702-unit-decomposition-p
    (x fund-system
     carrier zero one add multiply negate inverse)
  (and
   (q1227702-decomposition-exists-p
    x fund-system
    carrier zero one add multiply negate inverse)
   (q1227702-decomposition-unique-p
    x fund-system
    carrier zero one add multiply negate inverse)))

(defun-sk q1227702-all-unit-decompositions-p
    (fund-system
     carrier zero one add multiply negate inverse)
  (forall (x)
    (implies
     (q1227702-unit-p
      x carrier zero one add multiply negate inverse)
     (q1227702-unit-decomposition-p
      x fund-system
      carrier zero one add multiply negate inverse))))

(defun q1227702-fund-system-p
    (fund-system rank
     carrier zero one add multiply negate inverse)
  (and
   (true-listp fund-system)
   (equal (len fund-system) rank)
   (q1227702-unit-list-p
    fund-system
    carrier zero one add multiply negate inverse)
   (q1227702-all-unit-decompositions-p
    fund-system
    carrier zero one add multiply negate inverse)))

(defun-sk q1227702-fund-system-exists-p
    (rank carrier zero one add multiply negate inverse)
  (exists (fund-system)
    (q1227702-fund-system-p
     fund-system rank
     carrier zero one add multiply negate inverse)))

(defun thousand-theorems-q1227702-dirichlet-unit-theorem-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     real-square-root real-odd-root real-archimedean-bound
     carrier zero one add multiply negate inverse
     field-basis field-coordinates places)
  (implies
   (and
    (q1227702-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     real-square-root real-odd-root real-archimedean-bound)
    (q1227702-number-field-p
     carrier zero one add multiply negate inverse
     field-basis field-coordinates)
    (q1227702-infinite-place-list-p
     places
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     carrier zero one add multiply negate inverse))
   (q1227702-fund-system-exists-p
    (- (len places) 1)
    carrier zero one add multiply negate inverse)))

(value-triple :itpeval-statement-checked)
:q
