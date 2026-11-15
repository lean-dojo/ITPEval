;; Statement-only formalization of thousand-theorems corpus artifact Q656645,
;; "Hilbert's basis theorem": the univariate polynomial ring over a
;; commutative Noetherian ring is Noetherian. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame function objects represent an arbitrary commutative ring and arbitrary
;; ideal-membership predicates. No carrier or ideal is enumerated.
;; Noetherianity means that every ideal has an internally existential finite
;; generating list, with its coefficient witnesses also internally quantified.
;;
;; Polynomials are canonical finite-support coefficient lists in increasing
;; degree order: NIL is zero, and a nonzero polynomial has a nonzero final
;; coefficient. The definitions below give exact coefficientwise addition,
;; negation, and convolution multiplication over the supplied ring operations.
;; Thus polynomial degree, ideal size, and generator count remain unbounded.

(defun q656645-member-p (predicate value)
  (if (apply$ predicate (list value))
      t
    nil))

(defun q656645-unary-value (operation value)
  (apply$ operation (list value)))

(defun q656645-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun q656645-neg (negation value)
  (q656645-unary-value negation value))

(defun q656645-add (addition left right)
  (q656645-binary-value addition left right))

(defun q656645-mul (multiplication left right)
  (q656645-binary-value multiplication left right))

;; Commutative rings and their ideals.

(defun-sk q656645-commutative-ring-laws-p
    (carrier zero one addition multiplication negation)
  (forall (x y z)
    (and
     (implies
      (q656645-member-p carrier x)
      (and
       (q656645-member-p carrier (q656645-neg negation x))
       (equal (q656645-add addition x zero) x)
       (equal (q656645-add addition zero x) x)
       (equal
        (q656645-add addition x (q656645-neg negation x))
        zero)
       (equal
        (q656645-add addition (q656645-neg negation x) x)
        zero)
       (equal (q656645-mul multiplication x one) x)
       (equal (q656645-mul multiplication one x) x)))
     (implies
      (and
       (q656645-member-p carrier x)
       (q656645-member-p carrier y))
      (and
       (q656645-member-p
        carrier (q656645-add addition x y))
       (q656645-member-p
        carrier (q656645-mul multiplication x y))
       (equal
        (q656645-add addition x y)
        (q656645-add addition y x))
       (equal
        (q656645-mul multiplication x y)
        (q656645-mul multiplication y x))))
     (implies
      (and
       (q656645-member-p carrier x)
       (q656645-member-p carrier y)
       (q656645-member-p carrier z))
      (and
       (equal
        (q656645-add
         addition (q656645-add addition x y) z)
        (q656645-add
         addition x (q656645-add addition y z)))
       (equal
        (q656645-mul
         multiplication
         (q656645-mul multiplication x y)
         z)
        (q656645-mul
         multiplication
         x
         (q656645-mul multiplication y z)))
       (equal
        (q656645-mul
         multiplication
         x
         (q656645-add addition y z))
        (q656645-add
         addition
         (q656645-mul multiplication x y)
         (q656645-mul multiplication x z)))
       (equal
        (q656645-mul
         multiplication
         (q656645-add addition x y)
         z)
        (q656645-add
         addition
         (q656645-mul multiplication x z)
         (q656645-mul multiplication y z))))))))

(defun q656645-commutative-ring-p
    (carrier zero one addition multiplication negation)
  (and
   (tamep-functionp carrier)
   (tamep-functionp addition)
   (tamep-functionp multiplication)
   (tamep-functionp negation)
   (q656645-member-p carrier zero)
   (q656645-member-p carrier one)
   (q656645-commutative-ring-laws-p
    carrier zero one addition multiplication negation)))

(defun-sk q656645-ideal-laws-p
    (carrier zero addition multiplication negation ideal)
  (forall (a x y)
    (and
     (implies
      (q656645-member-p ideal x)
      (and
       (q656645-member-p carrier x)
       (q656645-member-p
        ideal (q656645-neg negation x))))
     (implies
      (and
       (q656645-member-p ideal x)
       (q656645-member-p ideal y))
      (q656645-member-p
       ideal (q656645-add addition x y)))
     (implies
      (and
       (q656645-member-p carrier a)
       (q656645-member-p ideal x))
      (q656645-member-p
       ideal (q656645-mul multiplication a x))))))

(defun q656645-ideal-p
    (carrier zero addition multiplication negation ideal)
  (and
   (tamep-functionp ideal)
   (q656645-member-p ideal zero)
   (q656645-ideal-laws-p
    carrier zero addition multiplication negation ideal)))

(defun q656645-ring-list-p (carrier values)
  (if (consp values)
      (and
       (q656645-member-p carrier (car values))
       (q656645-ring-list-p carrier (cdr values)))
    (equal values nil)))

(defun q656645-linear-combination
    (zero addition multiplication coefficients generators)
  (if (and (consp coefficients)
           (consp generators))
      (q656645-add
       addition
       (q656645-mul
        multiplication (car coefficients) (car generators))
       (q656645-linear-combination
        zero
        addition
        multiplication
        (cdr coefficients)
        (cdr generators)))
    zero))

(defun-sk q656645-generated-representation-p
    (carrier zero addition multiplication generators value)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (equal (len coefficients) (len generators))
     (q656645-ring-list-p carrier coefficients)
     (equal
      value
      (q656645-linear-combination
       zero addition multiplication coefficients generators)))))

(defun-sk q656645-generated-by-law-p
    (carrier zero addition multiplication ideal generators)
  (forall (x)
    (implies
     (q656645-member-p carrier x)
     (iff
      (q656645-member-p ideal x)
      (q656645-generated-representation-p
       carrier zero addition multiplication generators x)))))

(defun q656645-generated-by-p
    (carrier zero addition multiplication ideal generators)
  (and
   (true-listp generators)
   (q656645-ring-list-p carrier generators)
   (q656645-generated-by-law-p
    carrier zero addition multiplication ideal generators)))

(defun-sk q656645-finitely-generated-ideal-p
    (carrier zero addition multiplication ideal)
  (exists (generators)
    (q656645-generated-by-p
     carrier zero addition multiplication ideal generators)))

(defun-sk q656645-noetherian-p
    (carrier zero addition multiplication negation)
  (forall (ideal)
    (implies
     (q656645-ideal-p
      carrier zero addition multiplication negation ideal)
     (q656645-finitely-generated-ideal-p
      carrier zero addition multiplication ideal))))

;; Canonical univariate polynomials over the arbitrary base ring.

(defun q656645-polynomial-p (carrier zero polynomial)
  (and
   (true-listp polynomial)
   (q656645-ring-list-p carrier polynomial)
   (or
    (endp polynomial)
    (not (equal (car (last polynomial)) zero)))))

(defun q656645-polynomial-list-p
    (carrier zero polynomials)
  (if (consp polynomials)
      (and
       (q656645-polynomial-p carrier zero (car polynomials))
       (q656645-polynomial-list-p
        carrier zero (cdr polynomials)))
    (equal polynomials nil)))

(defun q656645-trim-polynomial (coefficients zero)
  (if (consp coefficients)
      (let ((trimmed-tail
             (q656645-trim-polynomial (cdr coefficients) zero)))
        (if (and
             (endp trimmed-tail)
             (equal (car coefficients) zero))
            nil
          (cons (car coefficients) trimmed-tail)))
    nil))

(defun q656645-polynomial-add-raw
    (addition left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons
         (q656645-add addition (car left) (car right))
         (q656645-polynomial-add-raw
          addition (cdr left) (cdr right)))
      left))
   ((consp right) right)
   (t nil)))

(defun q656645-polynomial-add
    (zero addition left right)
  (q656645-trim-polynomial
   (q656645-polynomial-add-raw addition left right)
   zero))

(defun q656645-polynomial-neg-raw
    (negation polynomial)
  (if (consp polynomial)
      (cons
       (q656645-neg negation (car polynomial))
       (q656645-polynomial-neg-raw negation (cdr polynomial)))
    nil))

(defun q656645-polynomial-neg
    (zero negation polynomial)
  (q656645-trim-polynomial
   (q656645-polynomial-neg-raw negation polynomial)
   zero))

(defun q656645-polynomial-scale-raw
    (multiplication scalar polynomial)
  (if (consp polynomial)
      (cons
       (q656645-mul multiplication scalar (car polynomial))
       (q656645-polynomial-scale-raw
        multiplication scalar (cdr polynomial)))
    nil))

(defun q656645-polynomial-mul-raw
    (zero addition multiplication left right)
  (if (consp left)
      (q656645-polynomial-add-raw
       addition
       (q656645-polynomial-scale-raw
        multiplication (car left) right)
       (cons
        zero
        (q656645-polynomial-mul-raw
         zero
         addition
         multiplication
         (cdr left)
         right)))
    nil))

(defun q656645-polynomial-mul
    (zero addition multiplication left right)
  (q656645-trim-polynomial
   (q656645-polynomial-mul-raw
    zero addition multiplication left right)
   zero))

;; Ideals and finite generation in the exact polynomial ring.

(defun-sk q656645-polynomial-ideal-laws-p
    (carrier zero addition multiplication negation ideal)
  (forall (a x y)
    (and
     (implies
      (q656645-member-p ideal x)
      (and
       (q656645-polynomial-p carrier zero x)
       (q656645-member-p
        ideal
        (q656645-polynomial-neg zero negation x))))
     (implies
      (and
       (q656645-member-p ideal x)
       (q656645-member-p ideal y))
      (q656645-member-p
       ideal
       (q656645-polynomial-add zero addition x y)))
     (implies
      (and
       (q656645-polynomial-p carrier zero a)
       (q656645-member-p ideal x))
      (q656645-member-p
       ideal
       (q656645-polynomial-mul
        zero addition multiplication a x))))))

(defun q656645-polynomial-ideal-p
    (carrier zero addition multiplication negation ideal)
  (and
   (tamep-functionp ideal)
   (q656645-member-p ideal nil)
   (q656645-polynomial-ideal-laws-p
    carrier zero addition multiplication negation ideal)))

(defun q656645-polynomial-linear-combination
    (zero addition multiplication coefficients generators)
  (if (and (consp coefficients)
           (consp generators))
      (q656645-polynomial-add
       zero
       addition
       (q656645-polynomial-mul
        zero
        addition
        multiplication
        (car coefficients)
        (car generators))
       (q656645-polynomial-linear-combination
        zero
        addition
        multiplication
        (cdr coefficients)
        (cdr generators)))
    nil))

(defun-sk q656645-polynomial-generated-representation-p
    (carrier zero addition multiplication generators value)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (equal (len coefficients) (len generators))
     (q656645-polynomial-list-p carrier zero coefficients)
     (equal
      value
      (q656645-polynomial-linear-combination
       zero addition multiplication coefficients generators)))))

(defun-sk q656645-polynomial-generated-by-law-p
    (carrier zero addition multiplication ideal generators)
  (forall (polynomial)
    (implies
     (q656645-polynomial-p carrier zero polynomial)
     (iff
      (q656645-member-p ideal polynomial)
      (q656645-polynomial-generated-representation-p
       carrier
       zero
       addition
       multiplication
       generators
       polynomial)))))

(defun q656645-polynomial-generated-by-p
    (carrier zero addition multiplication ideal generators)
  (and
   (true-listp generators)
   (q656645-polynomial-list-p carrier zero generators)
   (q656645-polynomial-generated-by-law-p
    carrier zero addition multiplication ideal generators)))

(defun-sk q656645-polynomial-finitely-generated-ideal-p
    (carrier zero addition multiplication ideal)
  (exists (generators)
    (q656645-polynomial-generated-by-p
     carrier zero addition multiplication ideal generators)))

(defun-sk q656645-polynomial-noetherian-p
    (carrier zero addition multiplication negation)
  (forall (ideal)
    (implies
     (q656645-polynomial-ideal-p
      carrier zero addition multiplication negation ideal)
     (q656645-polynomial-finitely-generated-ideal-p
      carrier zero addition multiplication ideal))))

(defun-sk
    thousand-theorems-q656645-hilbert-s-basis-theorem-statement
    ()
  (forall
    (carrier zero one addition multiplication negation)
    (implies
     (and
      (q656645-commutative-ring-p
       carrier zero one addition multiplication negation)
      (q656645-noetherian-p
       carrier zero addition multiplication negation))
     (q656645-polynomial-noetherian-p
      carrier zero addition multiplication negation))))

(value-triple :itpeval-statement-checked)
:q
