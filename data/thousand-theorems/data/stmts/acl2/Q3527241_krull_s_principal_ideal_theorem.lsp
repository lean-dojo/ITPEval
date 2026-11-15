;; Statement-only formalization of thousand-theorems corpus artifact Q3527241,
;; "Krull's principal ideal theorem": in a commutative Noetherian ring, every
;; prime ideal minimal over a principal ideal has height at most one. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame function objects represent the arbitrary ring carrier, operations, and
;; ideal membership predicates. No carrier or ideal is enumerated. Noetherianity
;; is expressed by finite generation of every ideal, with generators and their
;; coefficients kept under the statement's internal existential quantifiers.

(defun q3527241-member-p (predicate value)
  (if (apply$ predicate (list value))
      t
    nil))

(defun q3527241-unary-value (operation value)
  (apply$ operation (list value)))

(defun q3527241-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun q3527241-neg (negation value)
  (q3527241-unary-value negation value))

(defun q3527241-add (addition left right)
  (q3527241-binary-value addition left right))

(defun q3527241-mul (multiplication left right)
  (q3527241-binary-value multiplication left right))

(defun-sk q3527241-commutative-ring-laws-p
    (carrier zero one addition multiplication negation)
  (forall (x y z)
    (and
     (implies
      (q3527241-member-p carrier x)
      (and
       (q3527241-member-p
        carrier (q3527241-neg negation x))
       (equal (q3527241-add addition x zero) x)
       (equal (q3527241-add addition zero x) x)
       (equal
        (q3527241-add addition x (q3527241-neg negation x))
        zero)
       (equal
        (q3527241-add addition (q3527241-neg negation x) x)
        zero)
       (equal (q3527241-mul multiplication x one) x)
       (equal (q3527241-mul multiplication one x) x)))
     (implies
      (and
       (q3527241-member-p carrier x)
       (q3527241-member-p carrier y))
      (and
       (q3527241-member-p
        carrier (q3527241-add addition x y))
       (q3527241-member-p
        carrier (q3527241-mul multiplication x y))
       (equal
        (q3527241-add addition x y)
        (q3527241-add addition y x))
       (equal
        (q3527241-mul multiplication x y)
        (q3527241-mul multiplication y x))))
     (implies
      (and
       (q3527241-member-p carrier x)
       (q3527241-member-p carrier y)
       (q3527241-member-p carrier z))
      (and
       (equal
        (q3527241-add
         addition (q3527241-add addition x y) z)
        (q3527241-add
         addition x (q3527241-add addition y z)))
       (equal
        (q3527241-mul
         multiplication
         (q3527241-mul multiplication x y)
         z)
        (q3527241-mul
         multiplication
         x
         (q3527241-mul multiplication y z)))
       (equal
        (q3527241-mul
         multiplication
         x
         (q3527241-add addition y z))
        (q3527241-add
         addition
         (q3527241-mul multiplication x y)
         (q3527241-mul multiplication x z)))
       (equal
        (q3527241-mul
         multiplication
         (q3527241-add addition x y)
         z)
        (q3527241-add
         addition
         (q3527241-mul multiplication x z)
         (q3527241-mul multiplication y z))))))))

(defun q3527241-commutative-ring-p
    (carrier zero one addition multiplication negation)
  (and
   (tamep-functionp carrier)
   (tamep-functionp addition)
   (tamep-functionp multiplication)
   (tamep-functionp negation)
   (q3527241-member-p carrier zero)
   (q3527241-member-p carrier one)
   (q3527241-commutative-ring-laws-p
    carrier zero one addition multiplication negation)))

(defun-sk q3527241-ideal-laws-p
    (carrier zero addition multiplication negation ideal)
  (forall (a x y)
    (and
     (implies
      (q3527241-member-p ideal x)
      (and
       (q3527241-member-p carrier x)
       (q3527241-member-p
        ideal (q3527241-neg negation x))))
     (implies
      (and
       (q3527241-member-p ideal x)
       (q3527241-member-p ideal y))
      (q3527241-member-p
       ideal (q3527241-add addition x y)))
     (implies
      (and
       (q3527241-member-p carrier a)
       (q3527241-member-p ideal x))
      (q3527241-member-p
       ideal (q3527241-mul multiplication a x))))))

(defun q3527241-ideal-p
    (carrier zero addition multiplication negation ideal)
  (and
   (tamep-functionp ideal)
   (q3527241-member-p ideal zero)
   (q3527241-ideal-laws-p
    carrier zero addition multiplication negation ideal)))

(defun-sk q3527241-ideal-included-p (carrier left right)
  (forall (x)
    (implies
     (q3527241-member-p carrier x)
     (implies
      (q3527241-member-p left x)
      (q3527241-member-p right x)))))

(defun q3527241-strict-ideal-included-p
    (carrier left right)
  (and
   (q3527241-ideal-included-p carrier left right)
   (not (q3527241-ideal-included-p carrier right left))))

(defun-sk q3527241-prime-multiplication-law-p
    (carrier multiplication ideal)
  (forall (x y)
    (implies
     (and
      (q3527241-member-p carrier x)
      (q3527241-member-p carrier y)
      (q3527241-member-p
       ideal (q3527241-mul multiplication x y)))
     (or
      (q3527241-member-p ideal x)
      (q3527241-member-p ideal y)))))

(defun q3527241-prime-ideal-p
    (carrier zero one addition multiplication negation ideal)
  (and
   (q3527241-ideal-p
    carrier zero addition multiplication negation ideal)
   (not (q3527241-member-p ideal one))
   (q3527241-prime-multiplication-law-p
    carrier multiplication ideal)))

(defun q3527241-ring-list-p (carrier values)
  (if (consp values)
      (and
       (q3527241-member-p carrier (car values))
       (q3527241-ring-list-p carrier (cdr values)))
    (equal values nil)))

(defun q3527241-linear-combination
    (zero addition multiplication coefficients generators)
  (if (and (consp coefficients)
           (consp generators))
      (q3527241-add
       addition
       (q3527241-mul
        multiplication (car coefficients) (car generators))
       (q3527241-linear-combination
        zero
        addition
        multiplication
        (cdr coefficients)
        (cdr generators)))
    zero))

(defun-sk q3527241-generated-representation-p
    (carrier zero addition multiplication generators value)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (equal (len coefficients) (len generators))
     (q3527241-ring-list-p carrier coefficients)
     (equal
      value
      (q3527241-linear-combination
       zero addition multiplication coefficients generators)))))

(defun-sk q3527241-generated-by-law-p
    (carrier zero addition multiplication ideal generators)
  (forall (x)
    (implies
     (q3527241-member-p carrier x)
     (iff
      (q3527241-member-p ideal x)
      (q3527241-generated-representation-p
       carrier zero addition multiplication generators x)))))

(defun q3527241-generated-by-p
    (carrier zero addition multiplication ideal generators)
  (and
   (true-listp generators)
   (q3527241-ring-list-p carrier generators)
   (q3527241-generated-by-law-p
    carrier zero addition multiplication ideal generators)))

(defun-sk q3527241-finitely-generated-ideal-p
    (carrier zero addition multiplication ideal)
  (exists (generators)
    (q3527241-generated-by-p
     carrier zero addition multiplication ideal generators)))

(defun-sk q3527241-noetherian-p
    (carrier zero addition multiplication negation)
  (forall (ideal)
    (implies
     (q3527241-ideal-p
      carrier zero addition multiplication negation ideal)
     (q3527241-finitely-generated-ideal-p
      carrier zero addition multiplication ideal))))

(defun-sk q3527241-principal-ideal-p
    (carrier zero addition multiplication ideal)
  (exists (generator)
    (and
     (q3527241-member-p carrier generator)
     (q3527241-generated-by-p
      carrier
      zero
      addition
      multiplication
      ideal
      (list generator)))))

(defun-sk q3527241-minimal-prime-law-p
    (carrier zero one addition multiplication negation ideal prime)
  (forall (candidate)
    (implies
     (and
      (q3527241-prime-ideal-p
       carrier
       zero
       one
       addition
       multiplication
       negation
       candidate)
      (q3527241-ideal-included-p carrier ideal candidate)
      (q3527241-ideal-included-p carrier candidate prime))
     (q3527241-ideal-included-p carrier prime candidate))))

(defun q3527241-minimal-prime-over-p
    (carrier zero one addition multiplication negation ideal prime)
  (and
   (q3527241-prime-ideal-p
    carrier zero one addition multiplication negation prime)
   (q3527241-ideal-included-p carrier ideal prime)
   (q3527241-minimal-prime-law-p
    carrier zero one addition multiplication negation ideal prime)))

;; For a prime ideal P, height(P) <= 1 exactly when there do not exist prime
;; ideals Q0 < Q1 < P. This order-theoretic form avoids replacing the source's
;; possibly infinite ideal lattice by a finite carrier or a numeric bound.

(defun-sk q3527241-height-at-most-one-p
    (carrier zero one addition multiplication negation prime)
  (forall (lower middle)
    (not
     (and
      (q3527241-prime-ideal-p
       carrier
       zero
       one
       addition
       multiplication
       negation
       lower)
      (q3527241-prime-ideal-p
       carrier
       zero
       one
       addition
       multiplication
       negation
       middle)
      (q3527241-strict-ideal-included-p
       carrier lower middle)
      (q3527241-strict-ideal-included-p
       carrier middle prime)))))

(defun-sk
    thousand-theorems-q3527241-krull-s-principal-ideal-theorem-statement
    ()
  (forall
    (carrier zero one addition multiplication negation ideal prime)
    (implies
     (and
      (q3527241-commutative-ring-p
       carrier zero one addition multiplication negation)
      (q3527241-noetherian-p
       carrier zero addition multiplication negation)
      (q3527241-ideal-p
       carrier zero addition multiplication negation ideal)
      (q3527241-principal-ideal-p
       carrier zero addition multiplication ideal)
      (q3527241-minimal-prime-over-p
       carrier
       zero
       one
       addition
       multiplication
       negation
       ideal
       prime))
     (q3527241-height-at-most-one-p
      carrier
      zero
      one
      addition
      multiplication
      negation
      prime))))

(value-triple :itpeval-statement-checked)
:q
