;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_a2:
;; the identity polynomial is exactly the real polynomial P with P(0) = 0
;; and P(x^2 + 1) = P(x)^2 + 1 for every real x. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A context tag selects a real closed ordered field. Conservative DEFSTUB
;; symbols provide its carrier, arithmetic, order, and root selectors; every
;; field, order, closure, square-root, and odd-degree-root law is an explicit
;; hypothesis of the statement. The latter two root laws are the standard
;; algebraic characterization of real closed ordered fields.
;;
;; Polynomials are canonical nonempty finite coefficient lists in ascending
;; degree order, so they range over every polynomial over the represented
;; field. The source assertion is first-order polynomial algebra. Since all
;; real closed fields are elementarily equivalent and the usual reals form
;; one, its validity over this presentation is bidirectionally equivalent to
;; its validity over all real-coefficient polynomials. No coefficient is
;; restricted to the rationals, algebraic numbers, or any bounded carrier.

(defstub putnam-1971-a2-real-p (context value) t)
(defstub putnam-1971-a2-zero (context) t)
(defstub putnam-1971-a2-one (context) t)
(defstub putnam-1971-a2-add (context left right) t)
(defstub putnam-1971-a2-multiply (context left right) t)
(defstub putnam-1971-a2-negate (context value) t)
(defstub putnam-1971-a2-inverse (context value) t)
(defstub putnam-1971-a2-less (context left right) t)
(defstub putnam-1971-a2-square-root (context value) t)
(defstub putnam-1971-a2-odd-root (context polynomial) t)

(defun putnam-1971-a2-coefficient-list-p (context coefficients)
  (if (consp coefficients)
      (and
       (putnam-1971-a2-real-p context (car coefficients))
       (putnam-1971-a2-coefficient-list-p
        context (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-1971-a2-polynomial-p (context polynomial)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-1971-a2-coefficient-list-p context polynomial)
   (or
    (equal (len polynomial) 1)
    (not
     (equal
      (car (last polynomial))
      (putnam-1971-a2-zero context))))))

(defun putnam-1971-a2-evaluate (context polynomial x)
  (if (consp polynomial)
      (putnam-1971-a2-add
       context
       (car polynomial)
       (putnam-1971-a2-multiply
        context
        x
        (putnam-1971-a2-evaluate
         context (cdr polynomial) x)))
    (putnam-1971-a2-zero context)))

(defun-sk putnam-1971-a2-field-laws-p (context)
  (forall (x y z)
    (implies
     (and
      (putnam-1971-a2-real-p context x)
      (putnam-1971-a2-real-p context y)
      (putnam-1971-a2-real-p context z))
     (and
      (putnam-1971-a2-real-p
       context (putnam-1971-a2-add context x y))
      (putnam-1971-a2-real-p
       context (putnam-1971-a2-multiply context x y))
      (putnam-1971-a2-real-p
       context (putnam-1971-a2-negate context x))
      (putnam-1971-a2-real-p
       context (putnam-1971-a2-inverse context x))
      (equal
       (putnam-1971-a2-add
        context (putnam-1971-a2-add context x y) z)
       (putnam-1971-a2-add
        context x (putnam-1971-a2-add context y z)))
      (equal
       (putnam-1971-a2-add context x y)
       (putnam-1971-a2-add context y x))
      (equal
       (putnam-1971-a2-add
        context x (putnam-1971-a2-zero context))
       x)
      (equal
       (putnam-1971-a2-add
        context x (putnam-1971-a2-negate context x))
       (putnam-1971-a2-zero context))
      (equal
       (putnam-1971-a2-multiply
        context
        (putnam-1971-a2-multiply context x y)
        z)
       (putnam-1971-a2-multiply
        context
        x
        (putnam-1971-a2-multiply context y z)))
      (equal
       (putnam-1971-a2-multiply context x y)
       (putnam-1971-a2-multiply context y x))
      (equal
       (putnam-1971-a2-multiply
        context x (putnam-1971-a2-one context))
       x)
      (implies
       (equal x (putnam-1971-a2-zero context))
       (equal
        (putnam-1971-a2-inverse context x)
        (putnam-1971-a2-zero context)))
      (implies
       (not (equal x (putnam-1971-a2-zero context)))
       (equal
        (putnam-1971-a2-multiply
         context x (putnam-1971-a2-inverse context x))
        (putnam-1971-a2-one context)))
      (equal
       (putnam-1971-a2-multiply
        context x (putnam-1971-a2-add context y z))
       (putnam-1971-a2-add
        context
        (putnam-1971-a2-multiply context x y)
        (putnam-1971-a2-multiply context x z)))))))

(defun-sk putnam-1971-a2-order-laws-p (context)
  (forall (x y z)
    (implies
     (and
      (putnam-1971-a2-real-p context x)
      (putnam-1971-a2-real-p context y)
      (putnam-1971-a2-real-p context z))
     (and
      (not (putnam-1971-a2-less context x x))
      (or
       (equal x y)
       (putnam-1971-a2-less context x y)
       (putnam-1971-a2-less context y x))
      (implies
       (and
        (putnam-1971-a2-less context x y)
        (putnam-1971-a2-less context y z))
       (putnam-1971-a2-less context x z))
      (implies
       (putnam-1971-a2-less context x y)
       (putnam-1971-a2-less
        context
        (putnam-1971-a2-add context x z)
        (putnam-1971-a2-add context y z)))
      (implies
       (and
        (putnam-1971-a2-less
         context (putnam-1971-a2-zero context) x)
        (putnam-1971-a2-less
         context (putnam-1971-a2-zero context) y))
       (putnam-1971-a2-less
        context
        (putnam-1971-a2-zero context)
        (putnam-1971-a2-multiply context x y)))))))

(defun-sk putnam-1971-a2-square-root-laws-p (context)
  (forall (x)
    (implies
     (and
      (putnam-1971-a2-real-p context x)
      (not
       (putnam-1971-a2-less
        context x (putnam-1971-a2-zero context))))
     (and
      (putnam-1971-a2-real-p
       context (putnam-1971-a2-square-root context x))
      (equal
       (putnam-1971-a2-multiply
        context
        (putnam-1971-a2-square-root context x)
        (putnam-1971-a2-square-root context x))
       x)))))

(defun-sk putnam-1971-a2-odd-root-laws-p (context)
  (forall (polynomial)
    (implies
     (and
      (putnam-1971-a2-polynomial-p context polynomial)
      (evenp (len polynomial)))
     (and
      (putnam-1971-a2-real-p
       context
       (putnam-1971-a2-odd-root context polynomial))
      (equal
       (putnam-1971-a2-evaluate
        context
        polynomial
        (putnam-1971-a2-odd-root context polynomial))
       (putnam-1971-a2-zero context))))))

(defun putnam-1971-a2-real-closed-field-p (context)
  (and
   (putnam-1971-a2-real-p
    context (putnam-1971-a2-zero context))
   (putnam-1971-a2-real-p
    context (putnam-1971-a2-one context))
   (not
    (equal
     (putnam-1971-a2-zero context)
     (putnam-1971-a2-one context)))
   (putnam-1971-a2-less
    context
    (putnam-1971-a2-zero context)
    (putnam-1971-a2-one context))
   (putnam-1971-a2-field-laws-p context)
   (putnam-1971-a2-order-laws-p context)
   (putnam-1971-a2-square-root-laws-p context)
   (putnam-1971-a2-odd-root-laws-p context)))

(defun-sk putnam-1971-a2-functional-equation-p
    (context polynomial)
  (forall (x)
    (implies
     (putnam-1971-a2-real-p context x)
     (equal
      (putnam-1971-a2-evaluate
       context
       polynomial
       (putnam-1971-a2-add
        context
        (putnam-1971-a2-multiply context x x)
        (putnam-1971-a2-one context)))
      (putnam-1971-a2-add
       context
       (putnam-1971-a2-multiply
        context
        (putnam-1971-a2-evaluate context polynomial x)
        (putnam-1971-a2-evaluate context polynomial x))
       (putnam-1971-a2-one context))))))

(defun putnam-1971-a2-source-condition-p (context polynomial)
  (and
   (equal
    (putnam-1971-a2-evaluate
     context polynomial (putnam-1971-a2-zero context))
    (putnam-1971-a2-zero context))
   (putnam-1971-a2-functional-equation-p
    context polynomial)))

(defun putnam-1971-a2-identity-polynomial-p
    (context polynomial)
  (equal
   polynomial
   (list
    (putnam-1971-a2-zero context)
    (putnam-1971-a2-one context))))

(defun-sk putnambench-putnam-1971-a2-statement (context)
  (forall (polynomial)
    (implies
     (and
      (putnam-1971-a2-real-closed-field-p context)
      (putnam-1971-a2-polynomial-p context polynomial))
     (equal
      (putnam-1971-a2-source-condition-p context polynomial)
      (putnam-1971-a2-identity-polynomial-p
       context polynomial)))))

(value-triple :itpeval-statement-checked)
:q
