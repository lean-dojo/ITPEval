;; Statement-only formalization of thousand-theorems corpus artifact Q1008566,
;; "Gauss–Lucas theorem": every zero of the derivative of a nonconstant
;; complex polynomial lies in the convex hull of its zeros and equals the
;; center of mass determined by the source's derivative-root weights.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars form an arbitrary real closed ordered field. Complex numbers are
;; pairs of scalars, and polynomials are canonical coefficient lists in
;; ascending degree order. Real closed fields are elementarily equivalent, so
;; this first-order polynomial formulation is equivalent to the source theorem
;; over the real and complex numbers.
;;
;; DEFUN-SK supplies all unbounded quantifiers. A complete root multiset is an
;; internal existential witness, never an external statement parameter.
;; Repeating each root according to its multiplicity turns the source sum of
;; rootMultiplicity/||z-w||^2 over distinct roots into the equal per-occurrence
;; sum used below. Caratheodory's theorem in the real plane makes membership in
;; the convex hull equivalent to a convex combination of three roots.

(defun q1008566-add (add left right)
  (apply$ add (list left right)))

(defun q1008566-mul (mul left right)
  (apply$ mul (list left right)))

(defun q1008566-neg (neg value)
  (apply$ neg (list value)))

(defun q1008566-inv (inv value)
  (apply$ inv (list value)))

(defun q1008566-lt (lt left right)
  (apply$ lt (list left right)))

(defun q1008566-sqrt (square-root value)
  (apply$ square-root (list value)))

(defun-sk q1008566-field-laws-p
    (carrier zero one add mul neg inv)
  (forall (x y z)
    (implies
     (and
      (apply$ carrier (list x))
      (apply$ carrier (list y))
      (apply$ carrier (list z)))
     (let* ((xy-add (q1008566-add add x y))
            (yz-add (q1008566-add add y z))
            (xy-mul (q1008566-mul mul x y))
            (yz-mul (q1008566-mul mul y z))
            (neg-x (q1008566-neg neg x))
            (inv-x (q1008566-inv inv x)))
       (and
        (apply$ carrier (list xy-add))
        (apply$ carrier (list xy-mul))
        (apply$ carrier (list neg-x))
        (apply$ carrier (list inv-x))
        (equal
         (q1008566-add add xy-add z)
         (q1008566-add add x yz-add))
        (equal
         (q1008566-mul mul xy-mul z)
         (q1008566-mul mul x yz-mul))
        (equal xy-add (q1008566-add add y x))
        (equal xy-mul (q1008566-mul mul y x))
        (equal (q1008566-add add x zero) x)
        (equal (q1008566-add add x neg-x) zero)
        (equal (q1008566-mul mul x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (q1008566-mul mul x inv-x) one))
        (equal
         (q1008566-mul mul x yz-add)
         (q1008566-add
          add
          (q1008566-mul mul x y)
          (q1008566-mul mul x z))))))))

(defun-sk q1008566-order-laws-p
    (carrier zero add mul lt)
  (forall (x y z)
    (implies
     (and
      (apply$ carrier (list x))
      (apply$ carrier (list y))
      (apply$ carrier (list z)))
     (and
      (not (q1008566-lt lt x x))
      (or
       (q1008566-lt lt x y)
       (equal x y)
       (q1008566-lt lt y x))
      (implies
       (and
        (q1008566-lt lt x y)
        (q1008566-lt lt y z))
       (q1008566-lt lt x z))
      (implies
       (q1008566-lt lt x y)
       (q1008566-lt
        lt
        (q1008566-add add x z)
        (q1008566-add add y z)))
      (implies
       (and
        (q1008566-lt lt zero x)
        (q1008566-lt lt zero y))
       (q1008566-lt
        lt zero (q1008566-mul mul x y)))))))

(defun-sk q1008566-square-root-laws-p
    (carrier zero mul lt square-root)
  (forall (x)
    (implies
     (and
      (apply$ carrier (list x))
      (not (q1008566-lt lt x zero)))
     (let ((root (q1008566-sqrt square-root x)))
       (and
        (apply$ carrier (list root))
        (not (q1008566-lt lt root zero))
        (equal (q1008566-mul mul root root) x))))))

(defun q1008566-field-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (q1008566-add
     add
     one
     (q1008566-field-natural (- n 1) zero one add))))

(defun q1008566-real-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (q1008566-real-coefficient-list-p
      (cdr coefficients) carrier))))

(defun q1008566-real-polynomial-p
    (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (q1008566-real-coefficient-list-p coefficients carrier)
   (or
    (equal (len coefficients) 1)
    (not (equal (car (last coefficients)) zero)))))

(defun q1008566-real-polynomial-eval
    (coefficients x zero add mul)
  (if (endp coefficients)
      zero
    (q1008566-add
     add
     (car coefficients)
     (q1008566-mul
      mul
      x
      (q1008566-real-polynomial-eval
       (cdr coefficients) x zero add mul)))))

(defun-sk q1008566-odd-root-laws-p
    (carrier zero add mul odd-root)
  (forall (coefficients)
    (implies
     (and
      (q1008566-real-polynomial-p
       coefficients carrier zero)
      (evenp (len coefficients)))
     (let ((root (apply$ odd-root (list coefficients))))
       (and
        (apply$ carrier (list root))
        (equal
         (q1008566-real-polynomial-eval
          coefficients root zero add mul)
         zero))))))

(defun q1008566-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (tamep-functionp lt)
   (tamep-functionp square-root)
   (tamep-functionp odd-root)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (q1008566-field-laws-p
    carrier zero one add mul neg inv)
   (q1008566-order-laws-p
    carrier zero add mul lt)
   (q1008566-square-root-laws-p
    carrier zero mul lt square-root)
   (q1008566-odd-root-laws-p
    carrier zero add mul odd-root)))

(defun q1008566-complex-p (z carrier)
  (and
   (consp z)
   (apply$ carrier (list (car z)))
   (apply$ carrier (list (cdr z)))))

(defun q1008566-complex-zero (zero)
  (cons zero zero))

(defun q1008566-complex-one (zero one)
  (cons one zero))

(defun q1008566-complex-add (left right add)
  (cons
   (q1008566-add add (car left) (car right))
   (q1008566-add add (cdr left) (cdr right))))

(defun q1008566-complex-neg (value neg)
  (cons
   (q1008566-neg neg (car value))
   (q1008566-neg neg (cdr value))))

(defun q1008566-complex-mul (left right add mul neg)
  (let ((ac (q1008566-mul mul (car left) (car right)))
        (bd (q1008566-mul mul (cdr left) (cdr right)))
        (ad (q1008566-mul mul (car left) (cdr right)))
        (bc (q1008566-mul mul (cdr left) (car right))))
    (cons
     (q1008566-add add ac (q1008566-neg neg bd))
     (q1008566-add add ad bc))))

(defun q1008566-complex-sub (left right add neg)
  (q1008566-complex-add
   left (q1008566-complex-neg right neg) add))

(defun q1008566-complex-scale (scalar value mul)
  (cons
   (q1008566-mul mul scalar (car value))
   (q1008566-mul mul scalar (cdr value))))

(defun q1008566-complex-norm-square (value add mul)
  (q1008566-add
   add
   (q1008566-mul mul (car value) (car value))
   (q1008566-mul mul (cdr value) (cdr value))))

(defun q1008566-complex-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (q1008566-complex-p (car coefficients) carrier)
     (q1008566-complex-coefficient-list-p
      (cdr coefficients) carrier))))

(defun q1008566-positive-degree-polynomial-p
    (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp (cdr coefficients))
   (q1008566-complex-coefficient-list-p
    coefficients carrier)
   (not
    (equal
     (car (last coefficients))
     (q1008566-complex-zero zero)))))

(defun q1008566-complex-polynomial-eval
    (coefficients x zero add mul neg)
  (if (endp coefficients)
      (q1008566-complex-zero zero)
    (q1008566-complex-add
     (car coefficients)
     (q1008566-complex-mul
      x
      (q1008566-complex-polynomial-eval
       (cdr coefficients) x zero add mul neg)
      add mul neg)
     add)))

(defun q1008566-complex-polynomial-derivative-aux
    (coefficients index zero one add mul)
  (if (endp coefficients)
      nil
    (cons
     (q1008566-complex-scale
      (q1008566-field-natural index zero one add)
      (car coefficients)
      mul)
     (q1008566-complex-polynomial-derivative-aux
      (cdr coefficients) (+ index 1) zero one add mul))))

(defun q1008566-complex-polynomial-derivative
    (coefficients zero one add mul)
  (if (endp coefficients)
      nil
    (q1008566-complex-polynomial-derivative-aux
     (cdr coefficients) 1 zero one add mul)))

(defun q1008566-complex-polynomial-add
    (left right add)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons
     (q1008566-complex-add (car left) (car right) add)
     (q1008566-complex-polynomial-add
      (cdr left) (cdr right) add)))))

(defun q1008566-complex-polynomial-scale
    (scalar coefficients add mul neg)
  (if (endp coefficients)
      nil
    (cons
     (q1008566-complex-mul
      scalar (car coefficients) add mul neg)
     (q1008566-complex-polynomial-scale
      scalar (cdr coefficients) add mul neg))))

(defun q1008566-multiply-by-linear
    (coefficients root zero add mul neg)
  (q1008566-complex-polynomial-add
   (q1008566-complex-polynomial-scale
    (q1008566-complex-neg root neg)
    coefficients add mul neg)
   (cons (q1008566-complex-zero zero) coefficients)
   add))

(defun q1008566-root-product
    (roots zero one add mul neg)
  (if (endp roots)
      (list (q1008566-complex-one zero one))
    (q1008566-multiply-by-linear
     (q1008566-root-product
      (cdr roots) zero one add mul neg)
     (car roots)
     zero add mul neg)))

(defun q1008566-roots-p (roots carrier)
  (if (endp roots)
      (equal roots nil)
    (and
     (q1008566-complex-p (car roots) carrier)
     (q1008566-roots-p (cdr roots) carrier))))

(defun q1008566-factorization-p
    (coefficients roots carrier zero one add mul neg)
  (and
   (true-listp roots)
   (equal (len roots) (- (len coefficients) 1))
   (q1008566-roots-p roots carrier)
   (equal
    (q1008566-complex-polynomial-scale
     (car (last coefficients))
     (q1008566-root-product
      roots zero one add mul neg)
     add mul neg)
    coefficients)))

(defun q1008566-root-weight
    (root coefficients z zero one add mul neg inv)
  (if
      (equal
       (q1008566-complex-polynomial-eval
        coefficients z zero add mul neg)
       (q1008566-complex-zero zero))
      (if (equal root z) one zero)
    (q1008566-inv
     inv
     (q1008566-complex-norm-square
      (q1008566-complex-sub z root add neg)
      add mul))))

(defun q1008566-root-weight-sum
    (roots coefficients z zero one add mul neg inv)
  (if (endp roots)
      zero
    (q1008566-add
     add
     (q1008566-root-weight
      (car roots) coefficients z
      zero one add mul neg inv)
     (q1008566-root-weight-sum
      (cdr roots) coefficients z
      zero one add mul neg inv))))

(defun q1008566-weighted-root-sum
    (roots coefficients z zero one add mul neg inv)
  (if (endp roots)
      (q1008566-complex-zero zero)
    (q1008566-complex-add
     (q1008566-complex-scale
      (q1008566-root-weight
       (car roots) coefficients z
       zero one add mul neg inv)
      (car roots)
      mul)
     (q1008566-weighted-root-sum
      (cdr roots) coefficients z
      zero one add mul neg inv)
     add)))

(defun q1008566-center-mass-equality-p
    (roots coefficients z zero one add mul neg inv)
  (let ((total
         (q1008566-root-weight-sum
          roots coefficients z
          zero one add mul neg inv))
        (weighted-sum
         (q1008566-weighted-root-sum
          roots coefficients z
          zero one add mul neg inv)))
    (equal
     z
     (q1008566-complex-scale
      (q1008566-inv inv total)
      weighted-sum
      mul))))

(defun-sk q1008566-center-mass-statement-p
    (coefficients z carrier zero one add mul neg inv)
  (exists (roots)
    (and
     (q1008566-factorization-p
      coefficients roots carrier
      zero one add mul neg)
     (q1008566-center-mass-equality-p
      roots coefficients z
      zero one add mul neg inv))))

(defun q1008566-polynomial-root-p
    (root coefficients carrier zero add mul neg)
  (and
   (q1008566-complex-p root carrier)
   (equal
    (q1008566-complex-polynomial-eval
     coefficients root zero add mul neg)
    (q1008566-complex-zero zero))))

(defun q1008566-convex-witness-p
    (root1 root2 root3 weight1 weight2 weight3
           coefficients z carrier zero one add mul neg lt)
  (and
   (q1008566-polynomial-root-p
    root1 coefficients carrier zero add mul neg)
   (q1008566-polynomial-root-p
    root2 coefficients carrier zero add mul neg)
   (q1008566-polynomial-root-p
    root3 coefficients carrier zero add mul neg)
   (apply$ carrier (list weight1))
   (apply$ carrier (list weight2))
   (apply$ carrier (list weight3))
   (not (q1008566-lt lt weight1 zero))
   (not (q1008566-lt lt weight2 zero))
   (not (q1008566-lt lt weight3 zero))
   (equal
    (q1008566-add
     add weight1
     (q1008566-add add weight2 weight3))
    one)
   (equal
    z
    (q1008566-complex-add
     (q1008566-complex-scale weight1 root1 mul)
     (q1008566-complex-add
      (q1008566-complex-scale weight2 root2 mul)
      (q1008566-complex-scale weight3 root3 mul)
      add)
     add))))

(defun-sk q1008566-convex-hull-membership-p
    (coefficients z carrier zero one add mul neg lt)
  (exists (root1 root2 root3 weight1 weight2 weight3)
    (q1008566-convex-witness-p
     root1 root2 root3 weight1 weight2 weight3
     coefficients z carrier zero one add mul neg lt)))

(defun thousand-theorems-q1008566-gauss-lucas-statement
    (carrier zero one add mul neg inv lt square-root odd-root
             coefficients z)
  (implies
   (and
    (q1008566-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root)
    (q1008566-positive-degree-polynomial-p
     coefficients carrier zero)
    (q1008566-complex-p z carrier)
    (equal
     (q1008566-complex-polynomial-eval
      (q1008566-complex-polynomial-derivative
       coefficients zero one add mul)
      z zero add mul neg)
     (q1008566-complex-zero zero)))
   (and
    (q1008566-center-mass-statement-p
     coefficients z carrier
     zero one add mul neg inv)
    (q1008566-convex-hull-membership-p
     coefficients z carrier
     zero one add mul neg lt))))

(value-triple :itpeval-statement-checked)
:q
