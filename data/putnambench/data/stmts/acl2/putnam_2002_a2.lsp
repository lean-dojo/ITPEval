;; Statement-only formalization of PutnamBench corpus artifact putnam_2002_a2:
;; every five-point subset of the unit sphere in real three-space has four
;; points in some closed hemisphere. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 does not contain the analytic real numbers as a primitive
;; domain. Unconstrained function symbols present an arbitrary real closed
;; ordered field, and the explicit predicates below state its laws with
;; DEFUN-SK quantifiers. The source theorem is a first-order ordered-field
;; sentence, so completeness of real closed fields transfers it exactly
;; between this presentation and the ordinary real numbers.

(defstub putnam-2002-a2-real-p (x) t)
(defstub putnam-2002-a2-add-op (x y) t)
(defstub putnam-2002-a2-mul-op (x y) t)
(defstub putnam-2002-a2-neg-op (x) t)
(defstub putnam-2002-a2-inv-op (x) t)
(defstub putnam-2002-a2-less-op (x y) t)

(defun putnam-2002-a2-member-p (x)
  (if (putnam-2002-a2-real-p x) t nil))

(defun putnam-2002-a2-add (x y)
  (putnam-2002-a2-add-op x y))

(defun putnam-2002-a2-mul (x y)
  (putnam-2002-a2-mul-op x y))

(defun putnam-2002-a2-neg (x)
  (putnam-2002-a2-neg-op x))

(defun putnam-2002-a2-inv (x)
  (putnam-2002-a2-inv-op x))

(defun putnam-2002-a2-less (x y)
  (if (putnam-2002-a2-less-op x y) t nil))

(defun-sk putnam-2002-a2-field-laws-p (zero one)
  (forall
   (x y z)
   (implies
    (and
     (putnam-2002-a2-member-p x)
     (putnam-2002-a2-member-p y)
     (putnam-2002-a2-member-p z))
    (and
     (putnam-2002-a2-member-p
      (putnam-2002-a2-add x y))
     (putnam-2002-a2-member-p
      (putnam-2002-a2-mul x y))
     (putnam-2002-a2-member-p
      (putnam-2002-a2-neg x))
     (putnam-2002-a2-member-p
      (putnam-2002-a2-inv x))
     (equal
      (putnam-2002-a2-add
       (putnam-2002-a2-add x y) z)
      (putnam-2002-a2-add
       x (putnam-2002-a2-add y z)))
     (equal
      (putnam-2002-a2-add x y)
      (putnam-2002-a2-add y x))
     (equal (putnam-2002-a2-add x zero) x)
     (equal
      (putnam-2002-a2-add x (putnam-2002-a2-neg x))
      zero)
     (equal
      (putnam-2002-a2-mul
       (putnam-2002-a2-mul x y) z)
      (putnam-2002-a2-mul
       x (putnam-2002-a2-mul y z)))
     (equal
      (putnam-2002-a2-mul x y)
      (putnam-2002-a2-mul y x))
     (equal (putnam-2002-a2-mul x one) x)
     (implies
      (not (equal x zero))
      (equal
       (putnam-2002-a2-mul x (putnam-2002-a2-inv x))
       one))
     (equal
      (putnam-2002-a2-mul
       x (putnam-2002-a2-add y z))
      (putnam-2002-a2-add
       (putnam-2002-a2-mul x y)
       (putnam-2002-a2-mul x z)))))))

(defun-sk putnam-2002-a2-order-laws-p (zero)
  (forall
   (x y z)
   (implies
    (and
     (putnam-2002-a2-member-p x)
     (putnam-2002-a2-member-p y)
     (putnam-2002-a2-member-p z))
    (and
     (not (putnam-2002-a2-less x x))
     (or
      (equal x y)
      (putnam-2002-a2-less x y)
      (putnam-2002-a2-less y x))
     (implies
      (and
       (putnam-2002-a2-less x y)
       (putnam-2002-a2-less y z))
      (putnam-2002-a2-less x z))
     (implies
      (putnam-2002-a2-less x y)
      (putnam-2002-a2-less
       (putnam-2002-a2-add x z)
       (putnam-2002-a2-add y z)))
     (implies
      (and
       (putnam-2002-a2-less zero x)
       (putnam-2002-a2-less zero y))
      (putnam-2002-a2-less
       zero
       (putnam-2002-a2-mul x y)))))))

(defun putnam-2002-a2-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (putnam-2002-a2-member-p (car coefficients))
       (putnam-2002-a2-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2002-a2-polynomial-evaluate
    (coefficients x zero)
  (if (consp coefficients)
      (putnam-2002-a2-add
       (car coefficients)
       (putnam-2002-a2-mul
        x
        (putnam-2002-a2-polynomial-evaluate
         (cdr coefficients) x zero)))
    zero))

(defun putnam-2002-a2-odd-degree-polynomial-p
    (coefficients zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-2002-a2-coefficient-list-p coefficients)
   (not (equal (car (last coefficients)) zero))
   (evenp (len coefficients))))

(defun-sk putnam-2002-a2-square-root-exists-p (x)
  (exists
   (root)
   (and
    (putnam-2002-a2-member-p root)
    (equal (putnam-2002-a2-mul root root) x))))

(defun-sk putnam-2002-a2-nonnegative-square-roots-p (zero)
  (forall
   (x)
   (implies
    (and
     (putnam-2002-a2-member-p x)
     (not (putnam-2002-a2-less x zero)))
    (putnam-2002-a2-square-root-exists-p x))))

(defun-sk putnam-2002-a2-polynomial-root-exists-p
    (coefficients zero)
  (exists
   (root)
   (and
    (putnam-2002-a2-member-p root)
    (equal
     (putnam-2002-a2-polynomial-evaluate
      coefficients root zero)
     zero))))

(defun-sk putnam-2002-a2-odd-polynomial-roots-p (zero)
  (forall
   (coefficients)
   (implies
    (putnam-2002-a2-odd-degree-polynomial-p
     coefficients zero)
    (putnam-2002-a2-polynomial-root-exists-p
     coefficients zero))))

(defun putnam-2002-a2-real-closed-field-p (zero one)
  (and
   (putnam-2002-a2-member-p zero)
   (putnam-2002-a2-member-p one)
   (not (equal zero one))
   (putnam-2002-a2-less zero one)
   (putnam-2002-a2-field-laws-p zero one)
   (putnam-2002-a2-order-laws-p zero)
   (putnam-2002-a2-nonnegative-square-roots-p zero)
   (putnam-2002-a2-odd-polynomial-roots-p zero)))

;; A duplicate-free list of length five is an ordered enumeration of the
;; source's five-element set. Each point is a three-element coordinate list.

(defun putnam-2002-a2-point-p (point)
  (and
   (true-listp point)
   (equal (len point) 3)
   (putnam-2002-a2-member-p (nth 0 point))
   (putnam-2002-a2-member-p (nth 1 point))
   (putnam-2002-a2-member-p (nth 2 point))))

(defun putnam-2002-a2-point-list-p (points)
  (if (consp points)
      (and
       (putnam-2002-a2-point-p (car points))
       (putnam-2002-a2-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-2002-a2-square (value)
  (putnam-2002-a2-mul value value))

(defun putnam-2002-a2-unit-point-p (point one)
  (equal
   (putnam-2002-a2-add
    (putnam-2002-a2-square (nth 0 point))
    (putnam-2002-a2-add
     (putnam-2002-a2-square (nth 1 point))
     (putnam-2002-a2-square (nth 2 point))))
   one))

(defun putnam-2002-a2-unit-point-list-p (points one)
  (if (consp points)
      (and
       (putnam-2002-a2-unit-point-p (car points) one)
       (putnam-2002-a2-unit-point-list-p
        (cdr points) one))
    (equal points nil)))

(defun putnam-2002-a2-dot (point vx vy vz)
  (putnam-2002-a2-add
   (putnam-2002-a2-mul (nth 0 point) vx)
   (putnam-2002-a2-add
    (putnam-2002-a2-mul (nth 1 point) vy)
    (putnam-2002-a2-mul (nth 2 point) vz))))

(defun putnam-2002-a2-nonnegative-count
    (points vx vy vz zero)
  (if (consp points)
      (+
       (if
        (putnam-2002-a2-less
         (putnam-2002-a2-dot
          (car points) vx vy vz)
         zero)
        0
        1)
       (putnam-2002-a2-nonnegative-count
        (cdr points) vx vy vz zero))
    0))

;; This is the source's internal existential V. Its nonzero condition and the
;; closed-hemisphere inequality are stated directly, with no witness search
;; and no negated functional equality.

(defun-sk putnam-2002-a2-witness-exists-p
    (points zero)
  (exists
   (vx vy vz)
   (and
    (putnam-2002-a2-member-p vx)
    (putnam-2002-a2-member-p vy)
    (putnam-2002-a2-member-p vz)
    (or
     (not (equal vx zero))
     (not (equal vy zero))
     (not (equal vz zero)))
    (<=
     4
     (putnam-2002-a2-nonnegative-count
      points vx vy vz zero)))))

(defun putnambench-putnam-2002-a2-statement
    (points zero one)
  (implies
   (and
    (putnam-2002-a2-real-closed-field-p zero one)
    (true-listp points)
    (equal (len points) 5)
    (no-duplicatesp-equal points)
    (putnam-2002-a2-point-list-p points)
    (putnam-2002-a2-unit-point-list-p points one))
   (putnam-2002-a2-witness-exists-p points zero)))

(value-triple :itpeval-statement-checked)
:q
