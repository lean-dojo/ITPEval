;; Statement-only formalization of miniF2F corpus artifact aime_1984_p15:
;; four equations in the squares of arbitrary real numbers x, y, z, and w
;; imply that their sum of squares is 36. This file contains no proof.
;;
;; The conservative operation symbols below present an arbitrary real-closed
;; ordered field, with all field, order, and real-closedness laws explicit in
;; the statement predicate. Real-closed ordered fields have the same
;; first-order ordered-field theory as the real numbers, so the unbounded
;; quantifiers below are bidirectionally equivalent to quantification over
;; arbitrary reals, without a rational, finite, or table-based surrogate.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub aime-1984-p15-real-p (x) t)
(defstub aime-1984-p15-add-op (x y) t)
(defstub aime-1984-p15-multiply-op (x y) t)
(defstub aime-1984-p15-negate-op (x) t)
(defstub aime-1984-p15-inverse-op (x) t)
(defstub aime-1984-p15-less-op (x y) t)

(defun aime-1984-p15-member-p (x)
  (if (aime-1984-p15-real-p x) t nil))

(defun aime-1984-p15-add (x y)
  (aime-1984-p15-add-op x y))

(defun aime-1984-p15-mul (x y)
  (aime-1984-p15-multiply-op x y))

(defun aime-1984-p15-neg (x)
  (aime-1984-p15-negate-op x))

(defun aime-1984-p15-inv (x)
  (aime-1984-p15-inverse-op x))

(defun aime-1984-p15-less (x y)
  (if (aime-1984-p15-less-op x y) t nil))

(defun aime-1984-p15-sub (x y)
  (aime-1984-p15-add
   x
   (aime-1984-p15-neg y)))

(defun aime-1984-p15-div (x y)
  (aime-1984-p15-mul
   x
   (aime-1984-p15-inv y)))

(defun aime-1984-p15-square (x)
  (aime-1984-p15-mul x x))

(defun aime-1984-p15-positive-p (x zero)
  (and
   (aime-1984-p15-member-p x)
   (aime-1984-p15-less zero x)))

(defun-sk aime-1984-p15-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (aime-1984-p15-member-p x)
      (aime-1984-p15-member-p y)
      (aime-1984-p15-member-p z))
     (and
      (aime-1984-p15-member-p
       (aime-1984-p15-add x y))
      (aime-1984-p15-member-p
       (aime-1984-p15-mul x y))
      (aime-1984-p15-member-p
       (aime-1984-p15-neg x))
      (implies
       (not (equal x zero))
       (aime-1984-p15-member-p
        (aime-1984-p15-inv x)))
      (equal
       (aime-1984-p15-add
        (aime-1984-p15-add x y)
        z)
       (aime-1984-p15-add
        x
        (aime-1984-p15-add y z)))
      (equal
       (aime-1984-p15-add x y)
       (aime-1984-p15-add y x))
      (equal
       (aime-1984-p15-add x zero)
       x)
      (equal
       (aime-1984-p15-add
        x
        (aime-1984-p15-neg x))
       zero)
      (equal
       (aime-1984-p15-mul
        (aime-1984-p15-mul x y)
        z)
       (aime-1984-p15-mul
        x
        (aime-1984-p15-mul y z)))
      (equal
       (aime-1984-p15-mul x y)
       (aime-1984-p15-mul y x))
      (equal
       (aime-1984-p15-mul x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (aime-1984-p15-mul
         x
         (aime-1984-p15-inv x))
        one))
      (equal
       (aime-1984-p15-mul
        x
        (aime-1984-p15-add y z))
       (aime-1984-p15-add
        (aime-1984-p15-mul x y)
        (aime-1984-p15-mul x z)))))))

(defun-sk aime-1984-p15-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (aime-1984-p15-member-p x)
      (aime-1984-p15-member-p y)
      (aime-1984-p15-member-p z))
     (and
      (not (aime-1984-p15-less x x))
      (or
       (equal x y)
       (aime-1984-p15-less x y)
       (aime-1984-p15-less y x))
      (implies
       (and
        (aime-1984-p15-less x y)
        (aime-1984-p15-less y z))
       (aime-1984-p15-less x z))
      (implies
       (aime-1984-p15-less x y)
       (aime-1984-p15-less
        (aime-1984-p15-add x z)
        (aime-1984-p15-add y z)))
      (implies
       (and
        (aime-1984-p15-less zero x)
        (aime-1984-p15-less zero y))
       (aime-1984-p15-less
        zero
        (aime-1984-p15-mul x y)))))))

(defun aime-1984-p15-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime-1984-p15-member-p (car coefficients))
     (aime-1984-p15-polynomial-p (cdr coefficients)))))

(defun aime-1984-p15-polynomial-value
    (coefficients x zero)
  (if (endp coefficients)
      zero
    (aime-1984-p15-add
     (car coefficients)
     (aime-1984-p15-mul
      x
      (aime-1984-p15-polynomial-value
       (cdr coefficients)
       x
       zero)))))

(defun aime-1984-p15-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime-1984-p15-leading-coefficient
     (cdr coefficients))))

(defun aime-1984-p15-odd-degree-p (coefficients zero)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime-1984-p15-leading-coefficient coefficients)
     zero))
   (equal
    (mod (1- (len coefficients)) 2)
    1)))

(defun-sk aime-1984-p15-square-root-exists-p (x zero)
  (exists (root)
    (and
     (or
      (equal root zero)
      (aime-1984-p15-positive-p root zero))
     (equal
      (aime-1984-p15-square root)
      x))))

(defun-sk aime-1984-p15-positive-square-roots-p (zero)
  (forall (x)
    (implies
     (aime-1984-p15-positive-p x zero)
     (aime-1984-p15-square-root-exists-p
      x
      zero))))

(defun-sk aime-1984-p15-polynomial-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (aime-1984-p15-member-p root)
     (equal
      (aime-1984-p15-polynomial-value
       coefficients
       root
       zero)
      zero))))

(defun-sk aime-1984-p15-odd-polynomial-roots-p (zero)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime-1984-p15-polynomial-p coefficients)
      (aime-1984-p15-odd-degree-p coefficients zero))
     (aime-1984-p15-polynomial-root-exists-p
      coefficients
      zero))))

(defun aime-1984-p15-real-closed-field-p (zero one)
  (and
   (aime-1984-p15-member-p zero)
   (aime-1984-p15-member-p one)
   (not (equal zero one))
   (aime-1984-p15-less zero one)
   (aime-1984-p15-field-laws-p zero one)
   (aime-1984-p15-order-laws-p zero)
   (aime-1984-p15-positive-square-roots-p zero)
   (aime-1984-p15-odd-polynomial-roots-p zero)))

(defun aime-1984-p15-natural (zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (aime-1984-p15-add
     one
     (aime-1984-p15-natural
      zero
      one
      (- n 1)))))

(defun aime-1984-p15-denominator
    (zero one n k)
  (aime-1984-p15-sub
   (aime-1984-p15-square
    (aime-1984-p15-natural zero one n))
   (aime-1984-p15-square
    (aime-1984-p15-natural zero one k))))

(defun aime-1984-p15-term
    (zero one n k x)
  (aime-1984-p15-div
   (aime-1984-p15-square x)
   (aime-1984-p15-denominator
    zero
    one
    n
    k)))

(defun aime-1984-p15-equation-p
    (zero one n x y z w)
  (equal
   (aime-1984-p15-add
    (aime-1984-p15-add
     (aime-1984-p15-term zero one n 1 x)
     (aime-1984-p15-term zero one n 3 y))
    (aime-1984-p15-add
     (aime-1984-p15-term zero one n 5 z)
     (aime-1984-p15-term zero one n 7 w)))
   one))

(defun aime-1984-p15-sum-of-squares (x y z w)
  (aime-1984-p15-add
   (aime-1984-p15-add
    (aime-1984-p15-square x)
    (aime-1984-p15-square y))
   (aime-1984-p15-add
    (aime-1984-p15-square z)
    (aime-1984-p15-square w))))

(defun-sk aime-1984-p15-statement (zero one)
  (forall (x y z w)
    (implies
     (and
      (aime-1984-p15-real-closed-field-p zero one)
      (aime-1984-p15-member-p x)
      (aime-1984-p15-member-p y)
      (aime-1984-p15-member-p z)
      (aime-1984-p15-member-p w)
      (aime-1984-p15-equation-p
       zero one 2 x y z w)
      (aime-1984-p15-equation-p
       zero one 4 x y z w)
      (aime-1984-p15-equation-p
       zero one 6 x y z w)
      (aime-1984-p15-equation-p
       zero one 8 x y z w))
     (equal
      (aime-1984-p15-sum-of-squares x y z w)
      (aime-1984-p15-natural zero one 36)))))

(value-triple :itpeval-statement-checked)
:q
