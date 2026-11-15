;; Statement-only formalization of miniF2F corpus artifact amc12b_2003_p6:
;; a real geometric sequence whose terms at indices 1 and 3 are 2 and 6 has
;; initial term 2/sqrt(3) or -2/sqrt(3). This file contains no proof.
;;
;; The conservative operation symbols below present an arbitrary real-closed
;; ordered field, with every field, order, and real-closedness law explicit in
;; the statement predicate. Real-closed fields have exactly the first-order
;; ordered-field theory of the reals, and sqrt(3) is the uniquely characterized
;; nonnegative square root selected by DEFCHOOSE.
;;
;; The source condition u(k) = a*r^k is eliminated by a bidirectional logical
;; equivalence: it makes u(0)=a, u(1)=a*r, and u(3)=a*r^3; conversely, for
;; every a and r the function k |-> a*r^k is a real sequence satisfying that
;; condition. Thus the implication below preserves universal real a and r
;; without restricting them to a rational or algebraic subfield.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub amc12b-2003-p6-real-p (x) t)
(defstub amc12b-2003-p6-add-op (x y) t)
(defstub amc12b-2003-p6-multiply-op (x y) t)
(defstub amc12b-2003-p6-negate-op (x) t)
(defstub amc12b-2003-p6-inverse-op (x) t)
(defstub amc12b-2003-p6-less-op (x y) t)

(defun amc12b-2003-p6-member-p (x)
  (if (amc12b-2003-p6-real-p x) t nil))

(defun amc12b-2003-p6-add (x y)
  (amc12b-2003-p6-add-op x y))

(defun amc12b-2003-p6-mul (x y)
  (amc12b-2003-p6-multiply-op x y))

(defun amc12b-2003-p6-neg (x)
  (amc12b-2003-p6-negate-op x))

(defun amc12b-2003-p6-inv (x)
  (amc12b-2003-p6-inverse-op x))

(defun amc12b-2003-p6-less (x y)
  (if (amc12b-2003-p6-less-op x y) t nil))

(defun amc12b-2003-p6-div (x y)
  (amc12b-2003-p6-mul
   x
   (amc12b-2003-p6-inv y)))

(defun amc12b-2003-p6-nonnegative-p (x zero)
  (and
   (amc12b-2003-p6-member-p x)
   (or
    (equal x zero)
    (amc12b-2003-p6-less zero x))))

(defun amc12b-2003-p6-positive-p (x zero)
  (and
   (amc12b-2003-p6-member-p x)
   (amc12b-2003-p6-less zero x)))

(defun amc12b-2003-p6-natural-value (zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (amc12b-2003-p6-add
     one
     (amc12b-2003-p6-natural-value
      zero one (- n 1)))))

(defun amc12b-2003-p6-power (one base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (amc12b-2003-p6-mul
     base
     (amc12b-2003-p6-power
      one base (- exponent 1)))))

(defun-sk amc12b-2003-p6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (amc12b-2003-p6-member-p x)
      (amc12b-2003-p6-member-p y)
      (amc12b-2003-p6-member-p z))
     (and
      (amc12b-2003-p6-member-p
       (amc12b-2003-p6-add x y))
      (amc12b-2003-p6-member-p
       (amc12b-2003-p6-mul x y))
      (amc12b-2003-p6-member-p
       (amc12b-2003-p6-neg x))
      (implies
       (not (equal x zero))
       (amc12b-2003-p6-member-p
        (amc12b-2003-p6-inv x)))
      (equal
       (amc12b-2003-p6-add
        (amc12b-2003-p6-add x y)
        z)
       (amc12b-2003-p6-add
        x
        (amc12b-2003-p6-add y z)))
      (equal
       (amc12b-2003-p6-add x y)
       (amc12b-2003-p6-add y x))
      (equal
       (amc12b-2003-p6-add x zero)
       x)
      (equal
       (amc12b-2003-p6-add
        x
        (amc12b-2003-p6-neg x))
       zero)
      (equal
       (amc12b-2003-p6-mul
        (amc12b-2003-p6-mul x y)
        z)
       (amc12b-2003-p6-mul
        x
        (amc12b-2003-p6-mul y z)))
      (equal
       (amc12b-2003-p6-mul x y)
       (amc12b-2003-p6-mul y x))
      (equal
       (amc12b-2003-p6-mul x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (amc12b-2003-p6-mul
         x
         (amc12b-2003-p6-inv x))
        one))
      (equal
       (amc12b-2003-p6-mul
        x
        (amc12b-2003-p6-add y z))
       (amc12b-2003-p6-add
        (amc12b-2003-p6-mul x y)
        (amc12b-2003-p6-mul x z)))))))

(defun-sk amc12b-2003-p6-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (amc12b-2003-p6-member-p x)
      (amc12b-2003-p6-member-p y)
      (amc12b-2003-p6-member-p z))
     (and
      (not (amc12b-2003-p6-less x x))
      (or
       (equal x y)
       (amc12b-2003-p6-less x y)
       (amc12b-2003-p6-less y x))
      (implies
       (and
        (amc12b-2003-p6-less x y)
        (amc12b-2003-p6-less y z))
       (amc12b-2003-p6-less x z))
      (implies
       (amc12b-2003-p6-less x y)
       (amc12b-2003-p6-less
        (amc12b-2003-p6-add x z)
        (amc12b-2003-p6-add y z)))
      (implies
       (and
        (amc12b-2003-p6-less zero x)
        (amc12b-2003-p6-less zero y))
       (amc12b-2003-p6-less
        zero
        (amc12b-2003-p6-mul x y)))))))

(defun amc12b-2003-p6-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc12b-2003-p6-member-p (car coefficients))
     (amc12b-2003-p6-polynomial-p
      (cdr coefficients)))))

(defun amc12b-2003-p6-polynomial-value
    (coefficients x zero)
  (if (endp coefficients)
      zero
    (amc12b-2003-p6-add
     (car coefficients)
     (amc12b-2003-p6-mul
      x
      (amc12b-2003-p6-polynomial-value
       (cdr coefficients)
       x
       zero)))))

(defun amc12b-2003-p6-leading-coefficient
    (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc12b-2003-p6-leading-coefficient
     (cdr coefficients))))

(defun amc12b-2003-p6-odd-degree-p
    (coefficients zero)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc12b-2003-p6-leading-coefficient coefficients)
     zero))
   (equal
    (mod (1- (len coefficients)) 2)
    1)))

(defun-sk amc12b-2003-p6-square-root-exists-p
    (x zero)
  (exists (root)
    (and
     (amc12b-2003-p6-nonnegative-p root zero)
     (equal
      (amc12b-2003-p6-mul root root)
      x))))

(defun-sk amc12b-2003-p6-positive-square-roots-p
    (zero)
  (forall (x)
    (implies
     (amc12b-2003-p6-positive-p x zero)
     (amc12b-2003-p6-square-root-exists-p
      x
      zero))))

(defun-sk amc12b-2003-p6-polynomial-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (amc12b-2003-p6-member-p root)
     (equal
      (amc12b-2003-p6-polynomial-value
       coefficients
       root
       zero)
      zero))))

(defun-sk amc12b-2003-p6-odd-polynomial-roots-p
    (zero)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc12b-2003-p6-polynomial-p coefficients)
      (amc12b-2003-p6-odd-degree-p
       coefficients
       zero))
     (amc12b-2003-p6-polynomial-root-exists-p
      coefficients
      zero))))

(defun amc12b-2003-p6-real-closed-field-p
    (zero one)
  (and
   (amc12b-2003-p6-member-p zero)
   (amc12b-2003-p6-member-p one)
   (not (equal zero one))
   (amc12b-2003-p6-less zero one)
   (amc12b-2003-p6-field-laws-p zero one)
   (amc12b-2003-p6-order-laws-p zero)
   (amc12b-2003-p6-positive-square-roots-p zero)
   (amc12b-2003-p6-odd-polynomial-roots-p zero)))

(defun amc12b-2003-p6-principal-sqrt-three-p
    (root zero one)
  (and
   (amc12b-2003-p6-nonnegative-p root zero)
   (equal
    (amc12b-2003-p6-mul root root)
    (amc12b-2003-p6-natural-value
     zero one 3))))

(defchoose amc12b-2003-p6-sqrt-three
    (root)
    (zero one)
  (amc12b-2003-p6-principal-sqrt-three-p
   root
   zero
   one))

(defun-sk amc12b-2003-p6-statement (zero one)
  (forall (a r)
    (let* ((two
            (amc12b-2003-p6-natural-value
             zero one 2))
           (six
            (amc12b-2003-p6-natural-value
             zero one 6))
           (sqrt-three
            (amc12b-2003-p6-sqrt-three zero one))
           (two-over-sqrt-three
            (amc12b-2003-p6-div two sqrt-three)))
      (implies
       (and
        (amc12b-2003-p6-real-closed-field-p zero one)
        (amc12b-2003-p6-member-p a)
        (amc12b-2003-p6-member-p r)
        (equal
         (amc12b-2003-p6-mul a r)
         two)
        (equal
         (amc12b-2003-p6-mul
          a
          (amc12b-2003-p6-power one r 3))
         six))
       (or
        (equal a two-over-sqrt-three)
        (equal
         a
         (amc12b-2003-p6-neg
          two-over-sqrt-three)))))))

(value-triple :itpeval-statement-checked)
:q
