;; Statement-only formalization of miniF2F corpus artifact amc12a_2002_p13:
;; distinct positive real numbers a and b satisfying |a - 1/a| = 1 and
;; |b - 1/b| = 1 have sum sqrt(5). This file contains no proof.
;;
;; The conservative operation symbols below present an arbitrary real-closed
;; ordered field, with every field, order, and real-closedness law explicit in
;; the statement predicate. Real-closed fields have the same first-order
;; ordered-field theory as the reals, and sqrt(5) is the uniquely characterized
;; nonnegative square root selected by DEFCHOOSE. Thus no rational or algebraic
;; subfield restriction is imposed on a or b.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub amc12a-2002-p13-real-p (x) t)
(defstub amc12a-2002-p13-add-op (x y) t)
(defstub amc12a-2002-p13-multiply-op (x y) t)
(defstub amc12a-2002-p13-negate-op (x) t)
(defstub amc12a-2002-p13-inverse-op (x) t)
(defstub amc12a-2002-p13-less-op (x y) t)

(defun amc12a-2002-p13-member-p (x)
  (if (amc12a-2002-p13-real-p x) t nil))

(defun amc12a-2002-p13-add (x y)
  (amc12a-2002-p13-add-op x y))

(defun amc12a-2002-p13-mul (x y)
  (amc12a-2002-p13-multiply-op x y))

(defun amc12a-2002-p13-neg (x)
  (amc12a-2002-p13-negate-op x))

(defun amc12a-2002-p13-inv (x)
  (amc12a-2002-p13-inverse-op x))

(defun amc12a-2002-p13-less (x y)
  (if (amc12a-2002-p13-less-op x y) t nil))

(defun amc12a-2002-p13-sub (x y)
  (amc12a-2002-p13-add
   x
   (amc12a-2002-p13-neg y)))

(defun amc12a-2002-p13-div (x y)
  (amc12a-2002-p13-mul
   x
   (amc12a-2002-p13-inv y)))

(defun amc12a-2002-p13-nonnegative-p (x zero)
  (and
   (amc12a-2002-p13-member-p x)
   (or (equal x zero)
       (amc12a-2002-p13-less zero x))))

(defun amc12a-2002-p13-positive-p (x zero)
  (and
   (amc12a-2002-p13-member-p x)
   (amc12a-2002-p13-less zero x)))

(defun amc12a-2002-p13-abs (x zero)
  (if (amc12a-2002-p13-less x zero)
      (amc12a-2002-p13-neg x)
    x))

(defun amc12a-2002-p13-five (one)
  (amc12a-2002-p13-add
   one
   (amc12a-2002-p13-add
    one
    (amc12a-2002-p13-add
     one
     (amc12a-2002-p13-add one one)))))

(defun-sk amc12a-2002-p13-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (amc12a-2002-p13-member-p x)
      (amc12a-2002-p13-member-p y)
      (amc12a-2002-p13-member-p z))
     (and
      (amc12a-2002-p13-member-p
       (amc12a-2002-p13-add x y))
      (amc12a-2002-p13-member-p
       (amc12a-2002-p13-mul x y))
      (amc12a-2002-p13-member-p
       (amc12a-2002-p13-neg x))
      (implies
       (not (equal x zero))
       (amc12a-2002-p13-member-p
        (amc12a-2002-p13-inv x)))
      (equal
       (amc12a-2002-p13-add
        (amc12a-2002-p13-add x y) z)
       (amc12a-2002-p13-add
        x (amc12a-2002-p13-add y z)))
      (equal
       (amc12a-2002-p13-add x y)
       (amc12a-2002-p13-add y x))
      (equal (amc12a-2002-p13-add x zero) x)
      (equal
       (amc12a-2002-p13-add
        x (amc12a-2002-p13-neg x))
       zero)
      (equal
       (amc12a-2002-p13-mul
        (amc12a-2002-p13-mul x y) z)
       (amc12a-2002-p13-mul
        x (amc12a-2002-p13-mul y z)))
      (equal
       (amc12a-2002-p13-mul x y)
       (amc12a-2002-p13-mul y x))
      (equal (amc12a-2002-p13-mul x one) x)
      (implies
       (not (equal x zero))
       (equal
        (amc12a-2002-p13-mul
         x (amc12a-2002-p13-inv x))
        one))
      (equal
       (amc12a-2002-p13-mul
        x (amc12a-2002-p13-add y z))
       (amc12a-2002-p13-add
        (amc12a-2002-p13-mul x y)
        (amc12a-2002-p13-mul x z)))))))

(defun-sk amc12a-2002-p13-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (amc12a-2002-p13-member-p x)
      (amc12a-2002-p13-member-p y)
      (amc12a-2002-p13-member-p z))
     (and
      (not (amc12a-2002-p13-less x x))
      (or (equal x y)
          (amc12a-2002-p13-less x y)
          (amc12a-2002-p13-less y x))
      (implies
       (and (amc12a-2002-p13-less x y)
            (amc12a-2002-p13-less y z))
       (amc12a-2002-p13-less x z))
      (implies
       (amc12a-2002-p13-less x y)
       (amc12a-2002-p13-less
        (amc12a-2002-p13-add x z)
        (amc12a-2002-p13-add y z)))
      (implies
       (and (amc12a-2002-p13-less zero x)
            (amc12a-2002-p13-less zero y))
       (amc12a-2002-p13-less
        zero
        (amc12a-2002-p13-mul x y)))))))

(defun amc12a-2002-p13-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc12a-2002-p13-member-p (car coefficients))
     (amc12a-2002-p13-polynomial-p (cdr coefficients)))))

(defun amc12a-2002-p13-polynomial-value
    (coefficients x zero)
  (if (endp coefficients)
      zero
    (amc12a-2002-p13-add
     (car coefficients)
     (amc12a-2002-p13-mul
      x
      (amc12a-2002-p13-polynomial-value
       (cdr coefficients) x zero)))))

(defun amc12a-2002-p13-leading-coefficient
    (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc12a-2002-p13-leading-coefficient
     (cdr coefficients))))

(defun amc12a-2002-p13-odd-degree-p
    (coefficients zero)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc12a-2002-p13-leading-coefficient coefficients)
     zero))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc12a-2002-p13-square-root-exists-p
    (x zero)
  (exists (root)
    (and
     (amc12a-2002-p13-nonnegative-p root zero)
     (equal
      (amc12a-2002-p13-mul root root)
      x))))

(defun-sk amc12a-2002-p13-positive-square-roots-p
    (zero)
  (forall (x)
    (implies
     (amc12a-2002-p13-positive-p x zero)
     (amc12a-2002-p13-square-root-exists-p
      x zero))))

(defun-sk amc12a-2002-p13-polynomial-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (amc12a-2002-p13-member-p root)
     (equal
      (amc12a-2002-p13-polynomial-value
       coefficients root zero)
      zero))))

(defun-sk amc12a-2002-p13-odd-polynomial-roots-p
    (zero)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc12a-2002-p13-polynomial-p coefficients)
      (amc12a-2002-p13-odd-degree-p coefficients zero))
     (amc12a-2002-p13-polynomial-root-exists-p
      coefficients zero))))

(defun amc12a-2002-p13-real-closed-field-p
    (zero one)
  (and
   (amc12a-2002-p13-member-p zero)
   (amc12a-2002-p13-member-p one)
   (not (equal zero one))
   (amc12a-2002-p13-less zero one)
   (amc12a-2002-p13-field-laws-p zero one)
   (amc12a-2002-p13-order-laws-p zero)
   (amc12a-2002-p13-positive-square-roots-p zero)
   (amc12a-2002-p13-odd-polynomial-roots-p zero)))

(defun amc12a-2002-p13-principal-sqrt-five-p
    (root zero one)
  (and
   (amc12a-2002-p13-nonnegative-p root zero)
   (equal
    (amc12a-2002-p13-mul root root)
    (amc12a-2002-p13-five one))))

(defchoose amc12a-2002-p13-sqrt-five
    (root)
    (zero one)
  (amc12a-2002-p13-principal-sqrt-five-p
   root zero one))

(defun-sk amc12a-2002-p13-statement (zero one)
  (forall (a b)
    (implies
     (and
      (amc12a-2002-p13-real-closed-field-p zero one)
      (amc12a-2002-p13-positive-p a zero)
      (amc12a-2002-p13-positive-p b zero)
      (not (equal a b))
      (equal
       (amc12a-2002-p13-abs
        (amc12a-2002-p13-sub
         a
         (amc12a-2002-p13-div one a))
        zero)
       one)
      (equal
       (amc12a-2002-p13-abs
        (amc12a-2002-p13-sub
         b
         (amc12a-2002-p13-div one b))
        zero)
       one))
     (equal
      (amc12a-2002-p13-add a b)
      (amc12a-2002-p13-sqrt-five zero one)))))

(value-triple :itpeval-statement-checked)
:q
