;; Statement-only formalization of miniF2F corpus artifact amc12a_2003_p24:
;; zero is the greatest real value of the stated sum of two base logarithms
;; when 1 < b <= a. This file contains no proof.
;;
;; The conservative operation symbols below present a real-closed ordered
;; field and its logarithm. Every field, order, real-closedness, and logarithm
;; law used to identify the real domain is explicit in the statement
;; predicate. The logarithm is characterized on positive values as a strictly
;; increasing homomorphism from multiplication to addition. On the real
;; numbers this differs from the natural logarithm at most by a positive
;; constant factor, which cancels in every base-logarithm quotient below.
;; Thus a and b remain arbitrary real values, and neither the logarithms nor
;; the universal real quantifiers are replaced by rational coordinates.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub amc12a-2003-p24-real-p (x) t)
(defstub amc12a-2003-p24-add-op (x y) t)
(defstub amc12a-2003-p24-multiply-op (x y) t)
(defstub amc12a-2003-p24-negate-op (x) t)
(defstub amc12a-2003-p24-inverse-op (x) t)
(defstub amc12a-2003-p24-less-op (x y) t)
(defstub amc12a-2003-p24-log-op (x) t)

(defun amc12a-2003-p24-member-p (x)
  (if (amc12a-2003-p24-real-p x) t nil))

(defun amc12a-2003-p24-add (x y)
  (amc12a-2003-p24-add-op x y))

(defun amc12a-2003-p24-mul (x y)
  (amc12a-2003-p24-multiply-op x y))

(defun amc12a-2003-p24-neg (x)
  (amc12a-2003-p24-negate-op x))

(defun amc12a-2003-p24-inv (x)
  (amc12a-2003-p24-inverse-op x))

(defun amc12a-2003-p24-less (x y)
  (if (amc12a-2003-p24-less-op x y) t nil))

(defun amc12a-2003-p24-log (x)
  (amc12a-2003-p24-log-op x))

(defun amc12a-2003-p24-sub (x y)
  (amc12a-2003-p24-add
   x
   (amc12a-2003-p24-neg y)))

(defun amc12a-2003-p24-div (x y)
  (amc12a-2003-p24-mul
   x
   (amc12a-2003-p24-inv y)))

(defun amc12a-2003-p24-positive-p (x zero)
  (and
   (amc12a-2003-p24-member-p x)
   (amc12a-2003-p24-less zero x)))

(defun amc12a-2003-p24-nonnegative-p (x zero)
  (and
   (amc12a-2003-p24-member-p x)
   (not (amc12a-2003-p24-less x zero))))

(defun-sk amc12a-2003-p24-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (amc12a-2003-p24-member-p x)
      (amc12a-2003-p24-member-p y)
      (amc12a-2003-p24-member-p z))
     (and
      (amc12a-2003-p24-member-p
       (amc12a-2003-p24-add x y))
      (amc12a-2003-p24-member-p
       (amc12a-2003-p24-mul x y))
      (amc12a-2003-p24-member-p
       (amc12a-2003-p24-neg x))
      (amc12a-2003-p24-member-p
       (amc12a-2003-p24-inv x))
      (equal
       (amc12a-2003-p24-add
        (amc12a-2003-p24-add x y)
        z)
       (amc12a-2003-p24-add
        x
        (amc12a-2003-p24-add y z)))
      (equal
       (amc12a-2003-p24-add x y)
       (amc12a-2003-p24-add y x))
      (equal
       (amc12a-2003-p24-add x zero)
       x)
      (equal
       (amc12a-2003-p24-add
        x
        (amc12a-2003-p24-neg x))
       zero)
      (equal
       (amc12a-2003-p24-mul
        (amc12a-2003-p24-mul x y)
        z)
       (amc12a-2003-p24-mul
        x
        (amc12a-2003-p24-mul y z)))
      (equal
       (amc12a-2003-p24-mul x y)
       (amc12a-2003-p24-mul y x))
      (equal
       (amc12a-2003-p24-mul x one)
       x)
      (implies
       (equal x zero)
       (equal
        (amc12a-2003-p24-inv x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (amc12a-2003-p24-mul
         x
         (amc12a-2003-p24-inv x))
        one))
      (equal
       (amc12a-2003-p24-mul
        x
        (amc12a-2003-p24-add y z))
       (amc12a-2003-p24-add
        (amc12a-2003-p24-mul x y)
        (amc12a-2003-p24-mul x z)))))))

(defun-sk amc12a-2003-p24-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (amc12a-2003-p24-member-p x)
      (amc12a-2003-p24-member-p y)
      (amc12a-2003-p24-member-p z))
     (and
      (not (amc12a-2003-p24-less x x))
      (or
       (equal x y)
       (amc12a-2003-p24-less x y)
       (amc12a-2003-p24-less y x))
      (implies
       (and
        (amc12a-2003-p24-less x y)
        (amc12a-2003-p24-less y z))
       (amc12a-2003-p24-less x z))
      (implies
       (amc12a-2003-p24-less x y)
       (amc12a-2003-p24-less
        (amc12a-2003-p24-add x z)
        (amc12a-2003-p24-add y z)))
      (implies
       (and
        (amc12a-2003-p24-less zero x)
        (amc12a-2003-p24-less zero y))
       (amc12a-2003-p24-less
        zero
        (amc12a-2003-p24-mul x y)))))))

(defun amc12a-2003-p24-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc12a-2003-p24-member-p (car coefficients))
     (amc12a-2003-p24-polynomial-p (cdr coefficients)))))

(defun amc12a-2003-p24-polynomial-value
    (coefficients x zero)
  (if (endp coefficients)
      zero
    (amc12a-2003-p24-add
     (car coefficients)
     (amc12a-2003-p24-mul
      x
      (amc12a-2003-p24-polynomial-value
       (cdr coefficients)
       x
       zero)))))

(defun amc12a-2003-p24-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc12a-2003-p24-leading-coefficient
     (cdr coefficients))))

(defun amc12a-2003-p24-odd-degree-p
    (coefficients zero)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc12a-2003-p24-leading-coefficient coefficients)
     zero))
   (equal
    (mod (1- (len coefficients)) 2)
    1)))

(defun-sk amc12a-2003-p24-square-root-exists-p
    (x zero)
  (exists (root)
    (and
     (amc12a-2003-p24-nonnegative-p root zero)
     (equal
      (amc12a-2003-p24-mul root root)
      x))))

(defun-sk amc12a-2003-p24-positive-square-roots-p
    (zero)
  (forall (x)
    (implies
     (amc12a-2003-p24-positive-p x zero)
     (amc12a-2003-p24-square-root-exists-p
      x
      zero))))

(defun-sk amc12a-2003-p24-polynomial-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (amc12a-2003-p24-member-p root)
     (equal
      (amc12a-2003-p24-polynomial-value
       coefficients
       root
       zero)
      zero))))

(defun-sk amc12a-2003-p24-odd-polynomial-roots-p
    (zero)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc12a-2003-p24-polynomial-p coefficients)
      (amc12a-2003-p24-odd-degree-p coefficients zero))
     (amc12a-2003-p24-polynomial-root-exists-p
      coefficients
      zero))))

(defun amc12a-2003-p24-real-closed-field-p
    (zero one)
  (and
   (amc12a-2003-p24-member-p zero)
   (amc12a-2003-p24-member-p one)
   (not (equal zero one))
   (amc12a-2003-p24-less zero one)
   (amc12a-2003-p24-field-laws-p zero one)
   (amc12a-2003-p24-order-laws-p zero)
   (amc12a-2003-p24-positive-square-roots-p zero)
   (amc12a-2003-p24-odd-polynomial-roots-p zero)))

(defun-sk amc12a-2003-p24-positive-logarithm-laws-p
    (zero)
  (forall (x y)
    (implies
     (and
      (amc12a-2003-p24-positive-p x zero)
      (amc12a-2003-p24-positive-p y zero))
     (and
      (amc12a-2003-p24-member-p
       (amc12a-2003-p24-log x))
      (amc12a-2003-p24-member-p
       (amc12a-2003-p24-log y))
      (equal
       (amc12a-2003-p24-log
        (amc12a-2003-p24-mul x y))
       (amc12a-2003-p24-add
        (amc12a-2003-p24-log x)
        (amc12a-2003-p24-log y)))
      (iff
       (amc12a-2003-p24-less x y)
       (amc12a-2003-p24-less
        (amc12a-2003-p24-log x)
        (amc12a-2003-p24-log y)))))))

(defun amc12a-2003-p24-real-log-context-p
    (zero one)
  (and
   (amc12a-2003-p24-real-closed-field-p zero one)
   (equal
    (amc12a-2003-p24-log one)
    zero)
   (amc12a-2003-p24-positive-logarithm-laws-p zero)))

(defun amc12a-2003-p24-logb (base argument)
  (amc12a-2003-p24-div
   (amc12a-2003-p24-log argument)
   (amc12a-2003-p24-log base)))

(defun amc12a-2003-p24-expression (a b)
  (amc12a-2003-p24-add
   (amc12a-2003-p24-logb
    a
    (amc12a-2003-p24-div a b))
   (amc12a-2003-p24-logb
    b
    (amc12a-2003-p24-div b a))))

(defun amc12a-2003-p24-source-domain-p
    (a b one)
  (and
   (amc12a-2003-p24-member-p a)
   (amc12a-2003-p24-member-p b)
   (amc12a-2003-p24-less one b)
   (not (amc12a-2003-p24-less a b))))

(defun-sk amc12a-2003-p24-zero-attained-p
    (zero one)
  (exists (a b)
    (and
     (amc12a-2003-p24-source-domain-p a b one)
     (equal
      (amc12a-2003-p24-expression a b)
      zero))))

(defun-sk amc12a-2003-p24-zero-upper-bound-p
    (zero one)
  (forall (a b)
    (implies
     (amc12a-2003-p24-source-domain-p a b one)
     (not
      (amc12a-2003-p24-less
       zero
       (amc12a-2003-p24-expression a b))))))

(defun amc12a-2003-p24-statement (zero one)
  (implies
   (amc12a-2003-p24-real-log-context-p zero one)
   (and
    (amc12a-2003-p24-zero-attained-p zero one)
    (amc12a-2003-p24-zero-upper-bound-p zero one))))

(value-triple :itpeval-statement-checked)
:q
