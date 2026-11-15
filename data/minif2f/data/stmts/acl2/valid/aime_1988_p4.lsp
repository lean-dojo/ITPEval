;; Statement-only formalization of miniF2F artifact aime_1988_p4:
        ;; a finite prefix of a real sequence with |a(k)|<1 and the stated sum-of-absolute-values equation must have length at least 20.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime88p4-real-p (value) t)
(defstub aime88p4-zero () t)
(defstub aime88p4-one () t)
(defstub aime88p4-add (left right) t)
(defstub aime88p4-mul (left right) t)
(defstub aime88p4-neg (value) t)
(defstub aime88p4-inv (value) t)
(defstub aime88p4-lt (left right) t)
(defstub aime88p4-of-rational (value) t)

(defun aime88p4-sub (left right)
  (aime88p4-add left (aime88p4-neg right)))

(defun aime88p4-div (left right)
  (aime88p4-mul left (aime88p4-inv right)))

(defun aime88p4-le (left right)
  (or (equal left right) (aime88p4-lt left right)))

(defun aime88p4-nonnegative-p (value)
  (and (aime88p4-real-p value)
       (aime88p4-le (aime88p4-zero) value)))

(defun aime88p4-positive-p (value)
  (and (aime88p4-real-p value)
       (aime88p4-lt (aime88p4-zero) value)))

(defun aime88p4-abs (value)
  (if (aime88p4-lt value (aime88p4-zero))
      (aime88p4-neg value)
    value))

(defun aime88p4-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime88p4-one)
    (aime88p4-mul
     value
     (aime88p4-pow value (1- exponent)))))

(defun-sk aime88p4-field-laws-p ()
  (forall (x y z)
    (and
     (aime88p4-real-p (aime88p4-zero))
     (aime88p4-real-p (aime88p4-one))
     (not (equal (aime88p4-zero) (aime88p4-one)))
     (implies
      (aime88p4-real-p x)
      (and
       (aime88p4-real-p (aime88p4-neg x))
       (aime88p4-real-p (aime88p4-inv x))
       (equal (aime88p4-add x (aime88p4-zero)) x)
       (equal (aime88p4-add x (aime88p4-neg x))
              (aime88p4-zero))
       (equal (aime88p4-mul x (aime88p4-one)) x)
       (implies
        (not (equal x (aime88p4-zero)))
        (equal (aime88p4-mul x (aime88p4-inv x))
               (aime88p4-one)))))
     (equal (aime88p4-inv (aime88p4-zero))
            (aime88p4-zero))
     (implies
      (and (aime88p4-real-p x)
           (aime88p4-real-p y))
      (and
       (aime88p4-real-p (aime88p4-add x y))
       (aime88p4-real-p (aime88p4-mul x y))
       (equal (aime88p4-add x y)
              (aime88p4-add y x))
       (equal (aime88p4-mul x y)
              (aime88p4-mul y x))))
     (implies
      (and (aime88p4-real-p x)
           (aime88p4-real-p y)
           (aime88p4-real-p z))
      (and
       (equal (aime88p4-add (aime88p4-add x y) z)
              (aime88p4-add x (aime88p4-add y z)))
       (equal (aime88p4-mul (aime88p4-mul x y) z)
              (aime88p4-mul x (aime88p4-mul y z)))
       (equal (aime88p4-mul x (aime88p4-add y z))
              (aime88p4-add
               (aime88p4-mul x y)
               (aime88p4-mul x z))))))))

(defun-sk aime88p4-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime88p4-real-p x)
          (aime88p4-real-p y)
          (aime88p4-real-p z))
     (and
      (not (aime88p4-lt x x))
      (or (equal x y)
          (aime88p4-lt x y)
          (aime88p4-lt y x))
      (implies
       (and (aime88p4-lt x y)
            (aime88p4-lt y z))
       (aime88p4-lt x z))
      (implies
       (aime88p4-lt x y)
       (aime88p4-lt
        (aime88p4-add x z)
        (aime88p4-add y z)))
      (implies
       (and (aime88p4-lt (aime88p4-zero) x)
            (aime88p4-lt (aime88p4-zero) y))
       (aime88p4-lt
        (aime88p4-zero)
        (aime88p4-mul x y)))))))

(defun-sk aime88p4-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime88p4-real-p (aime88p4-of-rational a))
      (equal (aime88p4-of-rational 0) (aime88p4-zero))
      (equal (aime88p4-of-rational 1) (aime88p4-one))
      (equal
       (aime88p4-of-rational (+ a b))
       (aime88p4-add
        (aime88p4-of-rational a)
        (aime88p4-of-rational b)))
      (equal
       (aime88p4-of-rational (* a b))
       (aime88p4-mul
        (aime88p4-of-rational a)
        (aime88p4-of-rational b)))
      (equal
       (aime88p4-of-rational (- a))
       (aime88p4-neg (aime88p4-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime88p4-of-rational a)
        (aime88p4-of-rational b)))
      (iff
       (< a b)
       (aime88p4-lt
        (aime88p4-of-rational a)
        (aime88p4-of-rational b)))))))

(defun aime88p4-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime88p4-real-p (car coefficients))
     (aime88p4-polynomial-p (cdr coefficients)))))

(defun aime88p4-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime88p4-zero)
    (aime88p4-add
     (car coefficients)
     (aime88p4-mul
      x
      (aime88p4-polynomial-value
       (cdr coefficients) x)))))

(defun aime88p4-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime88p4-leading-coefficient (cdr coefficients))))

(defun aime88p4-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime88p4-leading-coefficient coefficients)
     (aime88p4-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime88p4-square-root-exists-p (x)
  (exists (root)
    (and
     (aime88p4-nonnegative-p root)
     (equal (aime88p4-mul root root) x))))

(defun-sk aime88p4-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime88p4-nonnegative-p x)
     (aime88p4-square-root-exists-p x))))

(defun-sk aime88p4-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime88p4-real-p root)
     (equal
      (aime88p4-polynomial-value coefficients root)
      (aime88p4-zero)))))

(defun-sk aime88p4-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime88p4-polynomial-p coefficients)
      (aime88p4-odd-degree-p coefficients))
     (aime88p4-polynomial-root-exists-p coefficients))))

(defun aime88p4-real-closed-field-p ()
  (and
   (aime88p4-field-laws-p)
   (aime88p4-order-laws-p)
   (aime88p4-rational-laws-p)
   (aime88p4-lt (aime88p4-zero) (aime88p4-one))
   (aime88p4-nonnegative-square-roots-p)
   (aime88p4-odd-polynomial-roots-p)))

(defun aime88p4-principal-square-root-p (root value)
  (and
   (aime88p4-nonnegative-p root)
   (equal (aime88p4-mul root root) value)))

(defchoose aime88p4-sqrt (root) (value)
  (aime88p4-principal-square-root-p root value))

        (defun aime88p4-bounded-real-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (aime88p4-real-p (car values))
     (aime88p4-lt
      (aime88p4-abs (car values))
      (aime88p4-one))
     (aime88p4-bounded-real-list-p (cdr values)))))

(defun aime88p4-sum (values)
  (if (endp values)
      (aime88p4-zero)
    (aime88p4-add
     (car values)
     (aime88p4-sum (cdr values)))))

(defun aime88p4-sum-absolute-values (values)
  (if (endp values)
      (aime88p4-zero)
    (aime88p4-add
     (aime88p4-abs (car values))
     (aime88p4-sum-absolute-values (cdr values)))))

(defun aime-1988-p4-statement (n values)
  (implies
   (and
    (aime88p4-real-closed-field-p)
    (natp n)
    (true-listp values)
    (equal (len values) n)
    (aime88p4-bounded-real-list-p values)
    (equal
     (aime88p4-sum-absolute-values values)
     (aime88p4-add
      (aime88p4-of-rational 19)
      (aime88p4-abs (aime88p4-sum values)))))
   (<= 20 n)))

        (value-triple :itpeval-statement-checked)
        :q
