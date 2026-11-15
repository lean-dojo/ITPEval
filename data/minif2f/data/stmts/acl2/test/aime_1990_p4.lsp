;; Statement-only formalization of miniF2F artifact aime_1990_p4:
        ;; the stated reciprocal equation and nonzero-denominator hypotheses for a positive real x imply x=13.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime90p4-real-p (value) t)
(defstub aime90p4-zero () t)
(defstub aime90p4-one () t)
(defstub aime90p4-add (left right) t)
(defstub aime90p4-mul (left right) t)
(defstub aime90p4-neg (value) t)
(defstub aime90p4-inv (value) t)
(defstub aime90p4-lt (left right) t)
(defstub aime90p4-of-rational (value) t)

(defun aime90p4-sub (left right)
  (aime90p4-add left (aime90p4-neg right)))

(defun aime90p4-div (left right)
  (aime90p4-mul left (aime90p4-inv right)))

(defun aime90p4-le (left right)
  (or (equal left right) (aime90p4-lt left right)))

(defun aime90p4-nonnegative-p (value)
  (and (aime90p4-real-p value)
       (aime90p4-le (aime90p4-zero) value)))

(defun aime90p4-positive-p (value)
  (and (aime90p4-real-p value)
       (aime90p4-lt (aime90p4-zero) value)))

(defun aime90p4-abs (value)
  (if (aime90p4-lt value (aime90p4-zero))
      (aime90p4-neg value)
    value))

(defun aime90p4-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime90p4-one)
    (aime90p4-mul
     value
     (aime90p4-pow value (1- exponent)))))

(defun-sk aime90p4-field-laws-p ()
  (forall (x y z)
    (and
     (aime90p4-real-p (aime90p4-zero))
     (aime90p4-real-p (aime90p4-one))
     (not (equal (aime90p4-zero) (aime90p4-one)))
     (implies
      (aime90p4-real-p x)
      (and
       (aime90p4-real-p (aime90p4-neg x))
       (aime90p4-real-p (aime90p4-inv x))
       (equal (aime90p4-add x (aime90p4-zero)) x)
       (equal (aime90p4-add x (aime90p4-neg x))
              (aime90p4-zero))
       (equal (aime90p4-mul x (aime90p4-one)) x)
       (implies
        (not (equal x (aime90p4-zero)))
        (equal (aime90p4-mul x (aime90p4-inv x))
               (aime90p4-one)))))
     (equal (aime90p4-inv (aime90p4-zero))
            (aime90p4-zero))
     (implies
      (and (aime90p4-real-p x)
           (aime90p4-real-p y))
      (and
       (aime90p4-real-p (aime90p4-add x y))
       (aime90p4-real-p (aime90p4-mul x y))
       (equal (aime90p4-add x y)
              (aime90p4-add y x))
       (equal (aime90p4-mul x y)
              (aime90p4-mul y x))))
     (implies
      (and (aime90p4-real-p x)
           (aime90p4-real-p y)
           (aime90p4-real-p z))
      (and
       (equal (aime90p4-add (aime90p4-add x y) z)
              (aime90p4-add x (aime90p4-add y z)))
       (equal (aime90p4-mul (aime90p4-mul x y) z)
              (aime90p4-mul x (aime90p4-mul y z)))
       (equal (aime90p4-mul x (aime90p4-add y z))
              (aime90p4-add
               (aime90p4-mul x y)
               (aime90p4-mul x z))))))))

(defun-sk aime90p4-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime90p4-real-p x)
          (aime90p4-real-p y)
          (aime90p4-real-p z))
     (and
      (not (aime90p4-lt x x))
      (or (equal x y)
          (aime90p4-lt x y)
          (aime90p4-lt y x))
      (implies
       (and (aime90p4-lt x y)
            (aime90p4-lt y z))
       (aime90p4-lt x z))
      (implies
       (aime90p4-lt x y)
       (aime90p4-lt
        (aime90p4-add x z)
        (aime90p4-add y z)))
      (implies
       (and (aime90p4-lt (aime90p4-zero) x)
            (aime90p4-lt (aime90p4-zero) y))
       (aime90p4-lt
        (aime90p4-zero)
        (aime90p4-mul x y)))))))

(defun-sk aime90p4-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime90p4-real-p (aime90p4-of-rational a))
      (equal (aime90p4-of-rational 0) (aime90p4-zero))
      (equal (aime90p4-of-rational 1) (aime90p4-one))
      (equal
       (aime90p4-of-rational (+ a b))
       (aime90p4-add
        (aime90p4-of-rational a)
        (aime90p4-of-rational b)))
      (equal
       (aime90p4-of-rational (* a b))
       (aime90p4-mul
        (aime90p4-of-rational a)
        (aime90p4-of-rational b)))
      (equal
       (aime90p4-of-rational (- a))
       (aime90p4-neg (aime90p4-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime90p4-of-rational a)
        (aime90p4-of-rational b)))
      (iff
       (< a b)
       (aime90p4-lt
        (aime90p4-of-rational a)
        (aime90p4-of-rational b)))))))

(defun aime90p4-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime90p4-real-p (car coefficients))
     (aime90p4-polynomial-p (cdr coefficients)))))

(defun aime90p4-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime90p4-zero)
    (aime90p4-add
     (car coefficients)
     (aime90p4-mul
      x
      (aime90p4-polynomial-value
       (cdr coefficients) x)))))

(defun aime90p4-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime90p4-leading-coefficient (cdr coefficients))))

(defun aime90p4-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime90p4-leading-coefficient coefficients)
     (aime90p4-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime90p4-square-root-exists-p (x)
  (exists (root)
    (and
     (aime90p4-nonnegative-p root)
     (equal (aime90p4-mul root root) x))))

(defun-sk aime90p4-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime90p4-nonnegative-p x)
     (aime90p4-square-root-exists-p x))))

(defun-sk aime90p4-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime90p4-real-p root)
     (equal
      (aime90p4-polynomial-value coefficients root)
      (aime90p4-zero)))))

(defun-sk aime90p4-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime90p4-polynomial-p coefficients)
      (aime90p4-odd-degree-p coefficients))
     (aime90p4-polynomial-root-exists-p coefficients))))

(defun aime90p4-real-closed-field-p ()
  (and
   (aime90p4-field-laws-p)
   (aime90p4-order-laws-p)
   (aime90p4-rational-laws-p)
   (aime90p4-lt (aime90p4-zero) (aime90p4-one))
   (aime90p4-nonnegative-square-roots-p)
   (aime90p4-odd-polynomial-roots-p)))

(defun aime90p4-principal-square-root-p (root value)
  (and
   (aime90p4-nonnegative-p root)
   (equal (aime90p4-mul root root) value)))

(defchoose aime90p4-sqrt (root) (value)
  (aime90p4-principal-square-root-p root value))

        (defun aime-1990-p4-statement (x)
  (let ((d29
         (aime90p4-sub
          (aime90p4-sub
           (aime90p4-pow x 2)
           (aime90p4-mul
            (aime90p4-of-rational 10) x))
          (aime90p4-of-rational 29)))
        (d45
         (aime90p4-sub
          (aime90p4-sub
           (aime90p4-pow x 2)
           (aime90p4-mul
            (aime90p4-of-rational 10) x))
          (aime90p4-of-rational 45)))
        (d69
         (aime90p4-sub
          (aime90p4-sub
           (aime90p4-pow x 2)
           (aime90p4-mul
            (aime90p4-of-rational 10) x))
          (aime90p4-of-rational 69))))
    (implies
     (and
      (aime90p4-real-closed-field-p)
      (aime90p4-positive-p x)
      (not (equal d29 (aime90p4-zero)))
      (not (equal d45 (aime90p4-zero)))
      (not (equal d69 (aime90p4-zero)))
      (equal
       (aime90p4-sub
        (aime90p4-add
         (aime90p4-div (aime90p4-one) d29)
         (aime90p4-div (aime90p4-one) d45))
        (aime90p4-div (aime90p4-of-rational 2) d69))
       (aime90p4-zero)))
     (equal x (aime90p4-of-rational 13)))))

        (value-triple :itpeval-statement-checked)
        :q
