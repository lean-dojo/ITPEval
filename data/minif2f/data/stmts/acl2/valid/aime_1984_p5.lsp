;; Statement-only formalization of miniF2F artifact aime_1984_p5:
        ;; under the bijection u=log_2(a), v=log_2(b) for positive reals, the source logarithmic system implies log_2(ab)=9.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub aime84p5-real-p (value) t)
(defstub aime84p5-zero () t)
(defstub aime84p5-one () t)
(defstub aime84p5-add (left right) t)
(defstub aime84p5-mul (left right) t)
(defstub aime84p5-neg (value) t)
(defstub aime84p5-inv (value) t)
(defstub aime84p5-lt (left right) t)
(defstub aime84p5-of-rational (value) t)

(defun aime84p5-sub (left right)
  (aime84p5-add left (aime84p5-neg right)))

(defun aime84p5-div (left right)
  (aime84p5-mul left (aime84p5-inv right)))

(defun aime84p5-le (left right)
  (or (equal left right) (aime84p5-lt left right)))

(defun aime84p5-nonnegative-p (value)
  (and (aime84p5-real-p value)
       (aime84p5-le (aime84p5-zero) value)))

(defun aime84p5-positive-p (value)
  (and (aime84p5-real-p value)
       (aime84p5-lt (aime84p5-zero) value)))

(defun aime84p5-abs (value)
  (if (aime84p5-lt value (aime84p5-zero))
      (aime84p5-neg value)
    value))

(defun aime84p5-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime84p5-one)
    (aime84p5-mul
     value
     (aime84p5-pow value (1- exponent)))))

(defun-sk aime84p5-field-laws-p ()
  (forall (x y z)
    (and
     (aime84p5-real-p (aime84p5-zero))
     (aime84p5-real-p (aime84p5-one))
     (not (equal (aime84p5-zero) (aime84p5-one)))
     (implies
      (aime84p5-real-p x)
      (and
       (aime84p5-real-p (aime84p5-neg x))
       (aime84p5-real-p (aime84p5-inv x))
       (equal (aime84p5-add x (aime84p5-zero)) x)
       (equal (aime84p5-add x (aime84p5-neg x))
              (aime84p5-zero))
       (equal (aime84p5-mul x (aime84p5-one)) x)
       (implies
        (not (equal x (aime84p5-zero)))
        (equal (aime84p5-mul x (aime84p5-inv x))
               (aime84p5-one)))))
     (equal (aime84p5-inv (aime84p5-zero))
            (aime84p5-zero))
     (implies
      (and (aime84p5-real-p x)
           (aime84p5-real-p y))
      (and
       (aime84p5-real-p (aime84p5-add x y))
       (aime84p5-real-p (aime84p5-mul x y))
       (equal (aime84p5-add x y)
              (aime84p5-add y x))
       (equal (aime84p5-mul x y)
              (aime84p5-mul y x))))
     (implies
      (and (aime84p5-real-p x)
           (aime84p5-real-p y)
           (aime84p5-real-p z))
      (and
       (equal (aime84p5-add (aime84p5-add x y) z)
              (aime84p5-add x (aime84p5-add y z)))
       (equal (aime84p5-mul (aime84p5-mul x y) z)
              (aime84p5-mul x (aime84p5-mul y z)))
       (equal (aime84p5-mul x (aime84p5-add y z))
              (aime84p5-add
               (aime84p5-mul x y)
               (aime84p5-mul x z))))))))

(defun-sk aime84p5-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime84p5-real-p x)
          (aime84p5-real-p y)
          (aime84p5-real-p z))
     (and
      (not (aime84p5-lt x x))
      (or (equal x y)
          (aime84p5-lt x y)
          (aime84p5-lt y x))
      (implies
       (and (aime84p5-lt x y)
            (aime84p5-lt y z))
       (aime84p5-lt x z))
      (implies
       (aime84p5-lt x y)
       (aime84p5-lt
        (aime84p5-add x z)
        (aime84p5-add y z)))
      (implies
       (and (aime84p5-lt (aime84p5-zero) x)
            (aime84p5-lt (aime84p5-zero) y))
       (aime84p5-lt
        (aime84p5-zero)
        (aime84p5-mul x y)))))))

(defun-sk aime84p5-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (aime84p5-real-p (aime84p5-of-rational a))
      (equal (aime84p5-of-rational 0) (aime84p5-zero))
      (equal (aime84p5-of-rational 1) (aime84p5-one))
      (equal
       (aime84p5-of-rational (+ a b))
       (aime84p5-add
        (aime84p5-of-rational a)
        (aime84p5-of-rational b)))
      (equal
       (aime84p5-of-rational (* a b))
       (aime84p5-mul
        (aime84p5-of-rational a)
        (aime84p5-of-rational b)))
      (equal
       (aime84p5-of-rational (- a))
       (aime84p5-neg (aime84p5-of-rational a)))
      (iff
       (equal a b)
       (equal
        (aime84p5-of-rational a)
        (aime84p5-of-rational b)))
      (iff
       (< a b)
       (aime84p5-lt
        (aime84p5-of-rational a)
        (aime84p5-of-rational b)))))))

(defun aime84p5-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (aime84p5-real-p (car coefficients))
     (aime84p5-polynomial-p (cdr coefficients)))))

(defun aime84p5-polynomial-value (coefficients x)
  (if (endp coefficients)
      (aime84p5-zero)
    (aime84p5-add
     (car coefficients)
     (aime84p5-mul
      x
      (aime84p5-polynomial-value
       (cdr coefficients) x)))))

(defun aime84p5-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (aime84p5-leading-coefficient (cdr coefficients))))

(defun aime84p5-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (aime84p5-leading-coefficient coefficients)
     (aime84p5-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk aime84p5-square-root-exists-p (x)
  (exists (root)
    (and
     (aime84p5-nonnegative-p root)
     (equal (aime84p5-mul root root) x))))

(defun-sk aime84p5-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (aime84p5-nonnegative-p x)
     (aime84p5-square-root-exists-p x))))

(defun-sk aime84p5-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (aime84p5-real-p root)
     (equal
      (aime84p5-polynomial-value coefficients root)
      (aime84p5-zero)))))

(defun-sk aime84p5-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (aime84p5-polynomial-p coefficients)
      (aime84p5-odd-degree-p coefficients))
     (aime84p5-polynomial-root-exists-p coefficients))))

(defun aime84p5-real-closed-field-p ()
  (and
   (aime84p5-field-laws-p)
   (aime84p5-order-laws-p)
   (aime84p5-rational-laws-p)
   (aime84p5-lt (aime84p5-zero) (aime84p5-one))
   (aime84p5-nonnegative-square-roots-p)
   (aime84p5-odd-polynomial-roots-p)))

(defun aime84p5-principal-square-root-p (root value)
  (and
   (aime84p5-nonnegative-p root)
   (equal (aime84p5-mul root root) value)))

(defchoose aime84p5-sqrt (root) (value)
  (aime84p5-principal-square-root-p root value))

        (defun aime-1984-p5-statement (u v)
  (implies
   (and
    (aime84p5-real-closed-field-p)
    (aime84p5-real-p u)
    (aime84p5-real-p v)
    (equal
     (aime84p5-add
      (aime84p5-div
       u
       (aime84p5-of-rational 3))
      v)
     (aime84p5-of-rational 5))
    (equal
     (aime84p5-add
      (aime84p5-div
       v
       (aime84p5-of-rational 3))
      u)
     (aime84p5-of-rational 7)))
   (equal
    (aime84p5-add u v)
    (aime84p5-of-rational 9))))

        (value-triple :itpeval-statement-checked)
        :q
